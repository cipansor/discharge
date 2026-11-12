#![cfg_attr(not(feature = "std"), no_std)]
#![forbid(unsafe_op_in_unsafe_fn)]
#![deny(missing_docs)]
//! # verif — in-code formal verification for Rust
//!
//! SPARK/Ada earns its reputation in safety-critical work because the proof
//! tooling is *part of the language and part of the artifact*: `gnatprove` sits
//! next to `gnatmake`, and the contracts (`Pre`, `Post`, `Type_Invariant`,
//! `Assert`) are first-class syntax the compiler knows about. Rust ships with a
//! spectacular type system and no such prover.
//!
//! This crate is an experiment in closing that gap from inside Rust itself. It
//! embeds a **bit-blasting decision procedure** — formulas are lowered to
//! Reduced Ordered Binary Decision Diagrams, which are a canonical form, so
//! equivalence is node identity — and builds the modules below on top of it.
//!
//! ```
//! use verif::prelude::*;
//!
//! // ∀ x:u8. (x & 0x0f) < 16  — decided by the embedded engine
//! let proved = verif::smt::with_fresh(|| {
//!     let x = var(8);
//!     (x & 0x0fu32).lt_val(16).prove().is_proved()
//! });
//! assert!(proved);
//! ```
//!
//! # The three ways, in code
//!
//! The same obligation, discharged three ways. Each returns a verdict you can
//! inspect; none of them ever reports `Valid` for something false.
//!
//! ```
//! use verif::prelude::*;
//!
//! // 1. Symbolic: for every input, via BDDs. Fast, but can say Unknown.
//! let symbolic = verif::smt::with_fresh(|| {
//!     let x = var(8);
//!     smt::prove_implies(x.le_val(200), x.le_val(255)).is_proved()
//! });
//! assert!(symbolic);
//!
//! // 2. Exhaustive: every input of a small domain, no size wall, never Unknown.
//! assert!(for_all_u8(|a| a <= 255));
//!
//! // 3. Type-level: the kernel builds a proof term and `rustc` checks it, so a
//! //    falsehood fails to compile rather than returning a verdict.
//! use verif::proof::{And, Equals, Imp, Truth};
//! assert_proof!(And<Truth, Imp<Truth, Truth>>);
//! assert_proof!(Equals<u8, u8>);
//! ```
//!
//! A contract you can state in the source and check at run time, with the same
//! predicate usable symbolically:
//!
//! ```
//! use verif::prelude::*;
//!
//! // Pre/post as a symbolic obligation: `requires x <= 200` and
//! // `ensures x <= 255`; the engine proves the implication.
//! let v = verif::smt::with_fresh(|| {
//!     let x = var(8);
//!     let contract = ensures(requires(x.le_val(200)), x.le_val(255));
//!     contract.discharge()
//! });
//! assert!(v.is_proved());
//! ```
//!
//! # What you get, in one line each
//!
//! `no_std` by default, zero external dependencies, a fixed-size heap-free arena,
//! and `#![forbid(unsafe_op_in_unsafe_fn)]`. The engine links `core` and nothing
//! else, which is what a bare-metal safety build wants; the host-side tools (the
//! MIR frontend, the file-backed helpers) are behind the `std` feature.
//!
//! # The three ways this crate proves something
//!
//! ```text
//! 1. symbolic      smt::prove(p)              -- for all inputs, via BDDs
//! 2. exhaustive    exhaustive::for_all_u16(p) -- every input, no size wall
//! 3. type-level    proof::Theorem             -- the compiler checks the proof term
//! ```
//!
//! They are deliberately different tools, and each has a different honesty
//! profile. The symbolic engine is the fast, general one but can return
//! [`smt::Verdict::Unknown`] at the BDD size wall. Enumeration is a complete
//! proof that never says "unknown", but only for small domains. The kernel makes
//! *composition* of proofs machine-checked by `rustc`. A serious safety argument
//! uses all three, and says which one it used.
//!
//! | # | Mechanism | Entry point | Complete? | Can it lie? |
//! |---|---|---|---|---|
//! | 1 | Symbolic — BDD, then CDCL SAT fallback | [`smt::prove`], [`sym`] | no (scaling wall) | no — it returns `Unknown` |
//! | 2 | Exhaustive — every input of a real domain | [`exhaustive::for_all_u8`], [`exhaustive::for_all_u16`] | yes, small domains | no |
//! | 3 | Type-level — Curry–Howard kernel | [`proof::Theorem`], `assert_proof!` | yes, for composition | no — it will not compile |
//!
//! The third row is the one to read carefully, because two things in this crate
//! are easy to confuse. `assert_proof!` is a *compile-time* obligation: it asks
//! for a [`proof::Theorem`] impl and `rustc` refuses if the proof term cannot be
//! built, which is why a falsehood is a build error and not a bad verdict.
//! [`proof::Certificate::discharge`] is the *runtime* solver route: it takes a
//! predicate to the `smt` engine and returns `Option`, so it can answer `None` at
//! run time. Both are useful; only the first is checked before the program runs.
//!
//! # Module map
//!
//! ## The engine
//!
//! | Module | What it is |
//! |---|---|
//! | [`smt`] | The decision procedure: bit-vector terms, ROBDDs, [`smt::Verdict`], counterexamples, the `no_std` arena. |
//! | [`bitblast`] | The bit-level term graph → CNF lowering, used by the SAT fallback. |
//! | [`sat`] | The CDCL SAT solver used as the fallback past the BDD wall. |
//!
//! ## Specifications and proofs
//!
//! | Module | What it is |
//! |---|---|
//! | [`sym`] | A symbolic DSL: operator overloading so a specification reads like code, `(x + y).eq(y + x).prove()`. |
//! | [`logic`] | Checked and saturating arithmetic plus a Q16.16 [`logic::Fixed`] type, each with proofs attached. |
//! | [`mod@proof`] | The Curry–Howard kernel: [`proof::Theorem`] propositions whose proof terms `rustc` checks at compile time (so `Truth => Falsity` does not build), plus runtime [`proof::Certificate`]s for an engine-produced proof. |
//! | [`mod@contract`] | Runtime `requires`/`ensures`/`assert` over concrete values, with structured errors. |
//! | [`vc`] | [`vc::requires`]/[`vc::ensures`]/[`vc::invariant`], [`vc::verify_body`], and the [`vc::Verified`] witness. |
//! | [`wp`] | Weakest-precondition generation for statements, loops and calls, with a per-rule [`wp::Report`]. |
//! | [`mem`] | A bounded symbolic array with a proved [`mem::Mem::read`] / [`mem::Mem::store_wp`] frame condition. |
//! | [`quant`] | Bounded quantifiers, expanded into finite conjunctions and disjunctions. |
//!
//! ## Complete by enumeration
//!
//! | Module | What it is |
//! |---|---|
//! | [`exhaustive`] | Complete proofs by enumeration over `u8`/`u16` domains: no size wall, no `Unknown`. |
//!
//! ## The proved arithmetic, and its symbolic oracle
//!
//! | Module | What it is |
//! |---|---|
//! | [`arith`] | The sibling crate `verif-arithmetic`, re-exported: total integer operations and a refinement-typed [`arith::Bounded`], each with an enumeration proof carried in the artifact. `no_std`, `#![forbid(unsafe_code)]` and dependency-free on its own. |
//! | [`primitives`] | The symbolic *oracle* for those same operations: the obligations restated at widths enumeration cannot reach, cross-checked against it by `tests/oracle.rs`. |
//!
//! ## Interop and ergonomics
//!
//! | Module | What it is |
//! |---|---|
//! | [`smtscript`] | SMT-LIB2 export, so an independent solver can decide the same condition. |
//! | [`macros`] | `verify!`, `verify_implies!`, `contract!`, `proof!`, `assert_proof!`, `check!`, `verify_exhaustive!`. |
//!
//! ## Verifying real Rust (`std` only)
//!
//! | Module | What it is |
//! |---|---|
//! | `mir` | Verify **real Rust**: read `rustc`'s own MIR, symbolically execute it, and discharge rustc's overflow, underflow and division-by-zero asserts plus `/// requires:` / `/// ensures:` doc-comment contracts. |
//!
//! The `mir` frontend is the only module that needs a compiler at run time, so it
//! is behind the `std` feature. Its page appears in this documentation only when
//! that feature is enabled (the published docs on docs.rs are built with
//! `--all-features`, so it is there).
//!
//! # Feature flags
//!
//! | Feature | Default | Effect |
//! |---|---|---|
//! | *(none)* | yes | `no_std`, zero dependencies, `core` only. The engine, the DSL, the kernel, the contracts, `wp`, `mem`, `quant`, `exhaustive`. |
//! | `std` | no | Adds the `mir` frontend, the thread-local arena used by the host-side test suite, and the file-backed helpers. |
//!
//! There is no `alloc` feature and no allocator anywhere: every structure is
//! fixed-size, and the arena has a documented capacity rather than growing.
//!
//! # What this is not
//!
//! It is not a replacement for SPARK's proof tooling, and it does not make
//! arbitrary Rust correct. It reasons about **bit-vectors and boolean
//! predicates**, plus one bounded *array* ([`mem`], addressed by an integer). It
//! does not model pointers, address arithmetic across objects, aliasing or
//! concurrency: you cannot state "this pointer is valid" or "these two threads do
//! not race". The BDD engine is not a CDCL SAT solver: equalities between two
//! wide multipliers can hit the size wall, in which case the honest answer is
//! [`smt::Verdict::Unknown`].
//!
//! Read each module's page — and the crate `README`, which records the claim each
//! feature makes and the check that backs it — before trusting a green test.
//!
//! # Where to read more
//!
//! - The `README` is the long-form document: one section per claim, with the
//!   gate that holds it.
//! - `CONTRIBUTING.md` covers the ground rules and the gate script.
//! - `SECURITY.md` covers reporting a **soundness bug** — a false `Valid` —
//!   which is the vulnerability class that matters in a verifier.
//! - `AGENTS.md` is the engineering log: why each decision was made, including
//!   the ones that were reversed.

pub mod bitblast;
pub mod contract;
pub mod exhaustive;
pub mod logic;
pub mod macros;
pub mod mem;
#[cfg(feature = "std")]
pub mod mir;
pub mod primitives;
pub mod proof;
pub mod quant;
pub mod sat;
pub mod smt;
pub mod smtscript;
pub mod sym;
pub mod vc;
pub mod wp;

// The proved runtime primitives live in a sibling crate so that the arithmetic a
// safety build ships is `no_std`, `#![forbid(unsafe_code)]` and dependency-free
// on its own, with its proofs carried inside it. Re-exported as `arith` so the
// module reads `verif::arith` rather than the `verif::verif_arithmetic` stutter,
// and so the caller never has to name the workspace layout.
pub use verif_arithmetic as arith;

/// The names you almost always want: the prover entry points, the symbolic
/// constructors, and the verification macros.
pub mod prelude {
    pub use crate::contract::{Contract, ContractError};
    pub use crate::arith::prove::{self as arithmetic_proofs, Verdict as ProofVerdict};
    pub use crate::exhaustive::{
        find_violation_u8, find_violation_u8_2, for_all_u8, for_all_u8_2, for_all_u16,
    };
    pub use crate::logic::Fixed;
    pub use crate::primitives::{safe_add, safe_div, safe_mul, safe_rem, safe_sub, Bounded};
    pub use crate::proof::{Certificate, Implication};
    pub use crate::smt::{
        self, all_ones, and, bits, eq, eq_const, find_model, iff, implies, index, ite, mul, not, or, prove,
        prove_equiv, prove_implies, ule, ule_const, ult, ult_const, var, var_named, word, Cex, Pred,
        Var, Verdict,
    };
    pub use crate::vc::{ensures, invariant, requires, verify_body, verify_contract, Verified};
    pub use crate::mem::{declare as declare_memory, Mem};
    pub use crate::smtscript::Query;
    pub use crate::wp::{
        verify as verify_program, verify_modular, verify_proc, Correctness, Proc, Rule, Stmt,
    };

    // Macros live at the crate root; re-export them so `use prelude::*` is enough.
    pub use crate::{assert_proof, check, contract, proof, verify, verify_exhaustive, verify_implies};
}

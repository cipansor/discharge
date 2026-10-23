#![cfg_attr(not(feature = "std"), no_std)]
#![forbid(unsafe_op_in_unsafe_fn)]
#![deny(missing_docs)]
//! # sparkrs — in-code formal verification for Rust
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
//! equivalence is node identity — and builds four things on top of it:
//!
//! | Module | What it gives you |
//! |---|---|
//! | [`smt`] | The decision procedure. `no_std`, zero dependencies, fixed-size arena. |
//! | [`sym`] | A symbolic DSL: `(x + y).eq(y + x).prove()`. |
//! | [`logic`] | Verified arithmetic and Q16.16 fixed point, with proofs attached. |
//! | [`mod@proof`] | A Curry–Howard proof kernel plus composable certificates. |
//! | [`mod@contract`] | `requires` / `ensures` / `invariant`, checked at runtime *and* provable symbolically. |
//! | [`exhaustive`] | Complete proofs by enumeration over small domains. |
//! | [`primitives`] | Drop-in safe integer ops whose absence of overflow is proved. |
//!
//! # The three ways this crate proves something
//!
//! ```text
//! 1. symbolic      smt::prove(p)              -- for all inputs, via BDDs
//! 2. exhaustive    exhaustive::for_all_u16(p) -- every input, no size wall
//! 3. type-level    proof::Certificate         -- the compiler checks the proof term
//! ```
//!
//! They are deliberately different tools. The symbolic engine is the fast,
//! general one but can return [`smt::Verdict::Unknown`] at the BDD size wall.
//! Enumeration is a complete proof that never says "unknown", but only for small
//! domains. The kernel makes *composition* of proofs machine-checked by `rustc`.
//! A serious safety argument uses all three, and says which one it used.
//!
//! # What this is not
//!
//! It is not a replacement for SPARK's proof tooling, and it does not make
//! arbitrary Rust correct. It reasons about **bit-vectors and boolean
//! predicates**; it does not (yet) model memory, pointers, aliasing or
//! concurrency. The BDD engine is not a CDCL SAT solver: equalities between two
//! wide multipliers can hit the size wall, in which case the honest answer is
//! `Unknown`. Read the module docs before trusting a green test.
//!
//! # Example
//!
//! ```
//! use sparkrs::prelude::*;
//! use sparkrs::sym::*;
//!
//! // ∀ x:u8. x & 0x0f < 16
//! let proved = sparkrs::smt::with_fresh(|| {
//!     let x = var(8);
//!     (x & 0x0fu64).lt_val(16).prove().is_proved()
//! });
//! assert!(proved);
//! ```

pub mod contract;
pub mod exhaustive;
pub mod logic;
pub mod macros;
pub mod primitives;
pub mod proof;
pub mod smt;
pub mod sym;
pub mod vc;

/// The names you almost always want: the prover entry points, the symbolic
/// constructors, and the verification macros.
pub mod prelude {
    pub use crate::contract::{Contract, ContractError};
    pub use crate::exhaustive::{
        find_violation_u8, find_violation_u8_2, for_all_u8, for_all_u8_2, for_all_u16,
    };
    pub use crate::logic::Fixed;
    pub use crate::primitives::{safe_add, safe_div, safe_mul, safe_rem, safe_sub, Bounded};
    pub use crate::proof::{Certificate, Implication};
    pub use crate::smt::{
        self, and, bits, eq, eq_const, find_model, iff, implies, index, ite, mul, not, or, prove,
        prove_equiv, prove_implies, ule, ule_const, ult, ult_const, var, var_named, word, Cex, Pred,
        Var, Verdict,
    };
    pub use crate::vc::{ensures, invariant, requires, verify_body, verify_contract, Verified};

    // Macros live at the crate root; re-export them so `use prelude::*` is enough.
    pub use crate::{assert_proof, check, contract, proof, verify, verify_exhaustive, verify_implies};
}

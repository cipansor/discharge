//! # verif-arithmetic — proved integer primitives for safety-critical Rust
//!
//! The "library half" of the SPARK story: the arithmetic a flight-control or
//! motor-control loop reaches for, with the property that makes each one safe
//! **proved inside the crate**. No external solver, no `smt` dependency, no
//! `unsafe`, no allocator — `core` and nothing else.
//!
//! In C, `a + b` on `unsigned` wraps silently and on `signed` is undefined
//! behaviour; in Ada with `-gnato` it traps, and SPARK can prove the trap never
//! fires. Rust's `+` panics in debug and wraps in release, which for flight
//! software is arguably the worst of both. These primitives take the
//! total-function route — they return an `Option` — and carry a proof that the
//! `None` case is exactly the overflow case, so a caller either handles it or
//! discharges it away.
//!
//! ```
//! use verif_arithmetic::{checked_add, prove};
//!
//! // The runtime behaviour...
//! assert_eq!(checked_add(200, 55), Some(255));
//! assert_eq!(checked_add(u32::MAX, 1), None);
//!
//! // ...and the proof that its overflow flag is exact.
//! assert!(prove::checked_add_is_total().is_proved());
//! ```
//!
//! # What is in this crate
//!
//! | Module | What it gives you |
//! |---|---|
//! | [`checked`] | Total arithmetic, split by what a caller does with the overflow. [`checked_add`], [`checked_sub`], [`checked_mul`] and [`mul_div`] return `Option`, where `None` is exactly the case the machine op would have wrapped or panicked. [`saturating_add`] and [`saturating_sub`] return a plain `u32` and **clamp** at the bound instead of reporting it, so there is no `None` to check. |
//! | [`bounded`] | The `safe_*` functions (the same total route) and [`Bounded<MIN, MAX>`](bounded::Bounded), a refinement-typed integer whose constructors are the only way in. |
//! | [`fixed`] | [`Fixed`], a Q16.16 fixed-point number: deterministic, no floating point, no soft-float dependency. |
//! | [`prove`] | The proofs, discharged by exhaustive enumeration. This is the module that makes the rest trustworthy. |
//!
//! The crate root re-exports the common names, so `use verif_arithmetic::{checked_add, Bounded, Fixed, Verdict}`
//! is usually enough without naming a module.
//!
//! # The proof is a decision procedure, not a citation
//!
//! [`prove`] holds the proofs. Each is a **decision procedure by exhaustive
//! enumeration**: it walks every input in the domain and returns
//! [`Verdict::Valid`] only if the property held for all of them, or
//! [`Verdict::Counterexample`] with a witness if one failed. That is a complete
//! proof — no size wall, no `Unknown` for a domain it can reach — and it needs
//! nothing but `core`. It is the same technique used to validate flight-control
//! tables, and the same one the parent crate's `exhaustive` module uses.
//!
//! This is deliberately *not* a symbolic engine. Exhaustive enumeration cannot
//! reach a 32-bit two-variable domain, and it does not pretend to: a proof whose
//! domain exceeds [`prove::ENUM_BUDGET`] returns [`Verdict::Unknown`] rather
//! than a guess. The proofs here are stated at the widths the enumeration can
//! *finish*, which is the honest boundary of a method with no solver behind it.
//!
//! # Feature flags
//!
//! There are none. This crate is `no_std`, `#![forbid(unsafe_code)]` and
//! dependency-free by construction, and there is no configuration in which that
//! changes. A downstream build links `core` and nothing else.
//!
//! # The symbolic oracle lives in the parent crate
//!
//! [`verif`](https://docs.rs/verif) — the parent crate —
//! depends on this one, keeps its own bit-blasting `smt` engine, and states the
//! **same** obligations symbolically at widths 8, 16 and 32. `tests/oracle.rs`
//! in the parent then cross-checks the two: the enumeration and the symbolic
//! engine must agree on every obligation they share, and where they cannot (the
//! 32-bit two-variable domains) the symbolic engine is the one that answers.
//!
//! The split is the same shape as the parent's MIR frontend, which parses MIR
//! itself and is cross-checked against `rustc_public` in CI: **each crate owns a
//! self-contained mechanism, and the heavy external one is only ever an oracle.**
//! A dependency that can lie to you is not a proof; a second opinion is.
//!
//! # When to reach for the parent crate instead
//!
//! This crate proves things by *enumerating* a domain, so it is the right tool
//! for a primitive whose domain is small and whose proof you want carried in the
//! artifact with no solver. When the obligation is symbolic — a bound over all
//! `u32` inputs, a loop invariant, a contract on a whole `fn` — use
//! [`verif`](https://docs.rs/verif), which has the BDD engine, `wp`, `mem` and
//! the MIR frontend. The two are designed to be used together, and the parent
//! re-exports this crate as `verif::arith`.

#![no_std]
#![forbid(unsafe_code)]
#![deny(missing_docs)]

pub mod bounded;
pub mod checked;
pub mod fixed;
pub mod prove;

pub use bounded::{Bounded, safe_add, safe_div, safe_mul, safe_rem, safe_sub};
pub use checked::{
    checked_add, checked_mul, checked_sub, mul_div, saturating_add, saturating_sub,
};
pub use fixed::Fixed;
pub use prove::Verdict;

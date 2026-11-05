//! # discharge-arithmetic — proved integer primitives for safety-critical Rust
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
//! ## The proof is a decision procedure, not a citation
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
//! ## The symbolic oracle lives in the parent crate
//!
//! [`discharge`](https://github.com/cipansor/discharge) — the parent crate —
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
//! ```
//! use discharge_arithmetic::{checked_add, prove};
//!
//! // The runtime behaviour...
//! assert_eq!(checked_add(200, 55), Some(255));
//! assert_eq!(checked_add(u32::MAX, 1), None);
//!
//! // ...and the proof that its overflow flag is exact.
//! assert!(prove::checked_add_is_total().is_proved());
//! ```

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

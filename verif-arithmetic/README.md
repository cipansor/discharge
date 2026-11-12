# verif-arithmetic

[![crates.io](https://img.shields.io/crates/v/verif-arithmetic.svg)](https://crates.io/crates/verif-arithmetic)
[![docs.rs](https://docs.rs/verif-arithmetic/badge.svg)](https://docs.rs/verif-arithmetic)
[![license](https://img.shields.io/crates/l/verif-arithmetic.svg)](#license)

Integer primitives for safety-critical Rust whose central properties are
**proved inside the crate by exhaustive enumeration**. `no_std`, zero
dependencies, `#![forbid(unsafe_code)]`.

```rust
use verif_arithmetic::{checked_add, prove};

// The runtime behaviour...
assert_eq!(checked_add(200, 55), Some(255));
assert_eq!(checked_add(u32::MAX, 1), None);

// ...and the proof that its overflow flag is exact.
assert!(prove::checked_add_is_total().is_proved());
```

In C, `a + b` on `unsigned` wraps silently and on `signed` is undefined
behaviour; in Ada with `-gnato` it traps, and SPARK can prove the trap never
fires. Rust's `+` panics in debug and wraps in release, which for flight
software is arguably the worst of both. These primitives take the total-function
route — they return an `Option` — and carry a proof that the `None` case is
exactly the overflow case, so a caller either handles it or discharges it away.

## The proof is a decision procedure, not a citation

`prove` holds the proofs. Each is a decision procedure by exhaustive
enumeration: it walks every input in the domain and returns `Verdict::Valid`
only if the property held for all of them, or `Verdict::Counterexample` with a
witness if one failed. That is a complete proof — no size wall, no `Unknown` for
a domain it can reach — and it needs nothing but `core`.

This is deliberately *not* a symbolic engine. Exhaustive enumeration cannot
reach a 32-bit two-variable domain, and it does not pretend to: a proof whose
domain exceeds `prove::ENUM_BUDGET` returns `Verdict::Unknown` rather than a
guess. The proofs here are stated at the widths the enumeration can *finish*,
which is the honest boundary of a method with no solver behind it.

## What is in the crate

| Item | What it is |
| --- | --- |
| `checked_add`, `checked_sub`, `checked_mul` | `Option`-returning arithmetic with the overflow flag proved exact |
| `saturating_add`, `saturating_sub` | Saturating arithmetic, proved to clamp exactly at the bounds |
| `mul_div` | Multiply-then-divide without an intermediate overflow |
| `Fixed` | Q16.16 fixed-point with proved rounding and range properties |
| `Bounded` | A refinement type carrying a proved range invariant, with `safe_add`/`safe_sub`/`safe_mul`/`safe_div`/`safe_rem` |
| `prove` | The proofs themselves, as callable decision procedures |

## The symbolic oracle lives in the parent crate

[`verif`](https://crates.io/crates/verif) — the parent crate — depends on this
one, keeps its own bit-blasting SMT engine, and states the **same** obligations
symbolically at widths 8, 16 and 32. The parent's `tests/oracle.rs` then
cross-checks the two: the enumeration and the symbolic engine must agree on
every obligation they share, and where they cannot (the 32-bit two-variable
domains) the symbolic engine is the one that answers.

The split is the same shape as the parent's MIR frontend, which parses MIR
itself and is cross-checked against `rustc_public` in CI: **each crate owns a
self-contained mechanism, and the heavy external one is only ever an oracle.** A
dependency that can lie to you is not a proof; a second opinion is.

## Why the crate is split out

The runtime arithmetic a safety build ships should link `core` and nothing else.
The symbolic `smt` engine that cross-checks these proofs is a different thing —
large, host-side, and not wanted in a microcontroller image — so it lives in the
parent. This crate is the half that a flight build actually links, and its
dependency count is zero by construction, enforced by the parent's gate 5.

## Testing

The proofs run as ordinary tests (`cargo test`). The parent's differential
oracles — z3, Kani, Verus, Lean 4, Coq — are invoked as subprocesses by the
parent's CI and are never dependencies of either crate.

## License

Apache-2.0. The full text is in [`LICENSE`](LICENSE).

Copyright 2026 Yayasan Pesantren Cipansor and contributors.

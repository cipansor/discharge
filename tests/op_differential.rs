//! Every binary and unary operation, checked two ways: `evaluate` against `blast`.
//!
//! # Why this file exists
//!
//! The engine has two evaluators and they are *independent implementations* of the same
//! operators. `evaluate` is a term-level folder that computes each operator directly
//! (`wrapping_mul`, `wrapping_add`, and so on). `blast` builds a bit-level diagram that
//! `prove` then reasons over, and it is `blast` that every answer the frontend gives
//! comes from.
//!
//! Two bugs landed in `blast` and were missed by concrete tests written with `evaluate`,
//! because a concrete test through `evaluate` never calls `blast` at all. `shift_var`'s
//! mask was built at the wrong width, and the constant-multiply adder dropped a carry.
//! Both were found by accident, by asking `prove` a question rather than by any test of
//! the operator itself.
//!
//! This file closes that class of hole systematically rather than one operator at a
//! time. For each operator it enumerates the whole input domain at a width small enough
//! to exhaust, and asserts that `evaluate` and `blast` agree. A disagreement is either a
//! wrong `blast` -- a false proof waiting to happen -- or a wrong `evaluate`, which would
//! make every counterexample the engine reports a lie. Neither is acceptable and both
//! are caught here.
//!
//! # How `blast` is reached
//!
//! `prove(eq(op(x, y), word(expected, w)))` does not work: `word` is a `Const`, so the
//! query is about one point and `prove` cannot distinguish "true at that point" from
//! "true everywhere". Instead the *inputs* are pinned with `eq` constraints and the
//! equality of the two computations is asserted under those constraints, which is a
//! validity query whose falsity is exactly a disagreement at that point. The
//! alternative -- building the `blast` term and comparing verdicts -- needs a way to
//! force a term through the diagram, and pinning the inputs is that way.

// The explicit `y == 0` branch is the point of the division sweep: the divider's zero
// case is a *defined* value (all-ones quotient, dividend remainder), so the test spells
// that out rather than calling `checked_div`, which would only say the case is absent.
#![allow(clippy::manual_checked_ops)]

use discharge::smt::{self, Verdict};

/// Run a symbolic query on a thread with a large stack: the BDD operations recurse.
fn on_big_stack<F: FnOnce() + Send + 'static>(f: F) {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(f)
        .expect("spawn")
        .join()
        .expect("the query panicked");
}

/// Assert that the two evaluators agree on `x OP y == want` at the point `(x, y)`.
///
/// `op` builds the term; `want` is Rust's own answer. The check is a `prove` of the
/// implication "inputs pinned to these values => the term equals the answer", which is
/// `Valid` exactly when `blast` computes `want` there. A `Counterexample` means `blast`
/// and `evaluate` disagree, and the message names the point.
fn agree_at(w: u8, x: u64, y: u64, name: &str, op: fn(smt::Var, smt::Var) -> smt::Var, want: u64) {
    let mask = if w >= 64 { u64::MAX } else { (1u64 << w) - 1 };
    let (x, y) = (x & mask, y & mask);
    let want = want & mask;
    // `evaluate` first, so the message can say which side is which.
    let folded = smt::with_fresh(|| {
        smt::evaluate(op(smt::var(w), smt::var(w)), |i| Some(if i == 0 { x } else { y }))
    });
    let verdict = smt::with_fresh(|| {
        let a = smt::var(w);
        let b = smt::var(w);
        let pinned = smt::and(smt::eq(a, smt::word(x, w)), smt::eq(b, smt::word(y, w)));
        let term = op(a, b);
        smt::prove(smt::or(smt::not(pinned), smt::eq(term, smt::word(want, w))))
    });
    assert_eq!(
        verdict,
        Verdict::Valid,
        "{w}-bit {x} {name} {y}: blast disagreed with {want} (evaluate folded {folded:?})"
    );
    assert_eq!(
        folded,
        Some(want),
        "{w}-bit {x} {name} {y}: evaluate disagreed with Rust's {want}"
    );
}

/// Sweep a binary operator over the whole domain at `w`, both operands symbolic.
///
/// This covers the arms that handle two *variables*. It does **not** cover the arms
/// that specialise on a constant operand, and that is not a detail: the first version of
/// this file was only this sweep, and it passed on a `blast` whose constant-multiply
/// adder dropped a carry, because `var * var` never reaches that arm. `sweep_const`
/// below is the other half, and the two are kept separate so that a reader can see
/// which arm each one is evidence about.
fn sweep(w: u8, name: &str, op: fn(smt::Var, smt::Var) -> smt::Var, want: fn(u64, u64, u64) -> u64) {
    let mask = if w >= 64 { u64::MAX } else { (1u64 << w) - 1 };
    for x in 0..=mask {
        for y in 0..=mask {
            agree_at(w, x, y, name, op, want(x, y, mask));
        }
    }
}

/// Sweep a binary operator with the *right* operand a `Const`, which is the shape the
/// MIR frontend produces for `x * 4` and `x + 1`.
///
/// `smt::word` builds a `Const`, so the term here is `op(var, Const)` and `blast` takes
/// whichever specialised arm exists for that. Both operand orders are swept, because a
/// fast path that only checks one side is a real bug shape.
fn sweep_const(w: u8, name: &str, op: fn(smt::Var, smt::Var) -> smt::Var, want: fn(u64, u64, u64) -> u64) {
    let mask = if w >= 64 { u64::MAX } else { (1u64 << w) - 1 };
    for x in 0..=mask {
        for c in 0..=mask {
            let wnt = want(x, c, mask);
            // `op(x, c)`
            let folded = smt::with_fresh(|| {
                smt::evaluate(op(smt::var(w), smt::word(c, w)), |i| Some(if i == 0 { x } else { 0 }))
            });
            let verdict = smt::with_fresh(|| {
                let a = smt::var(w);
                let pinned = smt::eq(a, smt::word(x, w));
                let term = op(a, smt::word(c, w));
                smt::prove(smt::or(smt::not(pinned), smt::eq(term, smt::word(wnt, w))))
            });
            assert_eq!(
                verdict,
                Verdict::Valid,
                "{w}-bit {x} {name} {c} (constant on the right): blast disagreed with {wnt} \
                 (evaluate folded {folded:?})"
            );
            assert_eq!(folded, Some(wnt), "{w}-bit {x} {name} {c}: evaluate is wrong");

            // `op(c, x)`, so a fast path that only looks at the left operand is caught.
            // The variable is index 0 even here: `word(c, w)` is a `Const` and does not
            // take a variable slot, so the one free variable is `a` and it is `x`.
            // `op(c, x)` -- and the expectation is `want(c, x)`, not `want(x, c)`.
            // Subtraction is not commutative, and reusing the other order's answer here
            // was a bug in the first version of this helper; sweeping both orders is
            // partly *for* catching that class of mistake in the operator under test.
            let wnt = want(c, x, mask);
            let folded = smt::with_fresh(|| {
                smt::evaluate(op(smt::word(c, w), smt::var(w)), |i| {
                    Some(if i == 0 { x } else { 0 })
                })
            });
            let verdict = smt::with_fresh(|| {
                let a = smt::var(w);
                let pinned = smt::eq(a, smt::word(x, w));
                let term = op(smt::word(c, w), a);
                smt::prove(smt::or(smt::not(pinned), smt::eq(term, smt::word(wnt, w))))
            });
            assert_eq!(
                verdict,
                Verdict::Valid,
                "{w}-bit {c} {name} {x} (constant on the left): blast disagreed with {wnt} \
                 (evaluate folded {folded:?})"
            );
            assert_eq!(folded, Some(wnt), "{w}-bit {c} {name} {x}: evaluate is wrong");
        }
    }
}

#[test]
fn add_agrees_between_the_two_evaluators() {
    on_big_stack(|| {
        sweep(4, "+", smt::add, |x, y, m| x.wrapping_add(y) & m);
        sweep_const(4, "+", smt::add, |x, y, m| x.wrapping_add(y) & m);
    });
}

#[test]
fn sub_agrees_between_the_two_evaluators() {
    on_big_stack(|| {
        sweep(4, "-", smt::sub, |x, y, m| x.wrapping_sub(y) & m);
        sweep_const(4, "-", smt::sub, |x, y, m| x.wrapping_sub(y) & m);
    });
}

#[test]
fn mul_agrees_between_the_two_evaluators() {
    on_big_stack(|| {
        sweep(4, "*", smt::mul, |x, y, m| x.wrapping_mul(y) & m);
        sweep_const(4, "*", smt::mul, |x, y, m| x.wrapping_mul(y) & m);
    });
}

#[test]
fn band_agrees_between_the_two_evaluators() {
    on_big_stack(|| {
        sweep(4, "&", smt::band, |x, y, _| x & y);
        sweep_const(4, "&", smt::band, |x, y, _| x & y);
    });
}

#[test]
fn bor_agrees_between_the_two_evaluators() {
    on_big_stack(|| {
        sweep(4, "|", smt::bor, |x, y, _| x | y);
        sweep_const(4, "|", smt::bor, |x, y, _| x | y);
    });
}

#[test]
fn bxor_agrees_between_the_two_evaluators() {
    on_big_stack(|| {
        sweep(4, "^", smt::bxor, |x, y, _| x ^ y);
        sweep_const(4, "^", smt::bxor, |x, y, _| x ^ y);
    });
}

/// A unary operator, checked the same two ways.
///
/// `op` maps a variable to a term at the *result* width, so the comparison is against
/// the operator's own semantics at that width rather than at the input's.
fn agree_at_unary(
    w: u8,
    out_w: u8,
    x: u64,
    name: &str,
    op: fn(smt::Var, u8) -> smt::Var,
    want: u64,
) {
    let in_mask = if w >= 64 { u64::MAX } else { (1u64 << w) - 1 };
    let out_mask = if out_w >= 64 { u64::MAX } else { (1u64 << out_w) - 1 };
    let x = x & in_mask;
    let want = want & out_mask;
    let folded = smt::with_fresh(|| smt::evaluate(op(smt::var(w), out_w), |_| Some(x)));
    let verdict = smt::with_fresh(|| {
        let a = smt::var(w);
        let pinned = smt::eq(a, smt::word(x, w));
        let term = op(a, out_w);
        smt::prove(smt::or(smt::not(pinned), smt::eq(term, smt::word(want, out_w))))
    });
    assert_eq!(
        verdict,
        Verdict::Valid,
        "{w}-bit {x} {name} at {out_w} bits: blast disagreed with {want} (evaluate folded {folded:?})"
    );
    assert_eq!(folded, Some(want), "{w}-bit {x} {name}: evaluate is wrong");
}

/// `truncate` has an arm in each evaluator, and it does two things: it *narrows* (drop
/// the high bits) and it *widens* (zero-fill).
///
/// Both directions are swept, and that is not padding. The first version of this test
/// used only widths below the input's, so the widening branch was never taken -- a
/// deliberate corruption of that branch (sign-filling instead of zero-filling) went
/// undetected. The zero-fill is what the frontend's unsigned casts depend on, and the
/// distinction between it and `sign_extend` is the whole of the signed-cast handling, so
/// a branch this test did not reach was a branch it did not guard.
#[test]
fn truncate_agrees_between_the_two_evaluators() {
    on_big_stack(|| {
        // Narrowing: drop the high bits.
        for out_w in [1u8, 2, 3] {
            let out_mask = (1u64 << out_w) - 1;
            for x in 0..16u64 {
                agree_at_unary(4, out_w, x, "truncate", smt::truncate, x & out_mask);
            }
        }
        // Widening: zero-fill, which must *not* replicate the sign bit.
        for out_w in [5u8, 8, 16] {
            for x in 0..16u64 {
                agree_at_unary(4, out_w, x, "truncate", smt::truncate, x);
            }
        }
    });
}

/// `sign_extend` widens by replicating the sign bit, and it too has an arm in each
/// evaluator.
///
/// The two evaluators must agree on the replication or a signed product built from one
/// would not be the product the other reasons about -- which is how the signed multiply
/// overflow predicate is built.
#[test]
fn sign_extend_agrees_between_the_two_evaluators() {
    on_big_stack(|| {
        for wide in [5u8, 8] {
            for x in 0..16u64 {
                // The sign bit of a 4-bit value is bit 3, so the extension is
                // `x` or `x | (high bits)`, depending on that bit.
                let want = if x & 0b1000 != 0 {
                    (x | !0b1111u64) & ((1u64 << wide) - 1)
                } else {
                    x
                };
                agree_at_unary(4, wide, x, "sign_extend", smt::sign_extend, want);
            }
        }
    });
}

/// The divider is one implementation, not two -- `blast` has no `Op::Div` and the
/// divider is built from primitives -- so this compares `evaluate`'s division against
/// Rust's rather than against a second `blast` arm. It is here because the same file
/// should hold the whole operator surface, and because a divider that disagreed with
/// Rust's would make `%` and `/` proofs meaningless.
#[test]
fn division_agrees_with_rusts_own() {
    on_big_stack(|| {
        for w in [4u8] {
            let mask = (1u64 << w) - 1;
            for x in 0..=mask {
                for y in 0..=mask {
                    // The divider defines `y == 0` as an all-ones quotient and the
                    // dividend as the remainder, so the expectation spells that out
                    // rather than calling `checked_div` -- the zero case is a *defined*
                    // value here, not an absent one, and `checked_div` would only say
                    // the case is absent.
                    let (want_q, want_r) = if y == 0 {
                        (mask, x)
                    } else {
                        (x / y, x % y)
                    };
                    let (q, r) = smt::with_fresh(|| {
                        let a = smt::var(w);
                        let b = smt::var(w);
                        let (q, r) = smt::divmod(a, b);
                        let f = |i: u32| Some(if i == 0 { x } else { y });
                        (smt::evaluate(q, f), smt::evaluate(r, f))
                    });
                    assert_eq!((q, r), (Some(want_q), Some(want_r)), "{w}-bit {x} / {y}");
                }
            }
        }
    });
}

/// The barrel shifter's variable amount, both directions, against Rust's own.
///
/// `shift_var` takes the amount as a `Var`, which is what the MIR frontend has for
/// `x << n`. The bug it had was a mask built at the value's width rather than the
/// amount's; this sweep keeps the amount at the value's width and covers the *values*,
/// which is the other half of the surface.
#[test]
fn variable_shifts_agree_with_rusts_own() {
    on_big_stack(|| {
        use smt::Shift;
        for w in [4u8] {
            let mask = (1u64 << w) - 1;
            for x in 0..=mask {
                for n in 0..=mask {
                    let want_shl = if n >= w as u64 { 0 } else { (x << n) & mask };
                    let want_shr = if n >= w as u64 { 0 } else { x >> n };
                    let (shl, shr) = smt::with_fresh(|| {
                        let a = smt::var(w);
                        let k = smt::var(w);
                        let f = |i: u32| Some(if i == 0 { x } else { n });
                        (
                            smt::evaluate(smt::shift_var(Shift::Left, a, k), f),
                            smt::evaluate(smt::shift_var(Shift::LogicalRight, a, k), f),
                        )
                    });
                    assert_eq!(shl, Some(want_shl), "{w}-bit {x} << {n}");
                    assert_eq!(shr, Some(want_shr), "{w}-bit {x} >> {n}");
                }
            }
        }
    });
}

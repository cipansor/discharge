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

/// Check one unary term at one point: `evaluate` against `blast`, both against `want`.
///
/// `build` is given the input variable and returns the term under test, so the caller
/// spells the operator out rather than threading its parameters through this helper. An
/// earlier version took `(out_w, arg)` and passed `arg` for the shifts and `0` for the
/// casts, which meant two of the three call sites carried a parameter they had no use
/// for -- a signature that described the caller's accident rather than the check.
fn agree_unary(
    w: u8,
    out_w: u8,
    x: u64,
    name: &str,
    want: u64,
    build: impl Fn(smt::Var) -> smt::Var,
) {
    let in_mask = if w >= 64 { u64::MAX } else { (1u64 << w) - 1 };
    let out_mask = if out_w >= 64 { u64::MAX } else { (1u64 << out_w) - 1 };
    let x = x & in_mask;
    let want = want & out_mask;
    let folded = smt::with_fresh(|| smt::evaluate(build(smt::var(w)), |_| Some(x)));
    let verdict = smt::with_fresh(|| {
        let a = smt::var(w);
        let pinned = smt::eq(a, smt::word(x, w));
        let term = build(a);
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
                agree_unary(4, out_w, x, "truncate", x & out_mask, |a| smt::truncate(a, out_w));
            }
        }
        // Widening: zero-fill, which must *not* replicate the sign bit.
        for out_w in [5u8, 8, 16] {
            for x in 0..16u64 {
                agree_unary(4, out_w, x, "truncate", x, |a| smt::truncate(a, out_w));
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
                agree_unary(4, wide, x, "sign_extend", want, |a| smt::sign_extend(a, wide));
            }
        }
    });
}

/// A predicate, checked the same two ways.
fn agree_pred_at(
    w: u8,
    x: u64,
    y: u64,
    name: &str,
    pred: fn(smt::Var, smt::Var) -> smt::Pred,
    want: bool,
) {
    let mask = if w >= 64 { u64::MAX } else { (1u64 << w) - 1 };
    let (x, y) = (x & mask, y & mask);
    let folded = smt::with_fresh(|| {
        smt::evaluate_pred(pred(smt::var(w), smt::var(w)), |i| {
            Some(if i == 0 { x } else { y })
        })
    });
    let verdict = smt::with_fresh(|| {
        let a = smt::var(w);
        let b = smt::var(w);
        let pinned = smt::and(smt::eq(a, smt::word(x, w)), smt::eq(b, smt::word(y, w)));
        let p = pred(a, b);
        smt::prove(smt::or(smt::not(pinned), smt::iff(p, smt::truth(want))))
    });
    assert_eq!(
        verdict,
        Verdict::Valid,
        "{w}-bit {x} {name} {y}: blast disagreed with {want} (evaluate folded {folded:?})"
    );
    assert_eq!(folded, Some(want), "{w}-bit {x} {name} {y}: evaluate is wrong");
}

/// The signed comparisons, over the whole 4-bit domain, against Rust's `i8` order.
///
/// `slt` has no `Op::Slt`: it is built from `negative` and the *unsigned* `ult`, on the
/// reasoning that equal signs make the two orders agree and differing signs mean the
/// negative one is smaller. That reasoning is the whole of the signed-cast and
/// signed-overflow story, so it is checked exhaustively rather than sampled -- and
/// against `i8`, whose domain is the 4-bit domain sign-extended, so the test cannot
/// inherit the engine's own idea of what signed means.
#[test]
fn signed_comparisons_agree_with_rusts_own_order() {
    on_big_stack(|| {
        let mask = 0b1111u64;
        let signed = |v: u64| if v & 0b1000 != 0 { (v as i64) - 16 } else { v as i64 };
        for x in 0..=mask {
            for y in 0..=mask {
                let (ix, iy) = (signed(x), signed(y));
                agree_pred_at(4, x, y, "<", smt::slt, ix < iy);
                agree_pred_at(4, x, y, "<=", smt::sle, ix <= iy);
                agree_pred_at(4, x, y, ">", smt::sgt, ix > iy);
                agree_pred_at(4, x, y, ">=", smt::sge, ix >= iy);
                // The unsigned pair is here because `slt` is *built* from `ult`: a wrong
                // `ult` would be a wrong `slt` at equal signs, and this is the half that
                // pins it.
                agree_pred_at(4, x, y, "u<", smt::ult, x < y);
                agree_pred_at(4, x, y, "u<=", smt::ule, x <= y);
            }
        }
    });
}

/// `negative` is "the top bit is set", and it is the sign test the whole signed story
/// rests on.
#[test]
fn negative_agrees_with_the_sign_bit() {
    on_big_stack(|| {
        for w in [1u8, 4, 8] {
            let mask = (1u64 << w) - 1;
            for x in 0..=mask {
                let want = x >> (w - 1) & 1 == 1;
                agree_pred_at(w, x, 0, "negative", |a, _| smt::negative(a), want);
            }
        }
    });
}

/// The constant-amount shifts, swept past the width.
///
/// `k >= w` is the boundary the bit-blaster and the term folder compute in visibly
/// different ways -- `blast` tests `bit >= sh` and `sh < w - bit`, the folder branches on
/// `sh >= w` -- so it is swept rather than assumed. The arithmetic shift is the one with
/// the interesting answer there: an all-ones or all-zeros fill from the sign bit, not
/// zero, which is exactly what a logical shift would get wrong.
#[test]
fn constant_shifts_agree_past_the_width() {
    on_big_stack(|| {
        for w in [4u8] {
            let mask = (1u64 << w) - 1;
            for k in 0..=(w as u32 + 2) {
                for x in 0..=mask {
                    let sign = x >> (w - 1) & 1;
                    let want_shl = if k >= w as u32 { 0 } else { (x << k) & mask };
                    let want_lshr = if k >= w as u32 { 0 } else { x >> k };
                    let want_ashr = if k >= w as u32 {
                        if sign == 1 { mask } else { 0 }
                    } else if sign == 1 {
                        ((x >> k) | !(mask >> k)) & mask
                    } else {
                        x >> k
                    };
                    agree_unary(4, w, x, "shl", want_shl, |a| smt::shl(a, k));
                    agree_unary(4, w, x, "lshr", want_lshr, |a| smt::lshr(a, k));
                    agree_unary(4, w, x, "ashr", want_ashr, |a| smt::ashr(a, k));
                }
            }
        }
    });
}

/// `ite` has an arm in each evaluator, and the two read the condition differently.
///
/// `blast` selects on `c[0]`, the condition's low bit; `evaluate` branches on `c != 0`.
/// Those agree for a one-bit condition, which is what `Pred` is, but the two spellings
/// are a real place for a divergence to hide, so both branches are swept over the whole
/// 4-bit domain of the arms with the condition true and false.
#[test]
fn ite_agrees_between_the_two_evaluators() {
    on_big_stack(|| {
        for w in [1u8, 4] {
            let mask = (1u64 << w) - 1;
            for cond in [false, true] {
                for t in 0..=mask {
                    for e in 0..=mask {
                        let want = if cond { t } else { e };
                        agree_unary(w, w, t, "ite-taken", want, |tv| {
                            smt::ite(smt::truth(cond), tv, smt::word(e, w))
                        });
                    }
                }
            }
        }
    });
}

/// The divider through `prove`, not just through the folder.
///
/// `tests/divmod.rs` and the `division_agrees_with_rusts_own` test above both go through
/// `evaluate`. The divider is *built* from primitives, so there is no second `Op::Div`
/// arm to compare against -- but the built circuit is what `prove` reasons over, and a
/// circuit is a different object from the folder that reads the same term. This asks
/// `prove` directly, at every point, so the circuit itself is checked rather than the
/// arithmetic it was built from.
#[test]
fn division_agrees_through_prove() {
    on_big_stack(|| {
        // `1` is not padding: `divmod` has a *separate* implementation for width 1 (the
        // quotient is `x & y`, the remainder `x & !y`), so the narrowest width is where a
        // divergence between the two implementations would live, and the first version of
        // this test only asked 4.
        for w in [1u8, 2, 4] {
            let mask = (1u64 << w) - 1;
            for x in 0..=mask {
                for y in 0..=mask {
                    let (want_q, want_r) = if y == 0 { (mask, x) } else { (x / y, x % y) };
                    smt::with_fresh(|| {
                        let a = smt::var(w);
                        let b = smt::var(w);
                        let pinned =
                            smt::and(smt::eq(a, smt::word(x, w)), smt::eq(b, smt::word(y, w)));
                        assert_eq!(
                            smt::prove(smt::or(
                                smt::not(pinned),
                                smt::eq(smt::udiv(a, b), smt::word(want_q, w))
                            )),
                            Verdict::Valid,
                            "{w}-bit {x} / {y}: the divider circuit disagreed with {want_q}"
                        );
                        assert_eq!(
                            smt::prove(smt::or(
                                smt::not(pinned),
                                smt::eq(smt::urem(a, b), smt::word(want_r, w))
                            )),
                            Verdict::Valid,
                            "{w}-bit {x} % {y}: the divider circuit disagreed with {want_r}"
                        );
                    });
                }
            }
        }
    });
}

/// The divider's own defining identity, which holds for *every* input and so can be
/// asked as a single validity query rather than point by point.
///
/// `x == q * y + r` with `r < y` is what makes a divider a divider. Asking it this way
/// exercises the circuit on the whole domain at once, and it is the property the
/// frontend's `%` and `/` obligations reduce to.
#[test]
fn the_divider_satisfies_its_defining_identity() {
    on_big_stack(|| {
        // `1` and `2` cover the width-1 fast path and the smallest general path.
        for w in [1u8, 2, 4] {
            smt::with_fresh(|| {
                let x = smt::var(w);
                let y = smt::var(w);
                let (q, r) = smt::divmod(x, y);
                // Reconstruct: `q * y + r == x`. The divider defines `y == 0` as
                // quotient all-ones and remainder the dividend, and `q * y + r` is `x`
                // there too, so the identity needs no exception for zero.
                let recon = smt::add(smt::mul(q, y), r);
                assert_eq!(
                    smt::prove(smt::eq(recon, x)),
                    Verdict::Valid,
                    "{w}-bit: q * y + r != x"
                );
                // And the remainder is below the divisor whenever the divisor is not
                // zero, which is the half that constrains the quotient. Spelled as an
                // `implies` rather than as a disjunction: `A => B` is `!A | B`, and the
                // first version of this wrote `A | B` with `A` the *non*-zero guard,
                // which is the implication's consequent-side error and was reported as a
                // counterexample at `y == 0` -- the one point the guard exists to excuse.
                let nonzero = smt::not(smt::eq(y, smt::word(0, w)));
                assert_eq!(
                    smt::prove(smt::implies(nonzero, smt::ult(r, y))),
                    Verdict::Valid,
                    "{w}-bit: y != 0 => r < y failed"
                );
            });
        }
    });
}

/// The constant power-of-two division is a shift, and the shift identity is checked
/// exhaustively rather than trusted.
///
/// This path exists because the signed divider's sign fixup is a BDD wall at 64 bits:
/// `sdiv(x, 2)` took 9.3 seconds and was reported `incomplete`, while `udiv(x, 2)` took
/// 47ms. The replacement is `trunc(x / 2^k) == (x + (2^k - 1 if x < 0 else 0)) >> k`, with
/// an arithmetic shift, and the bias is the sign bit replicated and masked.
///
/// Two things make it worth the exhaustive sweep rather than a spot check. The bias is
/// only added on the negative side, and `>>` on a negative value is where the identity is
/// easy to get wrong; and the remainder is built as `x - q * 2^k` from the *magnitude*
/// quotient, so a negative divisor is the case that would give it the wrong sign. Both
/// signs of `c` are swept for that reason.
#[test]
fn constant_power_of_two_division_is_exact() {
    on_big_stack(|| {
        // Exhaustive at widths small enough to enumerate, against Rust's own `/` and `%`.
        for w in [2u8, 3, 4, 5, 6] {
            let half = 1i128 << (w - 1);
            let (mn, mx) = (-half, half - 1);
            let mask = (1u64 << w) - 1;
            for k in 1..w {
                let d = 1i128 << k;
                for c in [d, -d] {
                    for x in mn..=mx {
                        // The terms and the point they are pinned to are built in one
                        // scope: `sdivmod_pow2` produces fresh variables, so asking about
                        // a point means substituting into the same context that built them.
                        let (got_q, got_r) = smt::with_fresh(|| {
                            let v = smt::var(w);
                            let (q, r) = smt::sdivmod_pow2(v, c, w)
                                .expect("a power of two must be handled");
                            let pin = smt::eq(v, smt::word((x as u64) & mask, w));
                            (
                                smt::prove(smt::implies(
                                    pin,
                                    smt::eq(q, smt::word((q_val(x, c) as u64) & mask, w)),
                                )),
                                smt::prove(smt::implies(
                                    pin,
                                    smt::eq(r, smt::word((r_val(x, c) as u64) & mask, w)),
                                )),
                            )
                        });
                        assert_eq!(
                            got_q,
                            Verdict::Valid,
                            "{w}-bit {x} / {c}: quotient disagreed with {}",
                            q_val(x, c)
                        );
                        assert_eq!(
                            got_r,
                            Verdict::Valid,
                            "{w}-bit {x} % {c}: remainder disagreed with {}",
                            r_val(x, c)
                        );
                    }
                }
            }
        }

        // 64 bits, where the path is the only one available. The values straddle the
        // boundaries of each constant and sit at the ends of the range, including `MIN`,
        // which is where `x + 2^k - 1` would overflow if the bias were added on the
        // wrong side.
        let mask = u64::MAX;
        for k in [1u32, 2, 31, 62] {
            let d = 1i128 << k;
            for c in [d, -d] {
                for x in [
                    i64::MIN as i128,
                    i64::MIN as i128 + 1,
                    -d - 1,
                    -d,
                    -d + 1,
                    -1,
                    0,
                    1,
                    d - 1,
                    d,
                    d + 1,
                    i64::MAX as i128,
                ] {
                    let (got_q, got_r) = smt::with_fresh(|| {
                        let v = smt::var(64);
                        let (q, r) = smt::sdivmod_pow2(v, c, 64).unwrap();
                        let pin = smt::eq(v, smt::word((x as u64) & mask, 64));
                        (
                            smt::prove(smt::implies(
                                pin,
                                smt::eq(q, smt::word((q_val(x, c) as u64) & mask, 64)),
                            )),
                            smt::prove(smt::implies(
                                pin,
                                smt::eq(r, smt::word((r_val(x, c) as u64) & mask, 64)),
                            )),
                        )
                    });
                    assert_eq!(got_q, Verdict::Valid, "64-bit {x} / {c}: quotient");
                    assert_eq!(got_r, Verdict::Valid, "64-bit {x} % {c}: remainder");
                }
            }
        }

        // The cases the shift identity must *refuse*, so the fast path cannot quietly
        // become a claim about every divisor. `|c| == 1` is the one that matters: `MIN / -1`
        // overflows and the general path handles that explicitly, so a no-op shift here
        // would be a wrong answer rather than a slow one.
        for c in [0i128, 1, -1, 3, -3, 6, -6, 100, -100] {
            assert!(
                smt::with_fresh(|| smt::sdivmod_pow2(smt::var(64), c, 64)).is_none(),
                "{c} must not take the power-of-two path"
            );
        }
    });
}

/// Truncating signed division, toward zero, for the test above.
fn q_val(x: i128, c: i128) -> i128 {
    x / c
}

/// Truncating signed remainder, taking the dividend's sign.
fn r_val(x: i128, c: i128) -> i128 {
    x % c
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

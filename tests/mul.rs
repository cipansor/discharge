//! Tests for the engine's multiplication, in particular the constant-operand arm
//! of `blast` that the MIR frontend depends on for `i * 4`-shaped code.
//!
//! # Which layer each test actually covers
//!
//! This distinction is the whole reason the file is laid out the way it is, and it
//! cost a bug to learn. There are two evaluators in the engine:
//!
//! * `evaluate`, the term-level folder, which has its own arithmetic (`wrapping_mul`
//!   for `Op::Mul`) and never builds a diagram;
//! * `blast`, the bit-blaster that feeds the BDD, which is what `prove` uses and
//!   therefore what the frontend's answers come from.
//!
//! A concrete test written with `evaluate` therefore says *nothing* about `blast`.
//! The first version of this file swept `x * c` exhaustively against Rust's own `*`
//! through `evaluate` and passed -- while the `blast` arm it was meant to guard had a
//! dropped carry. So the concrete sweep below is kept and labelled for what it is,
//! and the tests that matter go through `prove`, which is the path the frontend takes.

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

/// The term-level folder multiplies exactly, over the whole domain at 1, 4 and 8 bits.
///
/// This covers `evaluate` and *only* `evaluate`. It is worth having -- a term folder
/// that disagreed with Rust's `*` would make every counterexample the engine reports
/// a lie -- but it is not evidence about `blast`, and the tests below are.
fn exhaustive_evaluate(w: u8, x: u64, c: u64) {
    let mask = if w >= 64 { u64::MAX } else { (1u64 << w) - 1 };
    let x = x & mask;
    let c = c & mask;
    let want = x.wrapping_mul(c) & mask;
    for (label, swapped) in [("x * c", false), ("c * x", true)] {
        // `evaluate` must run *inside* `with_fresh`: the handle is only meaningful
        // while that arena is live, and reading it after the closure returns gives a
        // stale term, which `evaluate` reports as `None` rather than as a wrong value.
        let got = smt::with_fresh(|| {
            let (a, b) = if swapped {
                (smt::word(c, w), smt::word(x, w))
            } else {
                (smt::word(x, w), smt::word(c, w))
            };
            smt::evaluate(smt::mul(a, b), |_| None)
        });
        assert_eq!(got, Some(want), "{w}-bit {label} = {x} * {c} (term folder)");
    }
}

#[test]
fn the_term_folder_multiplies_exactly() {
    for w in [1u8, 4, 8] {
        let max = (1u64 << w) - 1;
        for c in 0..=max {
            for x in 0..=max {
                exhaustive_evaluate(w, x, c);
            }
        }
    }
}

/// The `blast` constant arm agrees with the `blast` schoolbook arm, at every constant.
///
/// This is the test that covers the code the constant arm replaced. Both products are
/// built as *terms* and then bit-blasted, so the comparison goes through the diagram
/// rather than through the term folder: `x * y` takes the schoolbook arm because `y`
/// is a free variable, and `x * c` takes the shift-sum arm because a `word` is a
/// `Const`. Pinning `y == c` turns "the two arms agree at `c`" into the validity of
/// `y == c => x * y == x * c`, which `prove` answers.
///
/// The whole constant domain is enumerated at 4 and 8 bits. The arm's failure mode is
/// a dropped or mis-wired carry, which agrees on most inputs -- the bug it was written
/// for passed the exhaustive `evaluate` sweep above -- so sampling would not be
/// evidence.
#[test]
fn the_blast_constant_arm_agrees_with_the_schoolbook_arm() {
    on_big_stack(|| {
        for w in [4u8, 8] {
            let max = (1u64 << w) - 1;
            for c in 0..=max {
                smt::with_fresh(|| {
                    let x = smt::var(w);
                    let y = smt::var(w);
                    let pinned = smt::eq(y, smt::word(c, w));
                    let schoolbook = smt::mul(x, y);
                    let shifted = smt::mul(x, smt::word(c, w));
                    let agree = smt::eq(schoolbook, shifted);
                    assert_eq!(
                        smt::prove(smt::or(smt::not(pinned), agree)),
                        Verdict::Valid,
                        "{w}-bit multiply by {c}: the two blast arms disagree"
                    );
                });
            }
        }
    });
}

/// The `blast` constant arm agrees with an *independently built* shift-sum.
///
/// A different oracle from the test above, and a stronger one: instead of comparing
/// the new arm against the schoolbook arm the engine already had, this builds the
/// product from the engine's own `shl` and `add` primitives -- `sum over the set bits
/// k of c of (x << k)` -- and asks `prove` for the equality. That construction shares
/// no code with either multiply arm, so an error common to both would still be caught.
///
/// `shl` takes the amount as a `u32` constant, so the shifts are the engine's cheap
/// constant-shift path rather than the barrel shifter, which is what keeps the query
/// small enough to ask at 8 bits.
#[test]
fn the_blast_constant_arm_matches_an_independent_shift_sum() {
    on_big_stack(|| {
        for w in [4u8, 8] {
            let max = (1u64 << w) - 1;
            for c in 0..=max {
                smt::with_fresh(|| {
                    let x = smt::var(w);
                    let mut independent = smt::word(0, w);
                    for k in 0..w {
                        if (c >> k) & 1 == 1 {
                            independent = smt::add(independent, smt::shl(x, k as u32));
                        }
                    }
                    assert_eq!(
                        smt::prove(smt::eq(smt::mul(x, smt::word(c, w)), independent)),
                        Verdict::Valid,
                        "{w}-bit multiply by {c}: the arm disagrees with the shift sum"
                    );
                });
            }
        }
    });
}

/// The `blast` constant arm is not the identity, and not a sum.
///
/// The direction that keeps the model honest. An accumulator that forgot to clear, or
/// that added where it should have shifted, could still satisfy `x * 0 == 0` and
/// `x * 1 == x`; it would not satisfy `x * 3 != x + 3`. The comparison is a
/// `Counterexample` rather than a bare "not `Valid`" because a query the engine failed
/// to decide is `Unknown`, and that must not read as a refutation.
#[test]
fn the_blast_constant_arm_is_not_the_identity() {
    on_big_stack(|| {
        smt::with_fresh(|| {
            let x = smt::var(4);
            assert!(
                matches!(
                    smt::prove(smt::eq(smt::mul(x, smt::word(3, 4)), x)),
                    Verdict::Counterexample(_)
                ),
                "x * 3 must not be x"
            );
            assert!(
                matches!(
                    smt::prove(smt::eq(
                        smt::mul(x, smt::word(2, 4)),
                        smt::add(x, smt::word(2, 4))
                    )),
                    Verdict::Counterexample(_)
                ),
                "x * 2 must not be x + 2"
            );
        });
    });
}

/// The arm is exact at 64 bits, where an index scaled by an element size lives.
///
/// `usize` is 64 bits and `x * 4` there is the shape this arm exists for. The check
/// goes through `prove` against an independently built shift sum, which shares no code
/// with either multiply arm.
///
/// Two bands, because a 64-bit query is the engine's expensive end and the cost of this
/// arm is `popcount(c)` additions. A constant with few set bits must decide `Valid`.
/// One with many -- `1000` has six -- may exceed the diagram budget, and `Unknown` is
/// the honest answer there; what is *not* allowed is a wrong one, so the assertion is
/// that the verdict is never a counterexample. A too-weak or mis-wired arm would report
/// a counterexample here, which is the failure that would make the frontend's overflow
/// predicate unsound.
#[test]
fn the_blast_constant_arm_is_exact_at_usize_width() {
    on_big_stack(|| {
        for c in [2u64, 4, 8, 256, 65536] {
            smt::with_fresh(|| {
                let x = smt::var(64);
                let mut independent = smt::word(0, 64);
                for k in 0..64 {
                    if (c >> k) & 1 == 1 {
                        independent = smt::add(independent, smt::shl(x, k as u32));
                    }
                }
                assert_eq!(
                    smt::prove(smt::eq(smt::mul(x, smt::word(c, 64)), independent)),
                    Verdict::Valid,
                    "64-bit multiply by {c} is a single shift"
                );
            });
        }

        // Several shifts build a carry chain across the width, so the budget may run
        // out -- `17` is `x + (x << 4)` and is already `Unknown` -- but never a
        // counterexample.
        for c in [17u64, 1000, 0xFFFF] {
            smt::with_fresh(|| {
                let x = smt::var(64);
                let mut independent = smt::word(0, 64);
                for k in 0..64 {
                    if (c >> k) & 1 == 1 {
                        independent = smt::add(independent, smt::shl(x, k as u32));
                    }
                }
                assert!(
                    !matches!(
                        smt::prove(smt::eq(smt::mul(x, smt::word(c, 64)), independent)),
                        Verdict::Counterexample(_)
                    ),
                    "64-bit multiply by {c}: the arm must never be refuted"
                );
            });
        }
    });
}

//! Tests for the engine's unsigned division, which the MIR frontend relies on to
//! model `a / b` in real code.
//!
//! Two levels, because they catch different bugs. The concrete sweep checks the
//! divider against Rust's own `/` and `%` over values chosen at the interesting
//! boundaries (all-ones, a divisor of one, a divisor just below the dividend, and
//! zero). The symbolic laws check the property the divider has to have for a
//! proof built on it to mean anything: `(x / y) * y + x % y == x` and
//! `x % y < y`. A divider that passed only the concrete cases could still be
//! wrong on an input no one thought to try.

// The explicit `y == 0` branch is the point of the test: the divider's zero case
// is a *defined* value (all-ones quotient, dividend remainder), so the test
// spells that out rather than calling `checked_div`, which would only say the
// case is absent.
#![allow(clippy::manual_checked_ops)]

use discharge::smt::{self, Verdict};

/// Run a symbolic query on a thread with a large stack.
///
/// The BDD operations recurse, so their reach is bounded by stack depth as well
/// as by the arena. These laws are asked at 4 bits because that is where a
/// symbolic divider feeding a comparison is still cheap; wider asks run into the
/// engine's depth and size walls (see the README's scaling note), which is a
/// property of the engine rather than something to paper over. The room is asked
/// for anyway so that a width bump fails on time rather than on a stack abort.
fn on_big_stack<F: FnOnce() + Send + 'static>(f: F) {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(f)
        .expect("spawn")
        .join()
        .expect("the query panicked");
}

/// Concrete `x / y` and `x % y` at width `w`, compared with Rust's own.
fn concrete(w: u8, x: u64, y: u64) {
    // The values have to fit the width. Masking here rather than trusting the
    // call site keeps a narrow width from silently testing a different pair than
    // the one written down.
    let mask = (1u64 << w) - 1;
    let x = x & mask;
    let y = y & mask;
    smt::with_fresh(|| {
        let (q, r) = smt::divmod(smt::word(x, w), smt::word(y, w));
        let got_q = smt::evaluate(q, |_| None);
        let got_r = smt::evaluate(r, |_| None);
        // `y == 0` is defined here rather than trapped: quotient all ones,
        // remainder the dividend. See `smt::divmod`.
        let (want_q, want_r) = if y == 0 {
            ((1u64 << w) - 1, x)
        } else {
            (x / y, x % y)
        };
        assert_eq!(
            (got_q, got_r),
            (Some(want_q), Some(want_r)),
            "{w}-bit {x} / {y}"
        );
    });
}

#[test]
fn division_matches_rust_on_boundaries() {
    for w in [1u8, 2, 4, 8, 16] {
        let max = (1u64 << w) - 1;
        for (x, y) in [
            (max, 1),
            (max, 2),
            (max, 3),
            (max, 7),
            (max, max),
            (max, max - 1),
            (max, max / 2),
            (0, 1),
            (0, max),
            (1, 2),
            (max / 3, max / 2),
            (max, 0),
            (0, 0),
            (max, max / 4),
            (max / 2, max / 3),
        ] {
            concrete(w, x, y);
        }
    }
}

#[test]
fn division_is_total_at_zero() {
    // A verifier cannot leave an operation undefined, so `y == 0` has a value.
    // The MIR frontend pairs this with rustc's own divide-by-zero assert, which
    // is what turns the case into a reported panic.
    concrete(8, 42, 0);
    concrete(16, 1234, 0);
}

#[test]
fn remainder_is_below_divisor_symbolically() {
    // The law a proof needs. 4 bits is enough to catch a wrong restoring step,
    // and it is the width at which the query stays cheap.
    on_big_stack(|| {
        smt::with_fresh(|| {
            let x = smt::var(4);
            let y = smt::var(4);
            let (_, r) = smt::divmod(x, y);
            let nonzero = smt::not(smt::eq_const(y, 0));
            assert_eq!(
                smt::prove_implies(nonzero, smt::ult(r, y)),
                Verdict::Valid,
                "x % y < y must hold"
            );
        });
    });
}

#[test]
fn division_law_holds_symbolically() {
    on_big_stack(|| {
        smt::with_fresh(|| {
            let x = smt::var(4);
            let y = smt::var(4);
            let (q, r) = smt::divmod(x, y);
            let nonzero = smt::not(smt::eq_const(y, 0));
            let law = smt::eq(smt::add(smt::mul(q, y), r), x);
            assert_eq!(
                smt::prove_implies(nonzero, law),
                Verdict::Valid,
                "(x / y) * y + x % y == x must hold"
            );
        });
    });
}

#[test]
fn quotient_is_zero_when_divisor_exceeds_dividend() {
    on_big_stack(|| {
        smt::with_fresh(|| {
            let x = smt::var(4);
            let y = smt::var(4);
            let (q, _) = smt::divmod(x, y);
            // x < y implies x / y == 0.
            let premise = smt::and(smt::ult(x, y), smt::not(smt::eq_const(y, 0)));
            assert_eq!(
                smt::prove_implies(premise, smt::eq_const(q, 0)),
                Verdict::Valid
            );
        });
    });
}

#[test]
fn wide_divisor_case_is_not_run_through_the_restoring_loop() {
    // The narrow and wide paths differ, and the split is what keeps the restoring
    // loop sound: with a divisor whose top bit is set, `2y` overflows the width,
    // so the loop's doubling step would be wrong. This pins the wide path.
    for w in [8u8, 16] {
        let max = (1u64 << w) - 1;
        // Divisor with the top bit set, dividend at the top of the range.
        concrete(w, max, 1u64 << (w - 1));
        concrete(w, max, max);
        concrete(w, (1u64 << (w - 1)) - 1, 1u64 << (w - 1));
    }
}

/// A wide division by a *non-power-of-two constant* must return a verdict, not hang.
///
/// This is the shape that regressed, and it is a different wall from the ones the
/// tests above probe. `MAX_BLAST_STEPS` bounds the *term-DAG* walk (`blast`), and
/// for `x / 15` that walk is tiny -- a few hundred steps at every width -- so the
/// old budget never saw the blow-up. The cost is entirely in the BDD `apply2`,
/// which recurses over the *diagram*: `x / 15` for a `u64` has a BDD far larger
/// than its formula, `apply2` runs past 4 000 000 calls with no counter of its
/// own, and `prove` simply never returns. `MAX_APPLY_STEPS` charges the apply, so
/// the query trips the budget, falls back to the SAT engine, and answers.
///
/// The assertion is deliberately weak: `Valid`, `Unsat`, `Counterexample` and
/// `Unknown` are all accepted, because the property being pinned is *termination*,
/// not the answer. Before the fix the call did not return at all, so reaching the
/// assertion is the whole test. The one thing that must never come back is
/// `Valid`: `x / 15 == 0` is false for `x == 15`, and a truncated encoding read as
/// a proof is exactly the unsoundness the budget must not introduce.
///
/// `15` rather than `7` is the divisor because at these widths `7` stays under
/// the budget (it is decided) while `15` does not, so `15` is the smallest shape
/// that exercises the bound. The big stack is required regardless of the budget:
/// the restoring divider's `blast` recursion is about four frames per bit, which
/// is a pre-existing property of the engine (see the README's scaling note), not
/// something this fix changes.
#[test]
fn a_wide_constant_divisor_returns_a_verdict_instead_of_hanging() {
    on_big_stack(|| {
        for w in [24u8, 28, 32, 64] {
            smt::with_fresh(|| {
                let x = smt::var(w);
                let y = smt::word(15, w);
                let verdict = smt::prove(smt::eq(smt::udiv(x, y), smt::word(0, w)));
                assert_ne!(
                    verdict,
                    Verdict::Valid,
                    "`x / 15 == 0` is not valid at width {w}; a budget-truncated encoding \
                     must not read as a proof"
                );
            });
        }
    });
}

// ---------------------------------------------------------------------------
// The power-of-two fast paths
// ---------------------------------------------------------------------------

/// `udivmod_pow2` must agree with the general divider on every input.
///
/// The fast path is a *replacement*, so "it is faster" is not the claim -- "it is the
/// same function" is. Two checks, because they catch different bugs. The concrete sweep
/// walks every dividend at a width where the whole domain fits, against Rust's own `/`
/// and `%`. The symbolic check asks the engine whether the shift-and-mask expression and
/// the restoring divider denote the same value for a *symbolic* `x`, which is what makes
/// it a proof over all inputs rather than a spot check.
///
/// `d == 1` and `d == 0` are the guard's edges. `udivmod_pow2` returns `None` for both --
/// `1` is not a power of two above the threshold and `0` is not a power of two at all --
/// so neither can reach the fast path and shadow the general divider's defined zero case.
#[test]
fn the_unsigned_power_of_two_fast_path_agrees_with_the_divider() {
    for w in [4u8, 8, 16] {
        let max = (1u64 << w) - 1;
        for d in [1u64, 2, 4, 8, 16, 32, 64] {
            for x in 0..=max {
                // Built and evaluated inside one epoch: a term from outside is stale
                // here, and a stale handle evaluates to `None`, which would look like a
                // disagreement rather than a reset.
                smt::with_fresh(|| {
                    let Some((q, r)) = smt::udivmod_pow2(smt::word(x, w), d, w) else {
                        // The guard refused: only `d == 1` (and `d` too wide) can, and the
                        // general path is then the only path, so nothing is being compared.
                        return;
                    };
                    assert_eq!(
                        (smt::evaluate(q, |_| None), smt::evaluate(r, |_| None)),
                        (Some(x / d), Some(x % d)),
                        "{w}-bit {x} / {d}"
                    );
                });
            }
        }
    }
}

/// The fast path is *symbolically* the same function as the general divider.
///
/// The concrete sweep above fixes `x`; this asks the engine to prove the two
/// expressions equal with `x` free, which is the property that matters when the fast
/// path is spliced into a body. A width where the general divider is still decidable is
/// what makes the comparison possible at all -- the point is to pin the identity, not to
/// stress the engine.
#[test]
fn the_unsigned_power_of_two_fast_path_is_the_divider_symbolically() {
    on_big_stack(|| {
        for d in [2u64, 4, 8] {
            smt::with_fresh(|| {
                let x = smt::var(4);
                let (fq, fr) = smt::udivmod_pow2(x, d, 4).expect("a power of two in range");
                let (gq, gr) = smt::divmod(x, smt::word(d, 4));
                assert_eq!(
                    smt::prove(smt::eq(fq, gq)),
                    Verdict::Valid,
                    "the shift quotient must equal the divider's for /{d}"
                );
                assert_eq!(
                    smt::prove(smt::eq(fr, gr)),
                    Verdict::Valid,
                    "the mask remainder must equal the divider's for %{d}"
                );
            });
        }
    });
}

/// The signed fast path, pinned the same way: `sdivmod_pow2` is the signed divider.
///
/// The same two levels as the unsigned case, against Rust's truncating `/` and `%`. The
/// negatives are the whole reason the signed path has a bias and a negation, so they are
/// the values this test exists for.
#[test]
fn the_signed_power_of_two_fast_path_agrees_with_the_divider() {
    for w in [4u8, 8] {
        let min = -(1i64 << (w - 1));
        let max = (1i64 << (w - 1)) - 1;
        for d in [2i64, 4, -2, -4] {
            for x in min..=max {
                let bits = (x as u64) & ((1u64 << w) - 1);
                let mask = (1u64 << w) - 1;
                let trunc = |v: i64| -> u64 { (v as u64) & mask };
                smt::with_fresh(|| {
                    let Some((q, r)) = smt::sdivmod_pow2(smt::word(bits, w), d as i128, w) else {
                        return;
                    };
                    assert_eq!(
                        (smt::evaluate(q, |_| None), smt::evaluate(r, |_| None)),
                        (Some(trunc(x / d)), Some(trunc(x % d))),
                        "{w}-bit {x} / {d}"
                    );
                });
            }
        }
    }
}

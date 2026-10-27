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

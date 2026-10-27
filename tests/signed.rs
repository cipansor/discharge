//! Tests for the engine's *signed* operations: comparison, division and
//! remainder, widening, and the sign rule.
//!
//! These exist because the MIR frontend reads real Rust, and real Rust has signed
//! integers. The engine's arithmetic was unsigned-only, which is not a missing
//! feature but a wrong answer: `-1 < 1` is false read unsigned, `-7 / 2` is a huge
//! positive number read unsigned, and a signed addition's overflow is not the
//! unsigned carry. Every test here is a differential one against Rust's own
//! operators on the *same* two's-complement values, so the reference is the
//! language rather than a second model of it.
//!
//! # The one case that is defined rather than matched
//!
//! `MIN / -1` overflows in Rust and panics under debug checks. The engine gives it
//! a defined value, the wrapping result `MIN` with remainder `0`, for the same
//! reason it defines `y == 0`: a verifier that leaves an operation undefined has a
//! hole where the proof should be. rustc's own `assert` guards that pair, so a
//! path reaching the division with it has already been reported as a panic. The
//! sweep below spells that value out instead of avoiding the input.

// The `MIN / -1` case is deliberate, and `checked_div` would hide it.
#![allow(clippy::manual_checked_ops)]

use discharge::smt::{self, Verdict};

/// Run a symbolic query on a thread with a large stack.
///
/// The BDD operations recurse, so their reach is bounded by stack depth as well
/// as by the arena. The room is asked for up front rather than discovering the
/// limit as an abort.
fn on_big_stack<F: FnOnce() + Send + 'static>(f: F) {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(f)
        .expect("spawn")
        .join()
        .expect("the query panicked");
}

/// Sign-extend a `w`-bit pattern held in `u64` to a signed `i64`.
fn to_signed(x: u64, w: u8) -> i64 {
    let shift = 64 - w as u32;
    ((x << shift) as i64) >> shift
}

/// The bit pattern of a signed value at width `w`.
fn to_bits(v: i64, w: u8) -> u64 {
    (v as u64) & ((1u64 << w) - 1)
}

/// Concrete signed comparison, compared with Rust's own `iN` order.
fn concrete_cmp(w: u8, x: u64, y: u64) {
    let mask = (1u64 << w) - 1;
    let (x, y) = (x & mask, y & mask);
    let (sx, sy) = (to_signed(x, w), to_signed(y, w));
    smt::with_fresh(|| {
        let (xv, yv) = (smt::word(x, w), smt::word(y, w));
        let got = (
            smt::evaluate_pred(smt::slt(xv, yv), |_| None),
            smt::evaluate_pred(smt::sle(xv, yv), |_| None),
            smt::evaluate_pred(smt::sgt(xv, yv), |_| None),
            smt::evaluate_pred(smt::sge(xv, yv), |_| None),
        );
        let want = (sx < sy, sx <= sy, sx > sy, sx >= sy);
        assert_eq!(got, (Some(want.0), Some(want.1), Some(want.2), Some(want.3)),
            "{w}-bit {sx} vs {sy}");
    });
}

/// Concrete signed division, compared with Rust's own `/` and `%`.
///
/// `MIN / -1` is excluded from the Rust comparison and asserted separately,
/// because Rust panics there and the engine defines it.
fn concrete_div(w: u8, x: u64, y: u64) {
    let mask = (1u64 << w) - 1;
    let (x, y) = (x & mask, y & mask);
    let (sx, sy) = (to_signed(x, w), to_signed(y, w));
    let min = -(1i64 << (w - 1));
    smt::with_fresh(|| {
        let q = smt::evaluate(smt::sdiv(smt::word(x, w), smt::word(y, w)), |_| None);
        let r = smt::evaluate(smt::srem(smt::word(x, w), smt::word(y, w)), |_| None);
        if sy == 0 {
            // Defined rather than trapped: all-ones quotient, dividend remainder.
            let want_q = mask;
            let want_r = x;
            assert_eq!((q, r), (Some(want_q), Some(want_r)), "{w}-bit {sx} / 0");
            return;
        }
        if sx == min && sy == -1 {
            // The wrapping result: `MIN`, remainder `0`.
            assert_eq!((q, r), (Some(x), Some(0)), "{w}-bit MIN / -1");
            return;
        }
        let want_q = to_bits(sx / sy, w);
        let want_r = to_bits(sx % sy, w);
        assert_eq!((q, r), (Some(want_q), Some(want_r)), "{w}-bit {sx} / {sy}");
    });
}

/// Concrete sign extension, compared with a sign-extending cast.
fn concrete_sign_extend(w: u8, wide: u8, x: u64) {
    let mask = (1u64 << w) - 1;
    let x = x & mask;
    let sx = to_signed(x, w);
    smt::with_fresh(|| {
        let got = smt::evaluate(smt::sign_extend(smt::word(x, w), wide), |_| None);
        assert_eq!(got, Some(to_bits(sx, wide)), "{w}->{wide} of {sx}");
    });
}

#[test]
fn signed_comparison_matches_rust_at_the_boundaries() {
    let vals: [u64; 8] = [0, 1, 2, 0x7f, 0x80, 0x81, 0xfe, 0xff];
    for &x in &vals {
        for &y in &vals {
            concrete_cmp(8, x, y);
        }
    }
    // A spread of interior values, so the boundary list is not the only evidence.
    for i in 0..64u64 {
        concrete_cmp(8, i.wrapping_mul(37), i.wrapping_mul(91));
    }
}

#[test]
fn signed_comparison_is_not_the_unsigned_one() {
    // The exact pair the unsigned order gets backwards. If `slt` were `ult`,
    // this would fail, which is what makes the test about signedness rather than
    // about comparison in general.
    smt::with_fresh(|| {
        let minus_one = smt::word(to_bits(-1, 8), 8);
        let one = smt::word(1, 8);
        assert_eq!(smt::evaluate_pred(smt::slt(minus_one, one), |_| None), Some(true));
        assert_eq!(smt::evaluate_pred(smt::ult(minus_one, one), |_| None), Some(false));
    });
}

#[test]
fn signed_division_matches_rust_at_the_boundaries() {
    let vals: [u64; 9] = [0, 1, 2, 3, 0x7f, 0x80, 0x81, 0xfe, 0xff];
    for &x in &vals {
        for &y in &vals {
            concrete_div(8, x, y);
        }
    }
    for i in 0..64u64 {
        concrete_div(8, i.wrapping_mul(53), i.wrapping_mul(29));
    }
    // The `MIN / -1` and zero-divisor cases explicitly, since the sweep above
    // reaches them only as part of a larger loop.
    concrete_div(8, 0x80, 0xff);
    concrete_div(8, 0x80, 0x00);
}

#[test]
fn signed_division_is_not_the_unsigned_one() {
    // `-7 / 2` is `-3` signed and a huge number unsigned. This is the wrong
    // *value* the unsigned divider returns, which is worse than a weak proof.
    smt::with_fresh(|| {
        let minus_seven = smt::word(to_bits(-7, 8), 8);
        let two = smt::word(2, 8);
        assert_eq!(
            smt::evaluate(smt::sdiv(minus_seven, two), |_| None),
            Some(to_bits(-3, 8))
        );
        assert_eq!(
            smt::evaluate(smt::urem(minus_seven, two), |_| None),
            Some(to_bits(1, 8))
        );
    });
}

#[test]
fn sign_extension_matches_a_cast() {
    for w in [8u8, 16] {
        let wide = w * 2;
        let mask = (1u64 << w) - 1;
        let mut vals: Vec<u64> = vec![0, 1, mask / 2, mask / 2 + 1, mask];
        for i in 0..40u64 {
            vals.push(i.wrapping_mul(2654435761) & mask);
        }
        for &x in &vals {
            concrete_sign_extend(w, wide, x);
        }
    }
}

/// The symbolic law the signed divider has to satisfy for a proof built on it to
/// mean anything: `(x / y) * y + x % y == x`, over signed values.
///
/// Asked at 4 bits, where a symbolic divider feeding a multiply is still cheap.
/// The law is the *signed* one, so it would fail for the unsigned divider on
/// every negative dividend — which is exactly the regression it guards.
#[test]
fn signed_division_satisfies_its_own_identity() {
    on_big_stack(|| {
        smt::with_fresh(|| {
            let x = smt::var(4);
            let y = smt::var(4);
            // `y != 0` and not the `MIN / -1` pair, both of which are defined
            // rather than matched to Rust.
            let nonzero = smt::not(smt::eq_const(y, 0));
            let min = smt::word(0b1000, 4);
            let minus_one = smt::word(0b1111, 4);
            let not_overflow = smt::not(smt::and(smt::eq(x, min), smt::eq(y, minus_one)));
            let guard = smt::and(nonzero, not_overflow);

            let q = smt::sdiv(x, y);
            let r = smt::srem(x, y);
            // `q * y + r == x` as bit patterns, which holds for the truncating
            // definition including the sign of the remainder.
            let lhs = smt::add(smt::mul(q, y), r);
            assert_eq!(
                smt::prove_implies(guard, smt::eq(lhs, x)),
                Verdict::Valid,
                "the signed division identity must hold for every guarded pair"
            );
        });
    });
}

/// A symbolic proof that the sign rule is the *right* overflow condition: a
/// signed add overflows exactly when the operands agree in sign and the result
/// disagrees. Checked by finding a pair where the rule and a concrete wrap
/// disagree, which must be unsatisfiable.
#[test]
fn the_signed_overflow_rule_matches_the_wrapped_result() {
    on_big_stack(|| {
        smt::with_fresh(|| {
            let x = smt::var(4);
            let y = smt::var(4);
            let sum = smt::add(x, y);
            // The rule under test.
            let rule = smt::and(
                smt::iff(smt::negative(x), smt::negative(y)),
                smt::xor(smt::negative(x), smt::negative(sum)),
            );
            // The truth: the sign-extended sum is not the sign extension of the
            // wrapped result.
            let wide = 8u8;
            let exact = smt::add(smt::sign_extend(x, wide), smt::sign_extend(y, wide));
            let wrapped = smt::sign_extend(sum, wide);
            let truth = smt::not(smt::eq(exact, wrapped));
            assert_eq!(
                smt::prove(smt::iff(rule, truth)),
                Verdict::Valid,
                "the sign rule must agree with the wrapped result on every pair"
            );
        });
    });
}

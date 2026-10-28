//! The symbolic **oracle** for the proved arithmetic primitives.
//!
//! The runtime half of this module — [`checked_add`], [`saturating_add`],
//! [`mul_div`], [`Fixed`] — now lives in the standalone `discharge-arithmetic`
//! crate, which is `no_std`, `#![forbid(unsafe_code)]`, has no dependencies, and
//! proves its own properties by exhaustive enumeration *without* the `smt`
//! engine. Those items are re-exported here unchanged, so this crate's public
//! surface and every caller of `discharge::logic` are unaffected by the split.
//!
//! What stays in this module is the second opinion. The `verify_*` functions
//! state the **same** obligations symbolically, at widths the enumeration cannot
//! reach, and [`crate::smt`] discharges them. `tests/oracle.rs` then cross-checks
//! the two engines against each other: where both decide, they must agree, and
//! where only one can (the 32-bit two-variable domains) the symbolic engine is
//! the one that answers.
//!
//! This is the same division of labour as the MIR frontend: the crate owns a
//! self-contained mechanism, and the heavier external one is only ever an
//! oracle. See `README.md`, "Two engines, one obligation".

use crate::smt::{self, Verdict};

// The runtime primitives, unchanged, now owned by the standalone crate.
pub use discharge_arithmetic::checked::{
    checked_add, checked_mul, checked_sub, mul_div, saturating_add, saturating_sub,
};
pub use discharge_arithmetic::fixed::Fixed;

// ---------------------------------------------------------------------------
// Symbolic proofs about the primitives
// ---------------------------------------------------------------------------

/// The classic overflow test, proved sound: for a wrapping 8-bit sum,
/// "the result is below `a`" and "the result is below `b`" are *the same
/// event*. That is exactly why `checked_add` can test either one and why the
/// wrapped result is a reliable overflow flag even when the true sum is lost.
pub fn verify_checked_add() -> Verdict {
    smt::with_fresh(|| {
        let a = smt::var(8);
        let b = smt::var(8);
        let sum = smt::add(a, b);
        smt::prove(smt::iff(smt::ult(sum, a), smt::ult(sum, b)))
    })
}

/// Saturating add never wraps below an operand: the *saturating* result is always `>= a`
/// and `>= b`, with no hypothesis.
///
/// The previous version proved `a <= sum => (a <= sum && b <= sum)` about the *wrapping* sum
/// and never built the saturating result at all. That is a conditional statement about a
/// different quantity than the comment names -- and the interesting case, where the sum
/// overflows and saturation is what saves the bound, is exactly the case its hypothesis
/// excludes. The goal below is the unconditional property, over the saturating value.
pub fn verify_saturating_add_bounds() -> Verdict {
    smt::with_fresh(|| {
        let a = smt::var(8);
        let b = smt::var(8);
        let sum = smt::add(a, b);
        // Overflow iff the wrapped sum fell below an operand; then saturate to all ones.
        let overflow = smt::ult(sum, a);
        let sat = smt::ite(overflow, smt::all_ones(8), sum);
        smt::prove(smt::and(smt::ule(a, sat), smt::ule(b, sat)))
    })
}

/// `x - x == 0` for every width, the cancellation law for subtraction.
pub fn verify_sub_self_is_zero(width: u8) -> Verdict {
    smt::with_fresh(|| {
        let x = smt::var(width);
        let zero = smt::word(0, width);
        smt::prove(smt::eq(smt::sub(x, x), zero))
    })
}

/// The algebraic laws that an optimiser, a static analyser or a hand proof
/// relies on. Each is discharged symbolically; all of them must come back
/// `Valid`. Returns the number of laws proved.
pub fn verify_algebraic_identities() -> usize {
    let mut proved = 0;
    for w in [8u8, 16, 32] {
        // Kept as a fixed array, not a Vec, so this module needs no allocator.
        let verdicts: [Verdict; 10] = smt::with_fresh(|| {
            let x = smt::var(w);
            let zero = smt::word(0, w);
            let one = smt::word(1, w);
            let all_ones = smt::all_ones(w);
            [
                // x + 0 == x
                smt::prove(smt::eq(smt::add(x, zero), x)),
                // x * 1 == x
                smt::prove(smt::eq(smt::mul(x, one), x)),
                // x * 0 == 0
                smt::prove(smt::eq(smt::mul(x, zero), zero)),
                // x | 0 == x
                smt::prove(smt::eq(smt::bor(x, zero), x)),
                // x & all_ones == x
                smt::prove(smt::eq(smt::band(x, all_ones), x)),
                // x ^ x == 0
                smt::prove(smt::eq(smt::bxor(x, x), zero)),
                // x - x == 0
                smt::prove(smt::eq(smt::sub(x, x), zero)),
                // x >> w == 0 (over-shift is defined, not UB)
                smt::prove(smt::eq(smt::lshr(x, w as u32), zero)),
                // 0 <= x, always
                smt::prove(smt::ule(zero, x)),
                // x <= 2^w - 1, always -- the range law that says an `w`-bit value cannot
                // exceed its width. This slot previously held `ult(x, 0) <=> false`, which
                // is a tautology of the *encoding* (an unsigned value is never below zero)
                // rather than a statement about `x`: it is unchanged by substituting any
                // term for `x`, including a constant, so it added no coverage while the
                // comment claimed the range law. `all_ones(w)` is `2^w - 1`, so this is the
                // "x < 2^w" law written in a form that fits the width.
                smt::prove(smt::ule(x, all_ones)),
            ]
        });
        for v in verdicts {
            if v.is_proved() {
                proved += 1;
            }
        }
    }
    proved
}

/// `mul_div` widens to 64 bits precisely because a product of two `w`-bit values
/// needs `2w` bits. This proves the *shape* of that argument at a width the BDD
/// can still handle: if each factor is below `2^(w/2)`, the product fits.
///
/// Note the honest boundary. The same statement at 8-bit factors
/// (`a < 16 && b < 16 => a*b < 226`) exhausts the node budget and comes back
/// [`Verdict::Unknown`]: the middle bits of a wide multiplier have
/// exponentially large BDDs. That is a real limit of this engine, not a bug, and
/// the test suite asserts that the engine *says so* rather than guessing.
pub fn verify_product_of_bounded_fits() -> Verdict {
    smt::with_fresh(|| {
        let a = smt::var(4);
        let b = smt::var(4);
        let pre = smt::and(smt::ult_const(a, 4), smt::ult_const(b, 4));
        let prod = smt::mul(a, b);
        // a <= 3 and b <= 3  =>  a*b <= 9, which fits in 4 bits.
        smt::prove_implies(pre, smt::ule_const(prod, 9))
    })
}

/// The engine must be *honest* about scale: when a formula exceeds the node
/// budget it returns [`Verdict::Unknown`], never a wrong answer. This asks about
/// a deliberately hard identity (a 12-bit multiplier compared against a second,
/// structurally different one) and asserts we get a proof or an admission of
/// ignorance — never a bogus refutation.
pub fn hard_multiplier_query() -> Verdict {
    smt::with_fresh(|| {
        let a = smt::var(12);
        let b = smt::var(12);
        let c = smt::var(12);
        // (a * b) * c == a * (b * c): true, but notorious for BDD blow-up.
        let left = smt::mul(smt::mul(a, b), c);
        let right = smt::mul(a, smt::mul(b, c));
        smt::prove(smt::eq(left, right))
    })
}

/// Adding two non-negative Q16.16 values cannot overflow a signed 16-bit sum when
/// each is bounded by `2^14 - 1`. This is the guard a controller uses before summing terms.
///
/// The bound is `2^14 - 1`, not `2^14`. A signed 16-bit value tops out at `2^15 - 1`, and at
/// the inclusive bound `2^14` the sum `2^14 + 2^14` is exactly `2^15`, which sets the sign
/// bit and reads as `-32768`. The proof used to conclude only `sum <= 2^15` while the
/// comment said "sign bit clear": the conclusion was true and one larger than the property
/// it claimed, which is the same off-by-one a caller reading the guard would act on.
pub fn verify_fixed_add_no_overflow() -> Verdict {
    smt::with_fresh(|| {
        // 16-bit operands standing in for the sign+integer part, so the BDD
        // stays small while the *structure* of the argument is the real one.
        let a = smt::var(16);
        let b = smt::var(16);
        // a, b <= 2^14 - 1  =>  a + b <= 2^15 - 2, so the sign bit stays clear.
        let bound = (1u64 << 14) - 1;
        let a_ok = smt::ule_const(a, bound);
        let b_ok = smt::ule_const(b, bound);
        let sum = smt::add(a, b);
        let fits = smt::ule_const(sum, (1u64 << 15) - 1);
        let pre = smt::and(a_ok, b_ok);
        smt::prove_implies(pre, fits)
    })
}

/// `to_int(from_int(k)) == k`: the integer round-trip is lossless.
pub fn verify_fixed_roundtrip() -> Verdict {
    smt::with_fresh(|| {
        // 8-bit stand-in for a signed integer part.
        let k = smt::var(8);
        // from_int(k) = k << 16, to_int truncates back. At 8 bits we model the
        // shift/truncate pair by proving (k << 4) >> 4 == k for k < 16.
        let small = smt::ult_const(k, 16);
        let shifted = smt::shl(k, 4);
        let back = smt::lshr(shifted, 4);
        smt::prove_implies(small, smt::eq(back, k))
    })
}

/// `k * SCALE / SCALE == k`, the fixed-point identity behind unit conversion.
///
/// Unlike [`verify_fixed_roundtrip`], which models `from_int`/`to_int` as the shift pair
/// `<<` then `>>`, this one performs a real `bvmul` by the scale factor and *then* divides
/// by shifting. That distinction is the whole content of the identity: the previous version
/// was a copy of the roundtrip proof with only the local variable names changed, so it never
/// mentioned a scale factor at all and would have "proved" the identity for any scale,
/// including one that is not a power of two. Multiplying by the factor is what makes the
/// statement be about unit conversion.
pub fn verify_scale_identity() -> Verdict {
    smt::with_fresh(|| {
        let k = smt::var(8);
        // `k < 16` keeps `k * 16` inside 8 bits, so the multiply itself cannot wrap and
        // the only question is whether dividing by the scale recovers `k`.
        let small = smt::ult_const(k, 16);
        let scaled = smt::mul(k, smt::word(16, 8));
        let unscaled = smt::lshr(scaled, 4);
        smt::prove_implies(small, smt::eq(unscaled, k))
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn checked_add_is_total() {
        assert!(verify_checked_add().is_proved());
    }

    #[test]
    fn saturating_add_bounds_hold() {
        assert!(verify_saturating_add_bounds().is_proved());
        // Teeth: without saturation the bound is false, so the `ite` is load-bearing and
        // this is not just a restatement of the wrapping-sum law.
        smt::with_fresh(|| {
            let a = smt::var(8);
            let b = smt::var(8);
            let sum = smt::add(a, b);
            assert!(
                !smt::prove(smt::and(smt::ule(a, sum), smt::ule(b, sum))).is_proved(),
                "the wrapping sum must violate the bound for some input"
            );
        });
    }

    #[test]
    fn subtraction_cancels() {
        for w in [8u8, 16, 32] {
            assert!(verify_sub_self_is_zero(w).is_proved(), "width {}", w);
        }
    }

    #[test]
    fn algebraic_laws_hold() {
        // 10 laws x 3 widths
        assert_eq!(verify_algebraic_identities(), 30);
    }

    #[test]
    fn bounded_products_do_not_wrap() {
        assert!(verify_product_of_bounded_fits().is_proved());
    }

    #[test]
    fn the_engine_never_lies_about_hard_formulas() {
        // Either a proof or an honest "unknown"; never a false refutation.
        let v = hard_multiplier_query();
        assert!(
            matches!(v, Verdict::Valid | Verdict::Unknown),
            "engine returned an unjustified verdict: {}",
            v
        );
    }

    #[test]
    fn fixed_point_roundtrips() {
        assert!(verify_fixed_roundtrip().is_proved());
        assert!(verify_scale_identity().is_proved());
        // Teeth: the identity must depend on the scale *being* `SCALE`. With a
        // non-power-of-two factor the same shift does not recover `k`, so the multiply in
        // the proof is load-bearing and this is not the roundtrip proof renamed.
        smt::with_fresh(|| {
            let k = smt::var(8);
            let small = smt::ult_const(k, 16);
            let scaled = smt::mul(k, smt::word(10, 8));
            let unscaled = smt::lshr(scaled, 4);
            assert!(
                !smt::prove_implies(small, smt::eq(unscaled, k)).is_proved(),
                "a scale of 10 must not satisfy the identity"
            );
        });
    }

    #[test]
    fn fixed_add_guard_is_sound() {
        assert!(verify_fixed_add_no_overflow().is_proved());
        // Teeth: the bound has to be `2^14 - 1`. With `2^14` the sum `2^14 + 2^14 = 2^15`
        // sets the sign bit, so the goal `sum <= 2^15 - 1` must be refuted -- the old proof
        // concluded the weaker `sum <= 2^15` and passed anyway.
        smt::with_fresh(|| {
            let a = smt::var(16);
            let b = smt::var(16);
            let bound = 1u64 << 14;
            let pre = smt::and(smt::ule_const(a, bound), smt::ule_const(b, bound));
            let sum = smt::add(a, b);
            assert!(
                !smt::prove_implies(pre, smt::ule_const(sum, (1u64 << 15) - 1)).is_proved(),
                "the inclusive bound 2^14 lets the sum reach 2^15, which overflows i16"
            );
        });
        // And the concrete witness: 2^14 + 2^14 overflows a signed 16-bit add.
        assert_eq!((16384i32 + 16384) as i16, -32768);
    }

    #[test]
    fn fixed_to_int_truncates_toward_zero() {
        // `-0.5` and `-1/65536` both have integer part zero, not -1. An arithmetic shift
        // floors, so the old `>> 16` was wrong for every negative fractional input.
        assert_eq!(Fixed::from_bits(-32768).to_int(), 0);
        assert_eq!(Fixed::from_bits(-1).to_int(), 0);
        assert_eq!(Fixed::from_bits(-65536).to_int(), -1);
        assert_eq!(Fixed::from_bits(-65537).to_int(), -1);
        assert_eq!(Fixed::from_bits(65535).to_int(), 0);
        assert_eq!(Fixed::from_bits(i32::MIN).to_int(), -32768);
        assert_eq!(Fixed::from_bits(i32::MAX).to_int(), 32767);
        // Matches the language's own cast, which is the definition of "toward zero".
        for bits in [i32::MIN, -70000, -65536, -32768, -1, 0, 1, 32768, 65535, i32::MAX] {
            assert_eq!(
                Fixed::from_bits(bits).to_int(),
                bits / 65536,
                "bits {}",
                bits
            );
        }
    }

    #[test]
    fn fixed_from_int_saturates_instead_of_wrapping() {
        assert_eq!(Fixed::from_int(0).to_bits(), 0);
        assert_eq!(Fixed::from_int(1).to_bits(), 65536);
        assert_eq!(Fixed::from_int(-1).to_bits(), -65536);
        assert_eq!(Fixed::from_int(32767).to_bits(), 32767 << 16);
        assert_eq!(Fixed::from_int(-32768).to_bits(), i32::MIN);
        // Out of range: clamp, do not wrap to the opposite sign.
        assert_eq!(Fixed::from_int(32768), Fixed::MAX);
        assert_eq!(Fixed::from_int(40000), Fixed::MAX);
        assert_eq!(Fixed::from_int(-32769), Fixed::MIN);
        assert_eq!(Fixed::from_int(i32::MAX), Fixed::MAX);
    }

    #[test]
    fn runtime_behaviour_matches_the_proof() {
        assert_eq!(checked_add(200, 55), Some(255));
        assert_eq!(checked_add(u32::MAX, 1), None);
        assert_eq!(saturating_add(u32::MAX, 1), u32::MAX);
        assert_eq!(saturating_sub(0, 1), 0);
        assert_eq!(mul_div(1000, 1000, 8), Some(125_000));
        assert_eq!(mul_div(1, 1, 0), None);

        let a = Fixed::from_int(3);
        let b = Fixed::from_int(4);
        assert_eq!(a.saturating_add(b), Fixed::from_int(7));
        assert_eq!(a.to_int(), 3);
        assert_eq!(a.saturating_mul_int(2), Fixed::from_int(6));
        assert_eq!(a.checked_div_int(0), None);
        // The doc names only the zero divisor; the overflow case is the other `None`, and
        // the comment above is a claim about the function's failure modes, so pin both.
        assert_eq!(Fixed::MIN.checked_div_int(-1), None);
        assert_eq!(Fixed::from_bits(i32::MIN).checked_div_int(2), Some(Fixed(i32::MIN / 2)));
    }
}

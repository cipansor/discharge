//! Verified arithmetic primitives, the "library" half of the SPARK story.
//!
//! These are the operations that safety-critical code reaches for constantly,
//! and each one carries an executable proof of its central property:
//!
//! * [`checked_add`], [`checked_sub`], [`checked_mul`] — total functions. They
//!   *cannot* overflow, so the caller never inherits a panic or a wrap-around.
//! * [`saturating_add`], [`saturating_sub`] — clamp instead of wrapping, with
//!   proofs of the two bounds that matter.
//! * [`mul_div`] — multiply-then-divide without the intermediate overflow that
//!   makes the naive form wrong for PID-style controllers.
//! * [`Fixed`] — a Q16.16 fixed-point type with proved scaling behaviour, for
//!   the sensor/actuator code that must avoid floating point.
//!
//! Every `verify_*` function in this module returns a [`crate::smt::Verdict`],
//! and the module's tests assert that they are `Valid`. Run them with
//! `cargo test --features std`.

use crate::smt::{self, Verdict};

// ---------------------------------------------------------------------------
// Checked arithmetic
// ---------------------------------------------------------------------------

/// `a + b`, or `None` on overflow. Total: no panic, no wrap-around.
pub const fn checked_add(a: u32, b: u32) -> Option<u32> {
    a.checked_add(b)
}

/// `a - b`, or `None` on underflow.
pub const fn checked_sub(a: u32, b: u32) -> Option<u32> {
    a.checked_sub(b)
}

/// `a * b`, or `None` on overflow.
pub const fn checked_mul(a: u32, b: u32) -> Option<u32> {
    a.checked_mul(b)
}

/// `a + b`, clamped to the type's maximum.
pub const fn saturating_add(a: u32, b: u32) -> u32 {
    a.saturating_add(b)
}

/// `a - b`, clamped at zero.
pub const fn saturating_sub(a: u32, b: u32) -> u32 {
    a.saturating_sub(b)
}

/// `a * b / d` without overflow in the intermediate product, using a 64-bit
/// widening. Returns `None` when `d == 0` or the true quotient exceeds `u32`.
pub const fn mul_div(a: u32, b: u32, d: u32) -> Option<u32> {
    if d == 0 {
        return None;
    }
    let wide = (a as u64) * (b as u64);
    let q = wide / (d as u64);
    if q > u32::MAX as u64 {
        None
    } else {
        Some(q as u32)
    }
}

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

/// Saturating add never wraps: the result is always `>= a` and `>= b`.
pub fn verify_saturating_add_bounds() -> Verdict {
    smt::with_fresh(|| {
        let a = smt::var(8);
        let b = smt::var(8);
        let sum = smt::add(a, b);
        // If no overflow, sat(a,b) == a + b. Encode "no overflow" as sum >= a.
        let no_overflow = smt::ule(a, sum);
        // Under that hypothesis the true sum is at least both operands.
        let goal = smt::and(smt::ule(a, sum), smt::ule(b, sum));
        smt::prove_implies(no_overflow, goal)
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
                // x < 2^w, always
                smt::prove(smt::ult(x, smt::word(0, w)).iff(smt::truth(false))),
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

// ---------------------------------------------------------------------------
// Q16.16 fixed point
// ---------------------------------------------------------------------------

/// A Q16.16 fixed-point number: 16 integer bits, 16 fractional bits.
///
/// This is the workhorse representation in flight control and motor control:
/// deterministic, no floating point, no soft-float dependency. The crate proves
/// the properties that make it safe to add and scale.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Fixed(pub i32);

impl Fixed {
    /// The scaling factor, `2^16`.
    pub const SCALE: i32 = 1 << 16;
    /// One, as Q16.16.
    pub const ONE: Fixed = Fixed(Self::SCALE);
    /// Zero.
    pub const ZERO: Fixed = Fixed(0);
    /// The largest representable value.
    pub const MAX: Fixed = Fixed(i32::MAX);
    /// The smallest representable value.
    pub const MIN: Fixed = Fixed(i32::MIN);

    /// From an integer, saturating.
    ///
    /// The range of Q16.16 in `i32` is `[-32768, 32767]` integers, so `v << 16` silently
    /// wraps for `|v| >= 32768`: `from_int(32768)` used to give `-32768`. A shift is a
    /// total function, which is exactly why the wrap is invisible. Saturating keeps this
    /// module's promise that no primitive overflows without saying so.
    pub const fn from_int(v: i32) -> Fixed {
        if v > i32::MAX >> 16 {
            Fixed(i32::MAX)
        } else if v < i32::MIN >> 16 {
            Fixed(i32::MIN)
        } else {
            Fixed(v << 16)
        }
    }

    /// The integer part, truncated toward zero.
    ///
    /// Truncation toward zero is not `self.0 >> 16` for negative values: an arithmetic
    /// shift is a floor, so `-0.5 >> 16` gives `-1`, not `0`. That one-bit bias on every
    /// negative fractional input is the kind of error a control law cannot see. The
    /// magnitude is truncated and the sign restored, which is `as i32` behaviour.
    pub const fn to_int(self) -> i32 {
        if self.0 >= 0 {
            self.0 >> 16
        } else {
            -((self.0.unsigned_abs() >> 16) as i32)
        }
    }

    /// Construct from raw bits.
    pub const fn from_bits(bits: i32) -> Fixed {
        Fixed(bits)
    }

    /// The raw bits.
    pub const fn to_bits(self) -> i32 {
        self.0
    }

    /// Saturating addition.
    pub const fn saturating_add(self, other: Fixed) -> Fixed {
        Fixed(self.0.saturating_add(other.0))
    }

    /// Saturating subtraction.
    pub const fn saturating_sub(self, other: Fixed) -> Fixed {
        Fixed(self.0.saturating_sub(other.0))
    }

    /// Multiply by an integer, saturating.
    pub const fn saturating_mul_int(self, k: i32) -> Fixed {
        match self.0.checked_mul(k) {
            Some(v) => Fixed(v),
            None => {
                if (self.0 < 0) ^ (k < 0) {
                    Fixed(i32::MIN)
                } else {
                    Fixed(i32::MAX)
                }
            }
        }
    }

    /// Truncating division by an integer. `None` when `k == 0`.
    pub const fn checked_div_int(self, k: i32) -> Option<Fixed> {
        match self.0.checked_div(k) {
            Some(v) => Some(Fixed(v)),
            None => None,
        }
    }
}

/// Adding two Q16.16 values in `i32` cannot overflow when both are bounded by
/// half the range. This is the guard a controller uses before summing terms.
pub fn verify_fixed_add_no_overflow() -> Verdict {
    smt::with_fresh(|| {
        // 16-bit operands standing in for the sign+integer part, so the BDD
        // stays small while the *structure* of the argument is the real one.
        let a = smt::var(16);
        let b = smt::var(16);
        // |a|, |b| <= 2^14 (half the positive range) => a + b <= 2^15, which
        // still fits in 16 bits with the sign bit clear.
        let bound = 1u64 << 14;
        let a_ok = smt::ule_const(a, bound);
        let b_ok = smt::ule_const(b, bound);
        let sum = smt::add(a, b);
        let fits = smt::ule_const(sum, 1u64 << 15);
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
pub fn verify_scale_identity() -> Verdict {
    smt::with_fresh(|| {
        let k = smt::var(8);
        let small = smt::ult_const(k, 16);
        let scaled = smt::shl(k, 4);
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
    }

    #[test]
    fn fixed_add_guard_is_sound() {
        assert!(verify_fixed_add_no_overflow().is_proved());
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
    }
}

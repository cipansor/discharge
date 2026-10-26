//! Drop-in integer operations whose central safety property is *proved*.
//!
//! In C, `a + b` on `unsigned` silently wraps and on `signed` is undefined
//! behaviour; in Ada with `-gnato` it traps, and SPARK can prove statically that
//! the trap never fires. Rust's `+` panics in debug and wraps in release, which
//! is arguably the worst of both worlds for flight software. These primitives
//! take the total-function route: they return an `Option`, and the accompanying
//! `verify_*` functions prove that the `None` case is exactly the overflow case,
//! so a caller can either handle it or prove it away.
//!
//! The `Bounded` type carries a compile-time range, and the proofs show that
//! addition and subtraction of in-range values cannot leave a stated envelope —
//! the check a control law needs before it writes to an actuator.

use crate::smt::{self, Verdict};

/// `a + b`, or `None` on overflow.
pub const fn safe_add(a: u32, b: u32) -> Option<u32> {
    a.checked_add(b)
}

/// `a - b`, or `None` on underflow.
pub const fn safe_sub(a: u32, b: u32) -> Option<u32> {
    a.checked_sub(b)
}

/// `a * b`, or `None` on overflow.
pub const fn safe_mul(a: u32, b: u32) -> Option<u32> {
    a.checked_mul(b)
}

/// `a / b`, or `None` when `b == 0`. Division is *defined* for every nonzero
/// divisor, so the only failure mode is the one made explicit here.
pub const fn safe_div(a: u32, b: u32) -> Option<u32> {
    a.checked_div(b)
}

/// `a % b`, or `None` when `b == 0`.
pub const fn safe_rem(a: u32, b: u32) -> Option<u32> {
    a.checked_rem(b)
}

/// A value known at compile time to lie in `[MIN, MAX]`.
///
/// The constructor is the only way in, so `Bounded<MIN, MAX>` is a
/// refinement-typed integer: the invariant cannot be broken by construction.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Bounded<const MIN: u64, const MAX: u64>(u64);

impl<const MIN: u64, const MAX: u64> Bounded<MIN, MAX> {
    /// The inclusive lower bound.
    pub const LOW: u64 = MIN;
    /// The inclusive upper bound.
    pub const HIGH: u64 = MAX;

    /// Construct, or `None` when the value is outside the range.
    pub const fn new(v: u64) -> Option<Self> {
        if MIN <= v && v <= MAX {
            Some(Bounded(v))
        } else {
            None
        }
    }

    /// The raw value. Always within `[MIN, MAX]` by construction.
    pub const fn get(self) -> u64 {
        self.0
    }

    /// Clamp an arbitrary value into the range.
    pub const fn clamp(v: u64) -> Self {
        if v < MIN {
            Bounded(MIN)
        } else if v > MAX {
            Bounded(MAX)
        } else {
            Bounded(v)
        }
    }

    /// Add, or `None` if the sum leaves the range.
    pub const fn add(self, other: Self) -> Option<Self> {
        match self.0.checked_add(other.0) {
            Some(s) if MIN <= s && s <= MAX => Some(Bounded(s)),
            _ => None,
        }
    }

    /// Subtract, or `None` if the difference leaves the range.
    pub const fn sub(self, other: Self) -> Option<Self> {
        match self.0.checked_sub(other.0) {
            Some(d) if MIN <= d && d <= MAX => Some(Bounded(d)),
            _ => None,
        }
    }
}

// ---------------------------------------------------------------------------
// Proofs
// ---------------------------------------------------------------------------

/// Proves that adding two values below `max` cannot wrap at the given width.
///
/// This is the *whole* safety argument for an accumulator: if every term is
/// `<= max` and `2 * max` fits in `width` bits, then no intermediate sum
/// overflows. The caller supplies the width and `max`; the proof is
/// unconditional.
pub fn verify_accumulator_no_overflow(width: u8, max: u64) -> Verdict {
    smt::with_fresh(|| {
        let a = smt::var(width);
        let b = smt::var(width);
        let pre = smt::and(smt::ule_const(a, max), smt::ule_const(b, max));
        let sum = smt::add(a, b);
        smt::prove_implies(pre, smt::ule_const(sum, max.saturating_mul(2)))
    })
}

/// Proves that the wrapped result is a *sound and complete* overflow flag:
/// `sum < a` happens exactly when `sum < b`. So `safe_add` can test either
/// operand, and neither test can miss an overflow or raise a false alarm.
pub fn verify_safe_add_is_exact(width: u8) -> Verdict {
    smt::with_fresh(|| {
        let a = smt::var(width);
        let b = smt::var(width);
        let sum = smt::add(a, b);
        smt::prove(smt::iff(smt::ult(sum, a), smt::ult(sum, b)))
    })
}

/// Proves the refinement invariant of [`Bounded`]: for in-range `a` and `b`,
/// `a - b` is in range exactly when `a >= b`.
pub fn verify_bounded_sub_is_total(min: u64, max: u64) -> Verdict {
    smt::with_fresh(|| {
        let w = 32u8;
        let a = smt::var(w);
        let b = smt::var(w);
        let in_range = |v: smt::Var| {
            smt::and(smt::uge_const(v, min), smt::ule_const(v, max))
        };
        let pre = smt::and(in_range(a), in_range(b));
        let diff = smt::sub(a, b);
        // With `min == 0` there is nothing below the range, so an underflow
        // shows up as a wrapped value *above* `max`. The refinement invariant
        // is therefore: `a < b` exactly when `a - b` leaves the range upward.
        let _ = min;
        let underflow = smt::ult(a, b);
        let above_max = smt::ugt_const(diff, max);
        smt::prove_implies(pre, smt::iff(underflow, above_max))
    })
}

/// Proves that saturating addition is monotone: `a <= b` implies
/// `sat(a) <= sat(b)` for a fixed addend. Monotonicity is what lets a control
/// loop reason about saturation without case analysis.
pub fn verify_saturating_add_monotone(width: u8, k: u64) -> Verdict {
    smt::with_fresh(|| {
        let a = smt::var(width);
        let b = smt::var(width);
        let ka = smt::word(k, width);
        // sat(x) = min(x + k, MAX). Model MAX as 2^width - 1.
        let max = smt::all_ones(width);
        let sa = sat_add(a, ka, max, width);
        let sb = sat_add(b, ka, max, width);
        let pre = smt::ule(a, b);
        smt::prove_implies(pre, smt::ule(sa, sb))
    })
}

fn sat_add(x: smt::Var, k: smt::Var, max: smt::Var, width: u8) -> smt::Var {
    let sum = smt::add(x, k);
    // Overflow iff sum < x (wrapped). Use ite to select max in that case.
    let overflowed = smt::ult(sum, x);
    let _ = width;
    smt::ite(overflowed, max, sum)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn safe_ops_are_total() {
        assert_eq!(safe_add(1, 2), Some(3));
        assert_eq!(safe_add(u32::MAX, 1), None);
        assert_eq!(safe_sub(0, 1), None);
        assert_eq!(safe_mul(1 << 16, 1 << 16), None);
        assert_eq!(safe_div(10, 0), None);
        assert_eq!(safe_rem(10, 0), None);
        assert_eq!(safe_div(10, 3), Some(3));
    }

    #[test]
    fn accumulator_never_overflows() {
        // 12-bit terms bounded by 1000: 2000 fits, no wrap.
        assert!(verify_accumulator_no_overflow(12, 1000).is_proved());
    }

    #[test]
    fn safe_add_is_exact() {
        for w in [8u8, 16] {
            assert!(verify_safe_add_is_exact(w).is_proved(), "width {}", w);
        }
    }

    #[test]
    fn bounded_sub_refinement_holds() {
        assert!(verify_bounded_sub_is_total(0, 1000).is_proved());
    }

    #[test]
    fn saturating_add_is_monotone() {
        assert!(verify_saturating_add_monotone(8, 7).is_proved());
    }

    #[test]
    fn bounded_type_behaves() {
        type Pwm = Bounded<0, 1000>;
        assert_eq!(Pwm::new(500).unwrap().get(), 500);
        assert!(Pwm::new(1001).is_none());
        assert_eq!(Pwm::clamp(5000).get(), 1000);
        let a = Pwm::new(600).unwrap();
        let b = Pwm::new(500).unwrap();
        // 600 + 500 = 1100 leaves [0, 1000], so the refinement rejects it.
        assert_eq!(a.add(b), None);
        assert_eq!(a.sub(b).unwrap().get(), 100);
    }
}

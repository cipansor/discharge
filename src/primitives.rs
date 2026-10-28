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
///
/// Both constructors, [`new`](Self::new) and [`clamp`](Self::clamp), refuse an *empty*
/// range: when `MIN > MAX` no `u64` satisfies `MIN <= v <= MAX`, so neither can produce a
/// value. `clamp` used to return `MIN` in that case, which is outside `[LOW, HIGH]` and
/// so broke the very invariant the type exists to carry; see
/// `an_empty_bounded_range_admits_nothing` in the tests below.
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

    /// Clamp an arbitrary value into the range, or `None` when the range is empty.
    ///
    /// `MIN > MAX` is an empty range: no `u64` satisfies `MIN <= v <= MAX`, so there is
    /// no value to return. Returning `MIN` (the old behaviour) produced a `Bounded` whose
    /// `get()` is outside its own `[LOW, HIGH]`, which breaks the invariant the type
    /// exists to carry -- `Bounded<100, 10>::clamp(50)` gave `100`, and `100 <= 10` is
    /// false. [`new`](Self::new) already returns `None` for the same range, so the two
    /// constructors now agree: an empty range admits nothing.
    pub const fn clamp(v: u64) -> Option<Self> {
        if MIN > MAX {
            return None;
        }
        Some(if v < MIN {
            Bounded(MIN)
        } else if v > MAX {
            Bounded(MAX)
        } else {
            Bounded(v)
        })
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
/// `<= max`, then no intermediate sum overflows. The caller supplies the width
/// and `max`; the proof is unconditional, and it *refuses* when `max` is large
/// enough that a sum can wrap.
pub fn verify_accumulator_no_overflow(width: u8, max: u64) -> Verdict {
    smt::with_fresh(|| {
        let a = smt::var(width);
        let b = smt::var(width);
        let pre = smt::and(smt::ule_const(a, max), smt::ule_const(b, max));
        let sum = smt::add(a, b);
        // "No overflow" is exactly "the wrapped sum is not below an operand": `a + b`
        // wraps precisely when `sum < a`.
        //
        // The goal used to be `sum <= 2 * max`, which is only a sufficient condition and
        // degenerates at the one place it matters. When `2 * max` does not fit the width,
        // `ule_const` treats the bound as "every value is below it" and answers `true`, so
        // the obligation was *vacuously* proved for exactly the `max` values whose sums do
        // overflow: `verify_accumulator_no_overflow(8, 200)` came back `Valid`, though
        // 200 + 200 = 400 wraps to 144 in 8 bits. Testing the wrap directly is
        // width-independent and needs no side condition.
        smt::prove_implies(pre, smt::ule(a, sum))
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

/// Proves the refinement invariant of [`Bounded::sub`]: for in-range `a` and `b`,
/// [`Bounded::sub`] returns a value exactly when `b <= a` and `a - b >= min`.
///
/// That is the *whole* condition, and it needs all three halves. The lower bound is not
/// decoration: at `min == 10`, `a == 11` and `b == 10` are both in range and `a >= b`, yet
/// `a - b == 1` is below `min`, so [`Bounded::sub`] rejects it. An earlier version of this
/// obligation dropped `min` entirely (`let _ = min;`) and documented the claim as
/// "in range exactly when `a >= b`" -- which is false for any non-zero `min`. It was proved
/// only because the formula no longer mentioned the parameter it was given.
///
/// The underflow gate is the other half, and it went missing the same way: the goal was
/// `iff(in_range(diff), want)`, where `diff` is the *wrapping* difference. For a narrow
/// range that is harmless, because an underflow wraps to a value above `max` and
/// `in_range(diff)` is false. For a range whose `max` is near `2^32 - 1` it is false: at
/// `min == 0`, `max == u32::MAX`, `a == 0`, `b == 2^31`, the wrapped `diff` is `2^31`, which
/// is `<= max`, so `in_range(diff)` holds while `checked_sub` returned `None`. The claim was
/// then `true <=> false` and the obligation was refuted -- correctly, because the statement
/// was wrong, not because the engine failed. `checked_sub` gates on `b <= a` first, so the
/// left side must too. `result_ok` is exactly that: the value `sub` would return.
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
        // `checked_sub` yields a value only when `b <= a`; gate the left side on it, or a
        // wrapping underflow whose result happens to land in range makes the claim false.
        let no_underflow = smt::ule(b, a);
        let result_ok = smt::and(no_underflow, in_range(diff));
        // The upper bound is free: `a <= max` and `b >= min >= 0` give `a - b <= max`, so
        // the condition reduces to the lower bound once the gate holds.
        let want = smt::and(no_underflow, smt::uge_const(diff, min));
        smt::prove_implies(pre, smt::iff(result_ok, want))
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
        // And it must refuse when the bound is too large for the width: 200 + 200 = 400
        // wraps in 8 bits, so the claim is false and must not be proved. This is the case
        // the old `sum <= 2 * max` goal got wrong, by going vacuous.
        for (w, max) in [(8u8, 200u64), (8, 128), (8, 255), (16, 40000)] {
            let v = verify_accumulator_no_overflow(w, max);
            assert!(
                !v.is_proved(),
                "width {} max {} can overflow but was proved: {}",
                w,
                max,
                v
            );
            assert!(
                matches!(v, Verdict::Counterexample(_)),
                "width {} max {} should be refuted with a witness, got {}",
                w,
                max,
                v
            );
        }
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
        // A non-zero lower bound is the case the old obligation ignored: it must still be
        // proved, and now the goal actually depends on `min`.
        assert!(verify_bounded_sub_is_total(10, 100).is_proved());
        assert!(verify_bounded_sub_is_total(5, 200).is_proved());
        // The concrete instance the old doc got wrong: 11 and 10 are in [10, 100] and
        // 11 >= 10, but the difference 1 is below `min`, so `sub` must reject it.
        type R = Bounded<10, 100>;
        let a = R::new(11).unwrap();
        let b = R::new(10).unwrap();
        assert_eq!(a.sub(b), None, "1 is below min = 10");

        // The full range is the case the *underflow gate* exists for: at `min == 0` and
        // `max == u32::MAX`, an underflow wraps to a value that is still `<= max`, so a goal
        // of `iff(in_range(diff), want)` without the gate is refuted. It must now be proved.
        assert!(verify_bounded_sub_is_total(0, u32::MAX as u64).is_proved());
        assert!(verify_bounded_sub_is_total(1, u32::MAX as u64).is_proved());
        assert!(verify_bounded_sub_is_total(5, u32::MAX as u64).is_proved());

        // Teeth for the underflow gate: the same statement *without* it must be refuted at
        // the full range, so the gate cannot be dropped again. `a = 0`, `b = 2^31`: the
        // wrapped difference is `2^31 <= max`, so the ungated left side is true while
        // `checked_sub` returned `None`.
        smt::with_fresh(|| {
            let a = smt::var(32);
            let b = smt::var(32);
            let in_range = |v: smt::Var| {
                smt::and(smt::uge_const(v, 0), smt::ule_const(v, u32::MAX as u64))
            };
            let pre = smt::and(in_range(a), in_range(b));
            let diff = smt::sub(a, b);
            let ungated = smt::iff(in_range(diff), smt::ule(b, a));
            assert!(
                !smt::prove_implies(pre, ungated).is_proved(),
                "the claim without the underflow gate must be refuted at the full range"
            );
        });

        // Teeth for the `min` conjunct: state the claim without it and show it is false,
        // so the conjunct cannot be dropped again. `a = 11`, `b = 10` are in `[10, 100]`
        // and `b <= a`, but the difference is below `min`.
        let (min, max) = (10u64, 100u64);
        smt::with_fresh(|| {
            let a = smt::var(32);
            let b = smt::var(32);
            let in_range = |v: smt::Var| {
                smt::and(smt::uge_const(v, min), smt::ule_const(v, max))
            };
            let pre = smt::and(in_range(a), in_range(b));
            let diff = smt::sub(a, b);
            let without_min = smt::iff(in_range(diff), smt::ule(b, a));
            assert!(
                !smt::prove_implies(pre, without_min).is_proved(),
                "the claim without the min conjunct must be refuted"
            );
        });
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
        assert_eq!(Pwm::clamp(5000).unwrap().get(), 1000);
        assert_eq!(Pwm::clamp(0).unwrap().get(), 0);
        let a = Pwm::new(600).unwrap();
        let b = Pwm::new(500).unwrap();
        // 600 + 500 = 1100 leaves [0, 1000], so the refinement rejects it.
        assert_eq!(a.add(b), None);
        assert_eq!(a.sub(b).unwrap().get(), 100);
    }

    #[test]
    fn an_empty_bounded_range_admits_nothing() {
        // `MIN > MAX` is an empty range, and every constructor must agree that no value
        // is in it. `new` already returned `None`; `clamp` returned `MIN`, which is
        // outside `[LOW, HIGH]` -- `Bounded<100, 10>::clamp(50)` gave `100`, and
        // `100 <= 10` is false. A type whose whole purpose is to carry
        // `LOW <= get() <= HIGH` cannot have a constructor that breaks it.
        type Empty = Bounded<100, 10>;
        assert_eq!(Empty::new(50), None, "new already refuses an empty range");
        assert_eq!(Empty::clamp(50), None, "clamp must refuse it too");
        assert_eq!(Empty::clamp(0), None);
        assert_eq!(Empty::clamp(200), None);
        // The control: a real range still clamps, in both directions and in the middle.
        type Pwm = Bounded<0, 1000>;
        assert_eq!(Pwm::clamp(5000).unwrap().get(), 1000);
        assert_eq!(Pwm::clamp(500).unwrap().get(), 500);
    }
}

//! The proofs, discharged by exhaustive enumeration.
//!
//! There is no solver here. Each obligation walks **every** input in its domain
//! and answers [`Verdict::Valid`] only if the property held for all of them, or
//! [`Verdict::Counterexample`] with the first witness that falsified it. That is
//! a complete decision procedure for the domain it is given: no size wall, no
//! `Unknown` because an arena filled, no reliance on a search heuristic.
//!
//! It is deliberately *not* symbolic. Enumeration cannot reach a 32-bit
//! two-variable domain, and it does not pretend to: a domain larger than
//! [`ENUM_BUDGET`] returns [`Verdict::Unknown`], the same honest refusal the
//! parent crate's `smt` engine gives at its own wall. The obligations here are
//! therefore stated at widths the enumeration can *finish*, and the parent's
//! symbolic engine proves the same statements at the wider ones.
//!
//! # Why this is a proof and not a test
//!
//! A test that samples inputs shows the property holds for the inputs it tried.
//! An enumeration that visits every input of the domain and stops only when the
//! domain is exhausted shows it holds for *all* of them — for a domain small
//! enough to exhaust, that is a proof by cases with no gaps. The distinction is
//! the domain, not the technique, which is why the budget is explicit and the
//! answer at the budget is `Unknown` rather than `Valid`.

/// The largest number of cases one obligation will enumerate.
///
/// `2^32` is about two seconds of tight loop, and it is the point past which the
/// method stops being usable in a test suite. A domain above it is not attempted;
/// the verdict is [`Verdict::Unknown`].
pub const ENUM_BUDGET: u64 = 1 << 32;

/// The outcome of an obligation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Verdict {
    /// The property held for every input in the domain. A complete proof.
    Valid,
    /// The property failed, with a concrete input that falsifies it.
    Counterexample(Witness),
    /// The domain exceeds [`ENUM_BUDGET`], or the statement was not one this
    /// method can decide. We refuse to guess.
    Unknown,
}

impl Verdict {
    /// True only when the property was *proved*. `Unknown` is not a proof.
    pub const fn is_proved(&self) -> bool {
        matches!(self, Verdict::Valid)
    }

    /// True when the query reached a definite answer.
    pub const fn is_decided(&self) -> bool {
        !matches!(self, Verdict::Unknown)
    }
}

/// A falsifying input. `len` is how many of `a`/`b` the obligation ranged over.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Witness {
    /// The first input variable.
    pub a: u64,
    /// The second input variable, when the obligation has two.
    pub b: u64,
    /// How many variables the witness names (1 or 2).
    pub len: u8,
}

impl Witness {
    fn one(a: u64) -> Self {
        Witness { a, b: 0, len: 1 }
    }
    fn two(a: u64, b: u64) -> Self {
        Witness { a, b, len: 2 }
    }
}

// ---------------------------------------------------------------------------
// The enumeration primitives
// ---------------------------------------------------------------------------

/// Walk every pair of `w`-bit values, when `2^(2w)` fits the budget. This is the
/// general entry point for the two-variable obligations at a caller-chosen
/// width.
fn forall_pair(w: u8, p: impl Fn(u64, u64) -> bool) -> Verdict {
    if w > 16 {
        return Verdict::Unknown;
    }
    let domain = 1u64 << w;
    if domain.checked_mul(domain).map_or(true, |c| c > ENUM_BUDGET) {
        return Verdict::Unknown;
    }
    let mut a = 0u64;
    while a < domain {
        let mut b = 0u64;
        while b < domain {
            if !p(a, b) {
                return Verdict::Counterexample(Witness::two(a, b));
            }
            b += 1;
        }
        a += 1;
    }
    Verdict::Valid
}

/// Walk every `w`-bit value. Returns [`Verdict::Unknown`] past `2^ENUM_BUDGET`.
fn forall_one(w: u8, p: impl Fn(u64) -> bool) -> Verdict {
    if w > 32 {
        return Verdict::Unknown;
    }
    let domain = 1u64 << w;
    if domain > ENUM_BUDGET {
        return Verdict::Unknown;
    }
    let mut x = 0u64;
    while x < domain {
        if !p(x) {
            return Verdict::Counterexample(Witness::one(x));
        }
        x += 1;
    }
    Verdict::Valid
}

// ---------------------------------------------------------------------------
// The obligations
// ---------------------------------------------------------------------------

/// The overflow test is sound: for a wrapping 8-bit sum, "the result is below
/// `a`" and "the result is below `b`" are *the same event*. That is exactly why
/// `checked_add` can test either one, and why the wrapped result is a reliable
/// overflow flag even when the true sum is lost.
///
/// Enumerated over all `2^16` pairs of `u8`.
pub fn checked_add_is_total() -> Verdict {
    forall_pair(8, |a, b| {
        let sum = a.wrapping_add(b) & 0xFF;
        (sum < a) == (sum < b)
    })
}

/// The saturating sum never falls below an operand: `sat(a,b) >= a` and
/// `>= b`, unconditionally, including on overflow.
///
/// The property is stated about the *saturating* value, not the wrapping one.
/// The wrapping sum does not satisfy it, so the `min` is load-bearing; see
/// `saturation_is_load_bearing` in the tests.
pub fn saturating_add_bounds() -> Verdict {
    forall_pair(8, |a, b| {
        let sum = a.wrapping_add(b) & 0xFF;
        let overflowed = sum < a;
        let sat = if overflowed { 0xFF } else { sum };
        sat >= a && sat >= b
    })
}

/// `x - x == 0` at width `w`, the cancellation law for subtraction.
pub fn sub_self_is_zero(w: u8) -> Verdict {
    forall_one(w, |x| {
        let mask = if w == 64 { u64::MAX } else { (1u64 << w) - 1 };
        let x = x & mask;
        x.wrapping_sub(x) & mask == 0
    })
}

/// The algebraic laws an optimiser, a static analyser or a hand proof relies on.
/// Returns how many of the `laws x widths` were proved.
///
/// Each law is a separate obligation, and the count is returned rather than a
/// single verdict so a test can assert the exact number.
///
/// Two of the laws are identity operations -- `x | 0 == x` and `x ^ x == 0` --
/// which is the point: they are the trivial identities a peephole optimiser
/// actually folds, and enumerating them is how this module proves the fold is
/// sound. `clippy` flags them as such, correctly, so the lint is allowed here
/// with that reason rather than the laws being written to dodge it.
#[allow(clippy::identity_op, clippy::eq_op)]
pub fn algebraic_identities() -> usize {
    let mut proved = 0;
    for w in [8u8, 16] {
        let mask = (1u64 << w) - 1;
        let laws: [&dyn Fn(u64) -> bool; 10] = [
            &|x| x.wrapping_add(0) & mask == x,
            &|x| x.wrapping_mul(1) & mask == x,
            &|x| x.wrapping_mul(0) & mask == 0,
            &|x| (x | 0) & mask == x,
            &|x| (x & mask) & mask == x,
            &|x| (x ^ x) & mask == 0,
            &|x| x.wrapping_sub(x) & mask == 0,
            &|x| (x >> w) & mask == 0,
            // `x | all_ones == all_ones`. This slot previously held `0 <= x`, which for
            // an unsigned value is a tautology of the *type*, not a fact about the input
            // -- it is unchanged by substituting any term for `x`, so it added no
            // coverage while the comment claimed a law. Or-ing with the mask is a real
            // identity an optimiser folds, and it is falsifiable: `(x | 0) == mask` is
            // refuted at every `x < mask`.
            &|x| (x | mask) & mask == mask,
            &|x| x <= mask, // x <= 2^w - 1, the range law
        ];
        for law in laws {
            if forall_one(w, |x| law(x & mask)).is_proved() {
                proved += 1;
            }
        }
    }
    proved
}

/// `mul_div` widens to 64 bits precisely because a product of two `w`-bit
/// values needs `2w` bits. This proves the *shape* of that argument at a width
/// enumeration reaches: if each factor is below `2^(w/2)`, the product fits.
///
/// Enumerated over all `2^8` pairs of 4-bit values.
pub fn product_of_bounded_fits() -> Verdict {
    forall_pair(4, |a, b| {
        let pre = a < 4 && b < 4;
        let prod = a.wrapping_mul(b) & 0xF;
        !pre || prod <= 9
    })
}

/// Adding two non-negative Q16.16 values cannot overflow a signed 16-bit sum
/// when each is bounded by `2^14 - 1`. This is the guard a controller uses
/// before summing terms.
///
/// The bound is `2^14 - 1`, not `2^14`: a signed 16-bit value tops out at
/// `2^15 - 1`, and at the inclusive bound `2^14` the sum `2^14 + 2^14` is exactly
/// `2^15`, which sets the sign bit and reads as `-32768`.
///
/// Enumerated over all `2^32` pairs of 16-bit values — the one obligation here
/// that runs at the full budget.
pub fn fixed_add_no_overflow() -> Verdict {
    let bound = (1u64 << 14) - 1;
    forall_pair(16, |a, b| {
        let pre = a <= bound && b <= bound;
        let sum = (a + b) & 0xFFFF;
        !pre || sum < (1u64 << 15)
    })
}

/// `to_int(from_int(k)) == k`: the integer round-trip is lossless, for the `k`
/// the Q16.16 range can hold.
pub fn fixed_roundtrip() -> Verdict {
    forall_one(8, |k| {
        // from_int(k) = k << 16, to_int truncates back. At 8 bits we model the
        // shift/truncate pair by proving (k << 4) >> 4 == k for k < 16.
        let small = k < 16;
        let shifted = (k << 4) & 0xFF;
        let back = shifted >> 4;
        !small || back == k
    })
}

/// `k * SCALE / SCALE == k`, the fixed-point identity behind unit conversion.
///
/// Unlike [`fixed_roundtrip`], this performs a real multiply by the scale factor
/// and *then* divides by shifting. That distinction is the whole content: the
/// multiply is what makes the statement be about unit conversion rather than a
/// renamed round-trip.
pub fn scale_identity() -> Verdict {
    forall_one(8, |k| {
        let small = k < 16;
        let scaled = (k * 16) & 0xFF;
        let unscaled = scaled >> 4;
        !small || unscaled == k
    })
}

/// If every term of an accumulator is `<= max`, no intermediate sum wraps.
///
/// "No overflow" is exactly "the wrapped sum is not below an operand", which is
/// width-independent and needs no side condition. The naive goal `sum <= 2*max`
/// degenerates when `2*max` does not fit the width, and was vacuously proved for
/// exactly the `max` values whose sums overflow.
///
/// Enumerated over `2^24` pairs of 12-bit values.
pub fn accumulator_no_overflow(w: u8, max: u64) -> Verdict {
    forall_pair(w, move |a, b| {
        let pre = a <= max && b <= max;
        let mask = if w == 64 { u64::MAX } else { (1u64 << w) - 1 };
        let sum = a.wrapping_add(b) & mask;
        !pre || sum >= a
    })
}

/// The wrapped result is a sound and complete overflow flag: `sum < a` happens
/// exactly when `sum < b`. So `safe_add` can test either operand, and neither
/// test can miss an overflow or raise a false alarm.
pub fn safe_add_is_exact(w: u8) -> Verdict {
    forall_pair(w, |a, b| {
        let mask = if w == 64 { u64::MAX } else { (1u64 << w) - 1 };
        let sum = a.wrapping_add(b) & mask;
        (sum < a) == (sum < b)
    })
}

/// The refinement invariant of `Bounded::sub`: for in-range `a` and `b`, `sub`
/// returns a value exactly when `b <= a` **and** `a - b >= min`.
///
/// All three halves matter. The lower bound is not decoration: at `min == 10`,
/// `a == 11` and `b == 10` are in range and `a >= b`, yet the difference `1` is
/// below `min`. The underflow gate is the other half: without it, a wrapping
/// difference can land back in range and be accepted.
///
/// Enumerated over an 8-bit domain, which is the range the guard is stated for.
pub fn bounded_sub_is_total(min: u64, max: u64) -> Verdict {
    forall_pair(8, move |a, b| {
        let in_range = |v: u64| v >= min && v <= max;
        let pre = in_range(a) && in_range(b);
        // What `checked_sub` would do, and what `sub` accepts.
        let no_underflow = b <= a;
        let diff = a.wrapping_sub(b);
        let result_ok = no_underflow && in_range(diff);
        let want = no_underflow && diff >= min;
        !pre || result_ok == want
    })
}

/// Saturating addition is monotone: `a <= b` implies `sat(a, k) <= sat(b, k)`
/// for a fixed addend. Monotonicity is what lets a control loop reason about
/// saturation without a case split.
pub fn saturating_add_monotone(w: u8, k: u64) -> Verdict {
    forall_pair(w, move |a, b| {
        let mask = if w == 64 { u64::MAX } else { (1u64 << w) - 1 };
        let max = mask;
        let sat = |x: u64| {
            let sum = x.wrapping_add(k) & mask;
            if sum < x { max } else { sum }
        };
        let pre = a <= b;
        !pre || sat(a) <= sat(b)
    })
}

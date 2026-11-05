//! Q16.16 fixed point.
//!
//! The workhorse representation in flight control and motor control:
//! deterministic, no floating point, no soft-float dependency. The properties
//! that make it safe to add and to scale are proved in [`crate::prove`].

/// A Q16.16 fixed-point number: 16 integer bits, 16 fractional bits.
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
    /// The range of Q16.16 in `i32` is `[-32768, 32767]` integers, so `v << 16`
    /// silently wraps for `|v| >= 32768`: `from_int(32768)` used to give
    /// `-32768`. A shift is a total function, which is exactly why the wrap is
    /// invisible. Saturating keeps this module's promise that no primitive
    /// overflows without saying so.
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
    /// Truncation toward zero is not `self.0 >> 16` for negative values: an
    /// arithmetic shift is a floor, so `-0.5 >> 16` gives `-1`, not `0`. That
    /// one-bit bias on every negative fractional input is the kind of error a
    /// control law cannot see. The magnitude is truncated and the sign restored,
    /// which is `as i32` behaviour.
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

    /// Truncating division by an integer. `None` when `k == 0`, and also when
    /// the quotient is not representable -- the single overflowing case,
    /// `i32::MIN / -1`, whose true result `2^31` is one past `i32::MAX`.
    /// `checked_div` reports both, so this returns `None` for either rather than
    /// wrapping to `i32::MIN`.
    pub const fn checked_div_int(self, k: i32) -> Option<Fixed> {
        match self.0.checked_div(k) {
            Some(v) => Some(Fixed(v)),
            None => None,
        }
    }
}

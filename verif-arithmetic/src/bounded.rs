//! Drop-in integer operations, and a refinement-typed integer.
//!
//! The `safe_*` functions are the total-function route to overflow: each returns
//! an `Option`, and [`crate::prove`] carries the proof that the `None` case is
//! exactly the overflow case.
//!
//! [`Bounded`] is the type-level route: a value known at compile time to lie in
//! `[MIN, MAX]`. The constructors are the only way in, so the invariant cannot
//! be broken by construction, and [`crate::prove::bounded_sub_is_total`] proves
//! that [`Bounded::sub`] accepts exactly the in-range cases.

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
/// Both constructors, [`new`](Self::new) and [`clamp`](Self::clamp), refuse an
/// *empty* range: when `MIN > MAX` no `u64` satisfies `MIN <= v <= MAX`, so
/// neither can produce a value. `clamp` used to return `MIN` in that case, which
/// is outside `[LOW, HIGH]` and so broke the very invariant the type exists to
/// carry.
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
    /// `MIN > MAX` is an empty range: no `u64` satisfies `MIN <= v <= MAX`, so
    /// there is no value to return. Returning `MIN` (the old behaviour) produced
    /// a `Bounded` whose `get()` is outside its own `[LOW, HIGH]`, which breaks
    /// the invariant the type exists to carry -- `Bounded<100, 10>::clamp(50)`
    /// gave `100`, and `100 <= 10` is false. [`new`](Self::new) already returns
    /// `None` for the same range, so the two constructors agree: an empty range
    /// admits nothing.
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
    ///
    /// Accepts exactly when `other <= self` **and** the difference is still
    /// `>= MIN`. Both halves matter: at `MIN == 10`, `self == 11` and
    /// `other == 10` are in range and `other <= self`, yet the difference `1` is
    /// below `MIN`, so this returns `None`. The underflow gate is the other
    /// half -- without it a wrapping difference can land back in range and be
    /// accepted. [`crate::prove::bounded_sub_is_total`] is the obligation that
    /// proves this is exactly the condition.
    pub const fn sub(self, other: Self) -> Option<Self> {
        match self.0.checked_sub(other.0) {
            Some(d) if MIN <= d && d <= MAX => Some(Bounded(d)),
            _ => None,
        }
    }
}

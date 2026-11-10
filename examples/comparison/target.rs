//! The shared example for the README comparison: three ordinary Rust
//! functions, the same three written for every tool in the table, so the
//! comparison is about the tools and not about three different problems.
//!
//! These functions are the ones named in `examples/comparison/README.md`.
//!
//! The contracts state the *whole* function, not only a bound. `sat_add` says
//! the result is the sum when the sum fits and `u16::MAX` when it does not;
//! a contract that only said `ret >= a && ret >= b` would be satisfied by
//! `u16::MAX` for every input, which is not a saturating add. `clamp` says
//! which arm is taken, so `lo` for every input does not pass either.

/// Saturating add: the sum when it fits, `u16::MAX` when it does not.
/// requires: true
/// ensures: ret >= a
/// ensures: ret >= b
/// ensures: a <= 65535u16 - b || ret == 65535u16
/// ensures: a > 65535u16 - b || ret == a + b
pub fn sat_add(a: u16, b: u16) -> u16 {
    if a > u16::MAX - b {
        u16::MAX
    } else {
        a + b
    }
}

/// A clamp: the result is `lo` below the range, `hi` above it, and `x` inside.
/// requires: lo <= hi
/// ensures: !(x < lo) || ret == lo
/// ensures: !(lo <= x && x > hi) || ret == hi
/// ensures: !(lo <= x && x <= hi) || ret == x
pub fn clamp(x: u16, lo: u16, hi: u16) -> u16 {
    if x < lo {
        lo
    } else if x > hi {
        hi
    } else {
        x
    }
}

/// A counted loop. Deciding it needs an induction hypothesis, not unwinding to
/// a fixed depth.
/// requires: n <= 8
/// invariant: i <= n && s == i
/// ensures: ret == n
pub fn sum_to(n: u8) -> u8 {
    let mut s = 0u8;
    let mut i = 0u8;
    while i < n {
        s += 1;
        i += 1;
    }
    s
}

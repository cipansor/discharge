//! The shared example for the README comparison: three ordinary Rust
//! functions, the same three written for every tool in the table, so the
//! comparison is about the tools and not about three different problems.
//!
//! These functions are the ones named in `examples/comparison/README.md`.

/// Saturating add, written with a guard so the `+` cannot overflow.
/// requires: true
/// ensures: ret >= a
/// ensures: ret >= b
pub fn sat_add(a: u16, b: u16) -> u16 {
    if a > u16::MAX - b {
        u16::MAX
    } else {
        a + b
    }
}

/// A clamp: the result lies in `[lo, hi]`, and the proof covers all three
/// branches rather than the one the test happened to run.
/// requires: lo <= hi
/// ensures: lo <= ret
/// ensures: ret <= hi
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

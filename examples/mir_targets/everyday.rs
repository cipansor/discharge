//! Independent probe corpus: ordinary Rust, not shaped for the verifier.
//!
//! Written by an external reviewer (see the PR #8 review, appendix), not by the
//! process that writes the verifier, so it is the honest answer to "how much
//! ordinary Rust can this tool decide?". The contracts are deliberately true, so
//! every `incomplete` is a *coverage* gap, not a wrong contract.
//!
//! The score is tracked in `ROADMAP.md` (Phase 1's exit criterion is defined on
//! this file). Do not edit a function to make it decide: add a new one and leave
//! the old one as the record. Regenerate the score with:
//!
//! ```text
//! cargo run --features std --example mir_coverage -- examples/mir_targets/everyday.rs
//! ```
#![allow(dead_code)]

/// Slice indexing guarded by the caller.
/// requires: i < v.len()
/// ensures: true
pub fn get_at(v: &[u8], i: usize) -> u8 {
    v[i]
}

/// Iterator sum, may overflow.
/// requires: true
/// ensures: true
pub fn sum_iter(v: &[u32]) -> u32 {
    v.iter().sum()
}

/// Checked add with fallback.
/// requires: true
/// ensures: ret >= a
pub fn checked_or_max(a: u32, b: u32) -> u32 {
    a.checked_add(b).unwrap_or(u32::MAX)
}

/// min/max on integers.
/// requires: lo <= hi
/// ensures: lo <= ret
/// ensures: ret <= hi
pub fn clamp_std(x: u32, lo: u32, hi: u32) -> u32 {
    x.max(lo).min(hi)
}

/// Built-in clamp.
/// requires: lo <= hi
/// ensures: lo <= ret
/// ensures: ret <= hi
pub fn clamp_builtin(x: u32, lo: u32, hi: u32) -> u32 {
    x.clamp(lo, hi)
}

/// Average without overflow.
/// requires: true
/// ensures: ret >= a || ret >= b
pub fn midpoint(a: u32, b: u32) -> u32 {
    a / 2 + b / 2 + (a % 2 + b % 2) / 2
}

/// Counted loop with a range.
/// requires: n <= 100
/// ensures: ret <= 5050
pub fn tri(n: u32) -> u32 {
    let mut s = 0;
    for i in 0..=n {
        s += i;
    }
    s
}

/// Option match.
/// requires: true
/// ensures: true
pub fn or_zero(x: Option<u8>) -> u8 {
    match x {
        Some(v) => v,
        None => 0,
    }
}

/// Guarded unwrap on a checked division.
/// requires: d != 0
/// ensures: ret <= n
pub fn div_unwrap(n: u32, d: u32) -> u32 {
    n.checked_div(d).unwrap()
}

/// Enum state machine.
#[derive(Clone, Copy)]
pub enum Mode {
    Idle,
    Run(u8),
    Fault,
}

/// requires: true
/// ensures: true
pub fn next_mode(m: Mode) -> Mode {
    match m {
        Mode::Idle => Mode::Run(0),
        Mode::Run(n) if n < 10 => Mode::Run(n + 1),
        Mode::Run(_) => Mode::Idle,
        Mode::Fault => Mode::Fault,
    }
}

/// Struct method with &mut self.
pub struct Counter {
    pub n: u16,
}

impl Counter {
    /// requires: self.n < 1000
    /// ensures: true
    pub fn bump(&mut self) {
        self.n += 1;
    }
}

/// Generic function.
/// requires: true
/// ensures: true
pub fn first_or<T: Copy>(v: &[T], d: T) -> T {
    if v.is_empty() { d } else { v[0] }
}

/// Byte parsing.
/// requires: true
/// ensures: ret <= 9
pub fn digit(b: u8) -> u8 {
    if b.is_ascii_digit() { b - b'0' } else { 0 }
}

/// Fixed array loop.
/// requires: true
/// ensures: true
pub fn max_of(a: [u8; 4]) -> u8 {
    let mut m = 0;
    let mut i = 0;
    while i < 4 {
        if a[i] > m {
            m = a[i];
        }
        i += 1;
    }
    m
}

/// assert! with formatted message (PR #8 path).
/// requires: x < 200
/// ensures: ret == x + 1
pub fn inc_checked(x: u8) -> u8 {
    assert!(x < 200, "x too big: {}", x);
    x + 1
}

/// Signed arithmetic.
/// requires: x > -100 && x < 100
/// ensures: ret >= 0
pub fn abs_small(x: i32) -> i32 {
    x.abs()
}

/// Bit manipulation.
/// requires: true
/// ensures: ret <= 255
pub fn low_byte(x: u32) -> u32 {
    x & 0xff
}

/// Saturating ops from core.
/// requires: true
/// ensures: ret >= a
pub fn sat(a: u16, b: u16) -> u16 {
    a.saturating_add(b)
}

/// Vec usage (allocation).
/// requires: true
/// ensures: true
pub fn make(n: u8) -> usize {
    let mut v = Vec::new();
    v.push(n);
    v.len()
}

/// Wrapping mul.
/// requires: true
/// ensures: true
pub fn hash_step(h: u32, b: u8) -> u32 {
    h.wrapping_mul(31).wrapping_add(b as u32)
}

/// Division by constant.
/// requires: true
/// ensures: ret <= 25
pub fn pct(x: u8) -> u8 {
    x / 10
}

//! Functions under verification, with no `discharge` import at all.
//!
//! This file is ordinary Rust. It does not depend on the verifier, which is the
//! point: the code being checked and the tool doing the checking are separate
//! artifacts, and the tool reads this file's MIR rather than being linked into
//! it. It sits in a subdirectory so `cargo` does not build it as an example; the
//! demo and the test suite hand its path to the frontend instead.
//!
//! Contracts are doc comments (`requires:` / `ensures:`). See
//! `discharge::mir::spec` for why they are not attributes.

// This file is a *verification target*, not library code. The test suite compiles
// it so that counterexamples can be replayed against the real functions, which is
// why it allows lints that would otherwise push it toward shapes the verifier
// exists to check: rewriting `a - b` as `saturating_sub` would delete the very
// overflow the guard is there to prevent, and "unused function" is the normal
// state when the verifier rather than the program is the caller.
#![allow(dead_code, clippy::implicit_saturating_sub, clippy::manual_checked_ops)]

// ---------------------------------------------------------------------------
// Must verify: the guard and the arithmetic agree.
// ---------------------------------------------------------------------------

/// A clamp. The proof has to cover all three branches.
/// requires: lo <= hi
/// ensures: lo <= ret
/// ensures: ret <= hi
pub fn clamp(x: u32, lo: u32, hi: u32) -> u32 {
    if x < lo {
        lo
    } else if x > hi {
        hi
    } else {
        x
    }
}

/// A rate limiter: the command may not move more than 50 per tick, in either
/// direction.
/// requires: true
/// ensures: ret <= target
pub fn rate_limit(current: u32, target: u32) -> u32 {
    if target > current {
        let step = target - current;
        if step > 50 {
            current + 50
        } else {
            target
        }
    } else {
        target
    }
}

/// A saturating add written with a guard, so the `+` cannot overflow.
/// requires: true
/// ensures: ret >= a
pub fn sat_add(a: u16, b: u16) -> u16 {
    if a > u16::MAX - b {
        u16::MAX
    } else {
        a + b
    }
}

/// A saturating multiply, guarded the same way. This is the case the engine has
/// to work hardest for: the guard is a statement about a product.
/// requires: true
pub fn sat_mul(a: u16, b: u16) -> u16 {
    if b != 0 && a > u16::MAX / b {
        u16::MAX
    } else {
        a * b
    }
}

/// A guarded subtraction. `a - b` panics on underflow, so the guard is load
/// bearing.
/// requires: true
pub fn sat_sub(a: u16, b: u16) -> u16 {
    if b > a {
        0
    } else {
        a - b
    }
}

/// A *variable* shift with no guard of its own. rustc emits `assert(n < 16)`
/// before the shift, so `n == 16` is a real panic and must be reported; the
/// barrel shifter models the shift itself. This is the case that shows the
/// amount is now *modelled* rather than refused, while the panic is still found.
/// requires: true
pub fn shift_left(x: u16, n: u16) -> u16 {
    x << n
}

/// A shift by a constant. No guard is needed because the amount is in range, so
/// this proves on the cheap `Op::Shl` path.
/// requires: true
pub fn shift_const(x: u16) -> u16 {
    x << 3
}

/// A saturating variable shift, guarded the way real code guards one.
/// requires: true
pub fn sat_shift(x: u16, n: u16) -> u16 {
    if n >= 16 {
        0
    } else {
        x << n
    }
}

// ---------------------------------------------------------------------------
// Must fail: these are the bugs the frontend exists to find.
// ---------------------------------------------------------------------------

/// Plain `a + b` on `u16` with no guard. rustc emits `AddWithOverflow` and an
/// assert, so there is a reachable overflow and it must be reported.
/// requires: true
pub fn unchecked_add(a: u16, b: u16) -> u16 {
    a + b
}

/// The guard is off by one: `a <= MAX - b` admits the case where the sum is
/// exactly `MAX`, which is legal, and the overflow is still prevented. So this
/// function is panic-free — but its `ensures` is wrong, and that is the bug the
/// postcondition check has to catch.
/// requires: true
/// ensures: ret >= a
pub fn off_by_one_guard(a: u16, b: u16) -> u16 {
    if a <= u16::MAX - b {
        a + b
    } else {
        0
    }
}

/// Subtraction without a guard. Underflow is a real panic here.
/// requires: true
pub fn unchecked_sub(a: u16, b: u16) -> u16 {
    a - b
}

/// A divide with no zero check. rustc inserts the division-by-zero assert.
/// requires: true
pub fn unchecked_div(n: u32, d: u32) -> u32 {
    n / d
}

/// Multiplication without a guard, which overflows.
/// requires: true
pub fn unchecked_mul(a: u8, b: u8) -> u8 {
    a * b
}

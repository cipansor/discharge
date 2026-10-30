//! Total integer arithmetic: the operations that *cannot* overflow.
//!
//! Every function here returns an `Option`, and `None` is exactly the case the
//! machine's `+`/`-`/`*` would have wrapped (or, in debug, panicked). [`crate::prove`]
//! carries the proof that the flag is exact rather than a heuristic.

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
///
/// The naive `a * b / d` is wrong for exactly the PID-shaped inputs it is used
/// on: at `a = b = 1000` the product `10^6` is fine, but at `a = b = 100_000`
/// the product `10^10` wraps a `u32` before the division can bring it back. The
/// widening is the whole point of the function, and `prove::mul_div_is_exact`
/// is the obligation that says the widened result is the true quotient.
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

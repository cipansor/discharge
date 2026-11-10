//! The third bug: `clamp` returns `hi` when the input is below the range, so
//! the contract's first disjunct is false. Included so the clamp contract is
//! shown to have teeth too, not only `sat_add`'s.

/// requires: lo <= hi
/// ensures: !(x < lo) || ret == lo
/// ensures: !(lo <= x && x > hi) || ret == hi
/// ensures: !(lo <= x && x <= hi) || ret == x
pub fn clamp(x: u16, lo: u16, hi: u16) -> u16 {
    if x < lo {
        hi
    } else if x > hi {
        hi
    } else {
        x
    }
}

//! The bug used to show that `discharge` refuses a false claim, rather than
//! only agreeing with true ones. The two branches of `sat_add` are swapped, so
//! the guarded `+` is exactly the one that can overflow.

/// requires: true
/// ensures: ret >= a
/// ensures: ret >= b
pub fn sat_add(a: u16, b: u16) -> u16 {
    if a > u16::MAX - b {
        a + b
    } else {
        u16::MAX
    }
}

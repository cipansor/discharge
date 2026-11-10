//! The bug used to show that `discharge` refuses a false claim, rather than
//! only agreeing with true ones. The two branches of `sat_add` are swapped, so
//! the guarded `+` is exactly the one that can overflow. The contract is the
//! full one from `../target.rs`, so the rejection is of the same claim the
//! correct function discharges.

/// requires: true
/// ensures: ret >= a
/// ensures: ret >= b
/// ensures: a <= 65535u16 - b || ret == 65535u16
/// ensures: a > 65535u16 - b || ret == a + b
pub fn sat_add(a: u16, b: u16) -> u16 {
    if a > u16::MAX - b {
        a + b
    } else {
        u16::MAX
    }
}

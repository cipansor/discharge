//! The second bug: the loop body is wrong, so the invariant is not preserved.
//! This is the one an unwinding depth cannot catch for every `n`.

/// requires: n <= 8
/// invariant: i <= n && s == i
/// ensures: ret == n
pub fn sum_to(n: u8) -> u8 {
    let mut s = 0u8;
    let mut i = 0u8;
    while i < n {
        s += 2;
        i += 1;
    }
    s
}

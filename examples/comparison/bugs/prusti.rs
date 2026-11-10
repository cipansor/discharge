// The bugs as Prusti functions: the swapped-branch `sat_add`, the wrong-arm
// `clamp`, and the wrong-body `sum_to`. The claims are the full ones from
// `../prusti.rs`, so each rejection is of the same claim the correct function
// discharges. `body_invariant!` is the loop form in Prusti 0.2.2 (the
// `#[invariant]` attribute is not supported there).
use prusti_contracts::*;

#[requires(true)]
#[ensures(result >= a && result >= b)]
#[ensures(a <= u16::MAX - b ==> result == a + b)]
#[ensures(a > u16::MAX - b ==> result == u16::MAX)]
pub fn sat_add(a: u16, b: u16) -> u16 {
    if a > u16::MAX - b { a + b } else { u16::MAX }
}

#[requires(lo <= hi)]
#[ensures(lo <= result && result <= hi)]
#[ensures(x < lo ==> result == lo)]
#[ensures(lo <= x && x > hi ==> result == hi)]
#[ensures(lo <= x && x <= hi ==> result == x)]
pub fn clamp(x: u16, lo: u16, hi: u16) -> u16 {
    if x < lo { hi } else if x > hi { hi } else { x }
}

#[requires(n <= 8)]
#[ensures(result == n)]
pub fn sum_to(n: u8) -> u8 {
    let mut s = 0u8;
    let mut i = 0u8;
    while i < n {
        body_invariant!(i <= n && s == i);
        s += 2;
        i += 1;
    }
    s
}

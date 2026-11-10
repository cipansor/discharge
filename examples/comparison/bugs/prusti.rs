// The two bugs as Prusti functions. `body_invariant!` is the loop form in
// Prusti 0.2.2 (the `#[invariant]` attribute is not supported there).
use prusti_contracts::*;

#[requires(true)]
#[ensures(result >= a && result >= b)]
pub fn sat_add(a: u16, b: u16) -> u16 {
    if a > u16::MAX - b { a + b } else { u16::MAX }
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

use prusti_contracts::*;

#[requires(true)]
#[ensures(result >= a && result >= b)]
pub fn sat_add(a: u16, b: u16) -> u16 {
    if a > u16::MAX - b { u16::MAX } else { a + b }
}

#[requires(lo <= hi)]
#[ensures(lo <= result && result <= hi)]
pub fn clamp(x: u16, lo: u16, hi: u16) -> u16 {
    if x < lo { lo } else if x > hi { hi } else { x }
}

#[requires(n <= 8)]
#[ensures(result == n)]
pub fn sum_to(n: u8) -> u8 {
    let mut s = 0u8;
    let mut i = 0u8;
    while i < n {
        body_invariant!(i <= n && s == i);
        s += 1;
        i += 1;
    }
    s
}

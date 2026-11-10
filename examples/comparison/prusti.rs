use prusti_contracts::*;

// The whole function, not only a bound: the sum when it fits, MAX when it does
// not. `always return u16::MAX` satisfies the bounds and fails here.
#[requires(true)]
#[ensures(result >= a && result >= b)]
#[ensures(a <= u16::MAX - b ==> result == a + b)]
#[ensures(a > u16::MAX - b ==> result == u16::MAX)]
pub fn sat_add(a: u16, b: u16) -> u16 {
    if a > u16::MAX - b { u16::MAX } else { a + b }
}

// Which arm is taken, so `always return lo` fails.
#[requires(lo <= hi)]
#[ensures(lo <= result && result <= hi)]
#[ensures(x < lo ==> result == lo)]
#[ensures(lo <= x && x > hi ==> result == hi)]
#[ensures(lo <= x && x <= hi ==> result == x)]
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

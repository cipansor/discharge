use vstd::prelude::*;

verus! {

pub fn sat_add(a: u16, b: u16) -> (r: u16)
    ensures r >= a, r >= b,
{
    if a > u16::MAX - b {
        u16::MAX
    } else {
        a + b
    }
}

pub fn clamp(x: u16, lo: u16, hi: u16) -> (r: u16)
    requires lo <= hi,
    ensures lo <= r <= hi,
{
    if x < lo { lo } else if x > hi { hi } else { x }
}

pub fn sum_to(n: u8) -> (r: u8)
    requires n <= 8,
    ensures r == n,
{
    let mut s: u8 = 0;
    let mut i: u8 = 0;
    while i < n
        invariant i <= n, s == i,
        decreases n - i,
    {
        s = s + 1;
        i = i + 1;
    }
    s
}

} // verus!

fn main() {}

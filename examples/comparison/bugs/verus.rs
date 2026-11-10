// The bugs as Verus functions: the swapped-branch `sat_add`, the wrong-arm
// `clamp`, and the wrong-body `sum_to`. The claims are the full ones from
// `../verus.rs`, so each rejection is of the same claim the correct function
// discharges. `decreases` is required on the loop.
use vstd::prelude::*;

verus! {

pub fn sat_add(a: u16, b: u16) -> (r: u16)
    requires true,
    ensures
        r >= a, r >= b,
        a <= u16::MAX - b ==> r == a + b,
        a >  u16::MAX - b ==> r == u16::MAX,
{
    if a > u16::MAX - b { a + b } else { u16::MAX }
}

pub fn clamp(x: u16, lo: u16, hi: u16) -> (r: u16)
    requires lo <= hi,
    ensures
        lo <= r <= hi,
        x < lo ==> r == lo,
        lo <= x && x > hi ==> r == hi,
        lo <= x && x <= hi ==> r == x,
{
    if x < lo { hi } else if x > hi { hi } else { x }
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
        s = s + 2;
        i = i + 1;
    }
    s
}

} // verus!

fn main() {}

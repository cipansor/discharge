// The two bugs as Verus functions. `decreases` is required on the loop.
use vstd::prelude::*;

verus! {

pub fn sat_add(a: u16, b: u16) -> (r: u16)
    requires true,
    ensures r >= a, r >= b,
{
    if a > u16::MAX - b { a + b } else { u16::MAX }
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

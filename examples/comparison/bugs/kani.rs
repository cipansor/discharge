// The bugs as Kani harnesses: the swapped-branch `sat_add`, the wrong-body
// `sum_to`, and the wrong-arm `clamp`. The claims are the full ones from
// `../kani.rs`, so each rejection is of the same claim the correct function
// discharges.
pub fn sat_add(a: u16, b: u16) -> u16 {
    if a > u16::MAX - b { a + b } else { u16::MAX }
}
pub fn clamp(x: u16, lo: u16, hi: u16) -> u16 {
    if x < lo { hi } else if x > hi { hi } else { x }
}
pub fn sum_to(n: u8) -> u8 {
    let mut s = 0u8; let mut i = 0u8;
    while i < n { s += 2; i += 1; }
    s
}
#[cfg(kani)]
mod proofs {
    use super::*;
    #[kani::proof]
    fn verify_sat_add() {
        let a: u16 = kani::any();
        let b: u16 = kani::any();
        let r = sat_add(a, b);
        kani::assert(r >= a && r >= b, "sat_add result >= both inputs");
        if a <= u16::MAX - b {
            kani::assert(r == a + b, "sat_add returns the sum when it fits");
        } else {
            kani::assert(r == u16::MAX, "sat_add saturates when it does not");
        }
    }
    #[kani::proof]
    fn verify_clamp() {
        let x: u16 = kani::any();
        let lo: u16 = kani::any();
        let hi: u16 = kani::any();
        kani::assume(lo <= hi);
        let r = clamp(x, lo, hi);
        kani::assert(lo <= r && r <= hi, "clamp in range");
        if x < lo {
            kani::assert(r == lo, "below the range returns lo");
        } else if x > hi {
            kani::assert(r == hi, "above the range returns hi");
        } else {
            kani::assert(r == x, "inside the range returns x");
        }
    }
    #[kani::proof]
    #[kani::unwind(10)]
    fn verify_sum_to() {
        let n: u8 = kani::any();
        kani::assume(n <= 8);
        let r = sum_to(n);
        kani::assert(r == n, "sum_to == n");
    }
}

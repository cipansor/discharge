// The two bugs as Kani harnesses.
pub fn sat_add(a: u16, b: u16) -> u16 {
    if a > u16::MAX - b { a + b } else { u16::MAX }
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

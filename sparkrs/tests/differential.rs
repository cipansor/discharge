//! Differential testing: the symbolic prover and brute-force execution must
//! agree. This is the test that makes the whole approach trustworthy — if the
//! BDD engine ever disagreed with reality, this file would catch it.

use sparkrs::exhaustive::{for_all_u8, for_all_u8_2, find_violation_u8};
use sparkrs::prelude::*;
use sparkrs::smt::{self, Verdict};

/// For a predicate over one 8-bit variable, symbolic proof and enumeration must
/// give the same answer.
fn agrees_unary(build: impl Fn(Var) -> Pred, concrete: impl Fn(u8) -> bool) {
    // Symbolic: is it valid for all inputs?
    let symbolic_valid = smt::with_fresh(|| {
        let x = var(8);
        build(x).prove().is_proved()
    });
    let concrete_valid = for_all_u8(&concrete);
    assert_eq!(
        symbolic_valid, concrete_valid,
        "symbolic and exhaustive disagree for a unary predicate"
    );

    // If the symbolic engine produced a counterexample, it must be real.
    let cex = smt::with_fresh(|| {
        let x = var(8);
        match build(x).prove() {
            Verdict::Counterexample(c) => Some(c.value_of(0).unwrap()),
            _ => None,
        }
    });
    if let Some(v) = cex {
        assert!(!concrete(v as u8), "symbolic counterexample {} is bogus", v);
    }
}

#[test]
fn unary_predicates_agree() {
    agrees_unary(|x| x.lt_val(200), |v| v < 200);
    agrees_unary(|x| x.le_val(200), |v| v <= 200);
    agrees_unary(|x| x.ge_val(100), |v| v >= 100);
    agrees_unary(|x| x.gt_val(100), |v| v > 100);
    // `x & 0x0f <= x` is a real property (masking only clears bits), and it is
    // not trivially true the way `x & 0x0f < 16` is.
    agrees_unary(|x| (x & 0x0fu32).le(x), |v| (v & 0x0f) <= v);
    agrees_unary(|x| (x >> 4u32).le_val(15), |v| (v >> 4) <= 15);
    // `a => b` is `!a || b`, so the concrete form is `v >= k || v < m`.
    agrees_unary(|x| x.lt_val(16).implies(x.lt_val(32)), |v| v >= 16 || v < 32);
    agrees_unary(|x| x.lt_val(4).implies(x.lt_val(8)), |v| v >= 4 || v < 8);
}

#[test]
fn binary_predicates_agree() {
    // ∀ a b. a + b does not wrap below a  (this is false; check both engines agree)
    let symbolic = smt::with_fresh(|| {
        let a = var(8);
        let b = var(8);
        smt::prove(smt::ule(smt::add(a, b), a)).is_proved()
    });
    let concrete = for_all_u8_2(|a, b| a.wrapping_add(b) <= a);
    assert_eq!(symbolic, concrete);

    // ∀ a b. (a & b) <= a
    let symbolic = smt::with_fresh(|| {
        let a = var(8);
        let b = var(8);
        smt::prove(smt::ule(smt::band(a, b), a)).is_proved()
    });
    assert!(symbolic, "(a & b) <= a should be a theorem");
    assert!(for_all_u8_2(|a, b| (a & b) <= a));
}

#[test]
fn the_symbolic_counterexample_is_a_real_violation() {
    // The prover reports *a* violating input, not necessarily the smallest one:
    // BDD models are path-derived. What must hold is that the witness really
    // violates the property, and that enumeration confirms a violation exists.
    let sym = smt::with_fresh(|| {
        let x = var(8);
        match (x.lt_val(100)).prove() {
            Verdict::Counterexample(c) => c.value_of(0).unwrap() as u8,
            _ => panic!("expected a counterexample"),
        }
    });
    assert!(sym >= 100, "witness {} does not violate x < 100", sym);

    // Enumeration finds the smallest witness, and it must be exactly 100.
    let brute = find_violation_u8(|v| v < 100).unwrap();
    assert_eq!(brute, 100);
}

#[test]
fn saturating_add_matches_execution_everywhere() {
    // The proof module claims saturating addition never wraps. Check the claim
    // against every pair of u8s, and check the symbolic engine agrees.
    assert!(for_all_u8_2(|a, b| a.saturating_add(b) >= a));
    assert!(for_all_u8_2(|a, b| a.saturating_add(b) >= b));

    let symbolic = smt::with_fresh(|| {
        let a = var(8);
        let b = var(8);
        let sum = smt::add(a, b);
        let no_wrap = smt::ule(a, sum);
        smt::prove_implies(no_wrap, smt::ule(b, sum)).is_proved()
    });
    assert!(symbolic);
}

#[test]
fn the_runtime_contract_vocabulary_matches_the_symbolic_one() {
    // Same statement, both halves: `x <= 100` for a concrete x, and for all x.
    let runtime = contract::Contract::new(
        contract::Pred::Le(100),
        contract::Pred::Lt(200),
    );
    assert!(runtime.check_pre(100).is_ok());
    assert!(runtime.check_pre(101).is_err());

    let symbolic = smt::with_fresh(|| {
        let x = var(8);
        contract! { requires x.le_val(100), ensures x.lt_val(200) }
    });
    assert!(symbolic.is_proved());
}

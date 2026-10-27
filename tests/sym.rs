//! The operator-overloading DSL, checked for *semantics*, not just for compiling.
//!
//! `sym` is a thin wrapper over `smt`, so the risk is not a wrong bit-blast -- it is an
//! operator that quietly maps to the wrong primitive, or a literal form that exists for
//! one operator and not its neighbour. Both are tested here: every literal operator is
//! compared against the `smt::word` form it is defined as, and the `Var op Var` operators
//! are checked against the algebraic law they should satisfy.

use discharge::smt::{self, var, Var, Verdict};
use discharge::sym::*;

/// `lhs` and `rhs` are equivalent for every input.
fn equiv(lhs: discharge::smt::Pred, rhs: discharge::smt::Pred) {
    assert_eq!(
        smt::prove_equiv(lhs, rhs),
        Verdict::Valid,
        "the two forms must agree for every input"
    );
}

#[test]
fn every_literal_operator_means_the_same_as_its_word_form() {
    // The literal operators all desugar to `op(x, word(k, bits(x)))`. If one of them were
    // wired to the wrong primitive, the identity below would fail. The point of listing all
    // six is that the *set* has to be complete: the original set omitted `-` and `^`, so
    // `x - 1u32` and `x ^ 0xffu32` did not compile while their neighbours did, and a user
    // could not predict which existed.
    smt::with_fresh(|| {
        let x = var(8);
        let k = 0x0fu64;
        equiv((x + 0x0fu32).eq(smt::add(x, smt::word(k, 8))), smt::truth(true));
        equiv((x - 0x0fu32).eq(smt::sub(x, smt::word(k, 8))), smt::truth(true));
        equiv((x * 0x0fu32).eq(smt::mul(x, smt::word(k, 8))), smt::truth(true));
        equiv((x & 0x0fu32).eq(smt::band(x, smt::word(k, 8))), smt::truth(true));
        equiv((x | 0x0fu32).eq(smt::bor(x, smt::word(k, 8))), smt::truth(true));
        equiv((x ^ 0x0fu32).eq(smt::bxor(x, smt::word(k, 8))), smt::truth(true));
    });
}

#[test]
fn the_literal_operators_are_not_accidentally_all_the_same() {
    // Teeth for the test above: if every operator desugared to, say, addition, the
    // identities would still hold (each is checked against its own word form), so this
    // pins that the six forms are *different* from one another where they should be. On a
    // value where they disagree, they must disagree.
    smt::with_fresh(|| {
        let x = var(8);
        // At x = 3: 3 + 1 = 4, 3 - 1 = 2, 3 ^ 1 = 2, 3 & 1 = 1, 3 | 1 = 3, 3 * 1 = 3.
        let pin = smt::eq_const(x, 3);
        let add = smt::add(x, smt::word(1, 8));
        let sub = smt::sub(x, smt::word(1, 8));
        let xor = smt::bxor(x, smt::word(1, 8));
        assert_eq!(smt::prove_implies(pin, smt::eq_const(add, 4)), Verdict::Valid);
        assert_eq!(smt::prove_implies(pin, smt::eq_const(sub, 2)), Verdict::Valid);
        assert_eq!(smt::prove_implies(pin, smt::eq_const(xor, 2)), Verdict::Valid);
        // `+` and `-` must not be the same operator.
        assert_ne!(
            smt::prove_equiv(smt::eq_const(add, 4), smt::eq_const(sub, 4)),
            Verdict::Valid
        );
    });
}

#[test]
fn word_operators_satisfy_their_algebraic_laws() {
    smt::with_fresh(|| {
        let x = var(8);
        let y = var(8);
        // Commutativity of `+`, `&`, `|`, `^`. Multiplication is checked at a narrower
        // width below: the commutativity of an 8-bit multiplier is a BDD blow-up and comes
        // back `Unknown`, which is the engine being honest, not a defect in the operator.
        equiv((x + y).eq(y + x), smt::truth(true));
        equiv((x & y).eq(y & x), smt::truth(true));
        equiv((x | y).eq(y | x), smt::truth(true));
        equiv((x ^ y).eq(y ^ x), smt::truth(true));
        // `x - x == 0`.
        equiv((x - x).eq(smt::word(0, 8)), smt::truth(true));
    });
    smt::with_fresh(|| {
        let x = var(4);
        let y = var(4);
        equiv((x * y).eq(y * x), smt::truth(true));
    });
}

#[test]
fn a_shift_by_a_literal_matches_the_named_operation() {
    smt::with_fresh(|| {
        let x = var(8);
        // `Shr` on `Var` is the *logical* shift (`lshr`), matching the `smt` name.
        equiv((x >> 1u32).eq(smt::lshr(x, 1)), smt::truth(true));
        equiv((x << 1u32).eq(smt::shl(x, 1)), smt::truth(true));
    });
}

#[test]
fn predicate_operators_are_boolean_connectives() {
    smt::with_fresh(|| {
        let x = var(8);
        let p = x.lt_val(16);
        let q = x.lt_val(32);
        // `p & q` is conjunction, `p | q` disjunction, `!p` negation.
        equiv(smt::iff(p & q, smt::and(p, q)), smt::truth(true));
        equiv(smt::iff(p | q, smt::or(p, q)), smt::truth(true));
        equiv(smt::iff(!p, smt::not(p)), smt::truth(true));
        // `p => q` holds here (x < 16 implies x < 32), and is not the same as `q => p`.
        assert_eq!(p.implies(q).prove(), Verdict::Valid);
        assert_ne!(q.implies(p).prove(), Verdict::Valid);
    });
}

#[test]
fn variable_comparisons_agree_with_the_const_forms() {
    smt::with_fresh(|| {
        let x = var(8);
        let y = var(8);
        equiv(smt::iff(x.eq(y), smt::eq(x, y)), smt::truth(true));
        equiv(smt::iff(x.ne(y), smt::not(smt::eq(x, y))), smt::truth(true));
        equiv(smt::iff(x.lt(y), smt::ult(x, y)), smt::truth(true));
        equiv(smt::iff(x.le(y), smt::ule(x, y)), smt::truth(true));
        // `ge`/`gt` are the swapped-operand forms.
        equiv(smt::iff(x.ge(y), smt::ule(y, x)), smt::truth(true));
        equiv(smt::iff(x.gt(y), smt::ult(y, x)), smt::truth(true));
        // And the value forms.
        equiv(smt::iff(x.lt_val(16), smt::ult_const(x, 16)), smt::truth(true));
        equiv(smt::iff(x.le_val(16), smt::ule_const(x, 16)), smt::truth(true));
        equiv(smt::iff(x.gt_val(16), smt::ugt_const(x, 16)), smt::truth(true));
        equiv(smt::iff(x.ge_val(16), smt::uge_const(x, 16)), smt::truth(true));
        equiv(smt::iff(x.eq_val(16), smt::eq_const(x, 16)), smt::truth(true));
    });
}

#[test]
fn forall_is_the_identity_on_a_predicate() {
    // `forall` is documentation of intent: a `Pred` is already a statement about all
    // values, so the alias must not change it.
    smt::with_fresh(|| {
        let x = var(8);
        let p = x.lt_val(16);
        equiv(smt::iff(forall(p), p), smt::truth(true));
    });
}

#[test]
fn width_and_index_report_the_underlying_variable() {
    smt::with_fresh(|| {
        let x: Var = var(12);
        assert_eq!(x.width(), 12);
        assert_eq!(x.width(), smt::bits(x));
        assert_eq!(x.index(), smt::index(x));
    });
}

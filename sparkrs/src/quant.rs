//! Bounded quantification, expanded rather than decided.
//!
//! A bit-vector decision procedure has no quantifiers, and adding them would mean
//! a different engine. But the quantifiers that safety-critical code actually
//! needs are *bounded*: "every cell in this buffer is zero", "all elements below
//! the cursor have been processed". When the bound is a number the tool can count
//! to, a quantifier is not a search problem — it is a finite conjunction, and it
//! can simply be expanded.
//!
//! That is what this module does:
//!
//! ```text
//! forall k in 0..n { p(k) }   =>   p(0) && p(1) && ... && p(n-1)
//! exists k in 0..n { p(k) }   =>   p(0) || p(1) || ... || p(n-1)
//! ```
//!
//! The expansion is exact, so nothing is lost: a proof of the conjunction is a
//! proof of the quantified formula, and a counterexample names the index that
//! broke it.
//!
//! # The bound must be concrete, and that is the whole limitation
//!
//! `n` is a `usize`, not a symbolic word. `forall k in 0..k_var` is *not*
//! expressible, because the number of conjuncts would depend on a value the engine
//! has not fixed. When you need a bound that is symbolic — the standard case being
//! "all cells below the loop counter" — you write the guard into the predicate and
//! quantify over the full address space instead; see
//! [`crate::mem::Mem::forall_below`]. That turns the symbolic bound into `n`
//! guarded conjuncts, which is finite and therefore decidable.
//!
//! # Why this is not the same as unrolling by hand
//!
//! It is the same expansion, but stated once as a lemma rather than repeated at
//! every call site, and it composes: [`forall_range`] over a slice of cells is the
//! postcondition of a fill, the invariant of a scan, and the frame condition of a
//! write, all from one definition. The cost is the same either way, and it is worth
//! knowing: `n` conjuncts means `n` copies of the predicate in the decision
//! problem, so a bound of thousands is not practical. See the note on
//! [`crate::mem::MAX_CELLS`] for the same trade-off in the memory layer.

use crate::smt::{self, Pred};

/// `forall k in lo..hi { p(k) }`, expanded into a conjunction.
///
/// An empty range is vacuously true, which is the right identity: there is nothing
/// that could falsify it.
///
/// ```rust
/// use sparkrs::{quant, smt};
/// smt::with_fresh(|| {
///     let cells: Vec<_> = (0..4).map(|_| smt::var(8)).collect();
///     // Every cell is below 256, which is trivially true for a u8.
///     let p = quant::forall_range(0, 4, |k| smt::ult_const(cells[k], 256));
///     assert_eq!(smt::prove(p), smt::Verdict::Valid);
/// });
/// ```
pub fn forall_range<F>(lo: usize, hi: usize, p: F) -> Pred
where
    F: Fn(usize) -> Pred,
{
    let mut acc = smt::truth(true);
    for k in lo..hi {
        acc = smt::and(acc, p(k));
    }
    acc
}

/// `exists k in lo..hi { p(k) }`, expanded into a disjunction.
///
/// An empty range is false: nothing witnesses it.
pub fn exists_range<F>(lo: usize, hi: usize, p: F) -> Pred
where
    F: Fn(usize) -> Pred,
{
    let mut acc = smt::truth(false);
    for k in lo..hi {
        acc = smt::or(acc, p(k));
    }
    acc
}

/// `forall k in lo..hi { p(k) }` where the predicate is the same for every index.
///
/// Useful when the quantification is over structure rather than data — "every
/// element of this slice satisfies the same bound" — and the index would otherwise
/// be ignored.
pub fn forall_same(lo: usize, hi: usize, p: Pred) -> Pred {
    forall_range(lo, hi, |_| p)
}

/// `exists k in lo..hi { p(k) }` where the predicate is the same for every index.
pub fn exists_same(lo: usize, hi: usize, p: Pred) -> Pred {
    exists_range(lo, hi, |_| p)
}

/// `forall k in lo..hi { j < bound => p(k, j) }`: the quantified predicate is
/// guarded by a *symbolic* upper bound.
///
/// This is how a prefix property is stated when the prefix end is not known at
/// expansion time. `guarded` receives each concrete index together with a
/// predicate saying "this index is inside the bound"; the caller decides what to
/// do with it, normally by writing `smt::implies(inside, property)`.
///
/// ```rust
/// use sparkrs::{quant, smt};
/// smt::with_fresh(|| {
///     let cells: Vec<_> = (0..4).map(|_| smt::var(8)).collect();
///     let upto = smt::var(3); // symbolic prefix end
///     // "every cell below `upto` is zero"
///     let p = quant::forall_guarded(0, 4, upto, |k, inside| {
///         smt::implies(inside, smt::eq_const(cells[k], 0))
///     });
///     // Pinning the prefix to 0 makes it vacuous, so it holds.
///     assert_eq!(
///         smt::prove_implies(smt::eq_const(upto, 0), p),
///         smt::Verdict::Valid
///     );
/// });
/// ```
pub fn forall_guarded<F>(lo: usize, hi: usize, bound: smt::Var, guarded: F) -> Pred
where
    F: Fn(usize, Pred) -> Pred,
{
    let mut acc = smt::truth(true);
    for k in lo..hi {
        // `k < bound`, with `k` a concrete index and `bound` symbolic.
        let inside = smt::ult(smt::word(k as u64, smt::bits(bound)), bound);
        acc = smt::and(acc, guarded(k, inside));
    }
    acc
}

/// `exists k in lo..hi { j < bound && p(k, j) }`, the dual of [`forall_guarded`].
pub fn exists_guarded<F>(lo: usize, hi: usize, bound: smt::Var, guarded: F) -> Pred
where
    F: Fn(usize, Pred) -> Pred,
{
    let mut acc = smt::truth(false);
    for k in lo..hi {
        let inside = smt::ult(smt::word(k as u64, smt::bits(bound)), bound);
        acc = smt::or(acc, guarded(k, inside));
    }
    acc
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::smt::Verdict;

    #[test]
    fn an_empty_range_is_the_identity() {
        smt::with_fresh(|| {
            assert_eq!(smt::prove(forall_range(0, 0, |_| smt::truth(false))), Verdict::Valid);
            assert_eq!(smt::prove(exists_range(0, 0, |_| smt::truth(true))), Verdict::Unsat);
        });
    }

    #[test]
    fn a_universal_quantifier_is_a_conjunction() {
        smt::with_fresh(|| {
            let a = smt::var(8);
            let b = smt::var(8);
            // Quantifying over two different predicates equals their conjunction.
            let p = forall_range(0, 2, |k| if k == 0 { smt::ult_const(a, 5) } else { smt::ult_const(b, 5) });
            let q = smt::and(smt::ult_const(a, 5), smt::ult_const(b, 5));
            assert_eq!(smt::prove_equiv(p, q), Verdict::Valid);

            // One bad index breaks the whole thing.
            let all = forall_range(0, 2, |_| smt::ult_const(a, 5));
            assert!(matches!(
                smt::prove(all),
                Verdict::Counterexample(_)
            ));
        });
    }

    #[test]
    fn an_existential_quantifier_is_a_disjunction() {
        smt::with_fresh(|| {
            let a = smt::var(8);
            let b = smt::var(8);
            let p = exists_range(0, 2, |k| if k == 0 { smt::eq_const(a, 3) } else { smt::eq_const(b, 7) });
            let q = smt::or(smt::eq_const(a, 3), smt::eq_const(b, 7));
            assert_eq!(smt::prove_equiv(p, q), Verdict::Valid);

            // Something is always a witness for an unbounded u8.
            let some = exists_range(0, 4, |_| smt::ult_const(a, 256));
            assert_eq!(smt::prove(some), Verdict::Valid);
        });
    }

    #[test]
    fn the_two_quantifiers_are_dual() {
        smt::with_fresh(|| {
            let a = smt::var(8);
            let f = |k: usize| smt::ult_const(a, 4 + k as u64);
            // `!forall` is equivalent to `exists !`.
            let lhs = smt::not(forall_range(0, 3, f));
            let rhs = exists_range(0, 3, |k| smt::not(f(k)));
            assert_eq!(smt::prove_equiv(lhs, rhs), Verdict::Valid);
        });
    }

    #[test]
    fn a_guarded_prefix_collapses_when_the_bound_is_zero() {
        smt::with_fresh(|| {
            let a = smt::var(8);
            let b = smt::var(8);
            let upto = smt::var(2);
            let p = forall_guarded(0, 2, upto, |k, inside| {
                let cell = if k == 0 { a } else { b };
                smt::implies(inside, smt::eq_const(cell, 0))
            });
            // Nothing is below zero, so the property is vacuous.
            assert_eq!(smt::prove_implies(smt::eq_const(upto, 0), p), Verdict::Valid);
            // Below one, only cell 0 is constrained, so cell 1 is free.
            assert_eq!(
                smt::prove_implies(smt::and(smt::eq_const(upto, 1), smt::eq_const(a, 0)), p),
                Verdict::Valid
            );
            // And with the bound at the top, both are constrained.
            let q = smt::implies(
                smt::and(smt::eq_const(upto, 2), smt::and(smt::eq_const(a, 0), smt::eq_const(b, 0))),
                p,
            );
            assert_eq!(smt::prove(q), Verdict::Valid);
        });
    }

    #[test]
    fn guarded_and_unguarded_agree_at_a_concrete_bound() {
        smt::with_fresh(|| {
            let a = smt::var(8);
            let b = smt::var(8);
            let upto = smt::var(2);
            let guarded = forall_guarded(0, 2, upto, |k, inside| {
                let cell = if k == 0 { a } else { b };
                smt::implies(inside, smt::eq_const(cell, 0))
            });
            // At upto == 2 the guard is true for both indices, so it matches the
            // plain conjunction.
            let plain = smt::and(smt::eq_const(a, 0), smt::eq_const(b, 0));
            assert_eq!(
                smt::prove_implies(smt::eq_const(upto, 2), smt::iff(guarded, plain)),
                Verdict::Valid
            );
        });
    }

    #[test]
    fn the_same_predicate_helpers_match_the_general_form() {
        smt::with_fresh(|| {
            let a = smt::var(8);
            let p = smt::ult_const(a, 10);
            assert_eq!(
                smt::prove_equiv(forall_same(0, 3, p), forall_range(0, 3, |_| p)),
                Verdict::Valid
            );
            assert_eq!(
                smt::prove_equiv(exists_same(0, 3, p), exists_range(0, 3, |_| p)),
                Verdict::Valid
            );
        });
    }
}

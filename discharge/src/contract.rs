//! Runtime contract checking with the *same* predicate vocabulary as the prover.
//!
//! SPARK's `Pre`/`Post`/`Assert` are checked at runtime and proved statically.
//! This module is the runtime half: a small predicate type over concrete values,
//! plus an error type. Because the predicates mirror the symbolic ones in
//! [`crate::smt`], a contract written once can be discharged either way, and the
//! two results can be cross-checked (the `differential` test does exactly that).
//!
//! The checks are cheap and allocation-free, so they can stay enabled in release
//! builds on hardware where a violated invariant is worse than a branch.

use core::fmt;

/// A runtime predicate over a single `u64`-sized observation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Pred {
    /// Always true.
    True,
    /// Always false.
    False,
    /// `value == k`
    Eq(u64),
    /// `value != k`
    Ne(u64),
    /// `value < k` (unsigned)
    Lt(u64),
    /// `value <= k` (unsigned)
    Le(u64),
    /// `value > k` (unsigned)
    Gt(u64),
    /// `value >= k` (unsigned)
    Ge(u64),
    /// Logical negation.
    Not(&'static Pred),
    /// Conjunction.
    And(&'static Pred, &'static Pred),
    /// Disjunction.
    Or(&'static Pred, &'static Pred),
}

impl Pred {
    /// Evaluate the predicate on a concrete value.
    pub const fn eval(&self, value: u64) -> bool {
        match self {
            Pred::True => true,
            Pred::False => false,
            Pred::Eq(k) => value == *k,
            Pred::Ne(k) => value != *k,
            Pred::Lt(k) => value < *k,
            Pred::Le(k) => value <= *k,
            Pred::Gt(k) => value > *k,
            Pred::Ge(k) => value >= *k,
            Pred::Not(p) => !p.eval(value),
            Pred::And(a, b) => a.eval(value) && b.eval(value),
            Pred::Or(a, b) => a.eval(value) || b.eval(value),
        }
    }
}

/// A failed contract.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ContractError {
    /// Which obligation failed.
    pub kind: Obligation,
    /// The value that violated it.
    pub value: u64,
}

/// Which part of a contract failed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Obligation {
    /// The precondition was not met by the caller.
    Precondition,
    /// The postcondition was not met by the result.
    Postcondition,
    /// A loop or type invariant was broken.
    Invariant,
    /// An explicit assertion failed.
    Assertion,
}

impl fmt::Display for ContractError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let kind = match self.kind {
            Obligation::Precondition => "precondition",
            Obligation::Postcondition => "postcondition",
            Obligation::Invariant => "invariant",
            Obligation::Assertion => "assertion",
        };
        write!(f, "{} violated at value {}", kind, self.value)
    }
}

/// A function contract expressed over concrete values.
#[derive(Debug, Clone, Copy)]
pub struct Contract {
    /// Required of the input.
    pub pre: Pred,
    /// Guaranteed of the output.
    pub post: Pred,
}

impl Contract {
    /// Construct a contract.
    pub const fn new(pre: Pred, post: Pred) -> Contract {
        Contract { pre, post }
    }

    /// Check the precondition on a concrete input.
    pub const fn check_pre(&self, input: u64) -> Result<(), ContractError> {
        if self.pre.eval(input) {
            Ok(())
        } else {
            Err(ContractError { kind: Obligation::Precondition, value: input })
        }
    }

    /// Check the postcondition on a concrete output.
    pub const fn check_post(&self, output: u64) -> Result<(), ContractError> {
        if self.post.eval(output) {
            Ok(())
        } else {
            Err(ContractError { kind: Obligation::Postcondition, value: output })
        }
    }
}

/// Assert a runtime predicate, returning a structured error rather than
/// panicking. Useful in `no_std` code where a panic means a reset.
pub fn assert_that(p: Pred, value: u64) -> Result<(), ContractError> {
    if p.eval(value) {
        Ok(())
    } else {
        Err(ContractError { kind: Obligation::Assertion, value })
    }
}

/// Check a loop invariant on a concrete state.
pub fn check_invariant(p: Pred, value: u64) -> Result<(), ContractError> {
    if p.eval(value) {
        Ok(())
    } else {
        Err(ContractError { kind: Obligation::Invariant, value })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn predicates_evaluate() {
        assert!(Pred::Lt(10).eval(9));
        assert!(!Pred::Lt(10).eval(10));
        assert!(Pred::Ge(10).eval(10));
        assert!(Pred::And(&Pred::Ge(5), &Pred::Lt(10)).eval(7));
        assert!(Pred::Not(&Pred::Eq(1)).eval(2));
    }

    #[test]
    fn contract_reports_the_failing_obligation() {
        let c = Contract::new(Pred::Lt(100), Pred::Lt(200));
        assert!(c.check_pre(50).is_ok());
        let err = c.check_pre(150).unwrap_err();
        assert_eq!(err.kind, Obligation::Precondition);
        assert_eq!(err.value, 150);
    }
}

//! Verification conditions: `requires` / `ensures` / `invariant`, and the
//! `Verified<T>` wrapper that only exists once a condition is discharged.
//!
//! This is the SPARK-facing surface. A contract is written as a pair of
//! predicates over symbolic inputs, and [`Contract::discharge`] asks the
//! embedded decision procedure for a proof. Because the predicates are built
//! from the same [`crate::smt`] primitives, the *same* contract can be checked
//! at runtime on concrete values (see [`mod@crate::contract`]) and proved
//! symbolically on all values — which is exactly the property SPARK sells, and
//! which Rust's `debug_assert!` cannot give you.

use crate::proof::Certificate;
use crate::smt::{self, Pred, Var, Verdict};

/// A precondition, as a predicate over the (symbolic) inputs.
#[derive(Debug, Clone, Copy)]
pub struct Precondition(pub(crate) Pred);

/// A full contract: a precondition and a postcondition.
#[derive(Debug, Clone, Copy)]
pub struct Contract {
    pub(crate) pre: Pred,
    pub(crate) post: Pred,
}

/// State a precondition.
pub fn requires(pre: Pred) -> Precondition {
    Precondition(pre)
}

/// Attach a postcondition to a precondition, forming a contract.
pub fn ensures(pre: Precondition, post: Pred) -> Contract {
    Contract { pre: pre.0, post }
}

impl Contract {
    /// Prove the contract: `pre => post`, for every input.
    ///
    /// This discharges the *implication*, which is the standard Hoare reading: a
    /// contract whose precondition cannot hold is vacuously true, and
    /// `discharge` reports it `Valid`. That is deliberate and matches
    /// [`verify_contract`] and [`invariant`], but it is not the same promise as
    /// [`crate::wp::verify`], which treats an unsatisfiable precondition as a
    /// *finding* rather than a proof. If you need the non-vacuous reading, ask
    /// [`Contract::precondition_is_satisfiable`] as well.
    pub fn discharge(&self) -> Verdict {
        smt::prove_implies(self.pre, self.post)
    }

    /// Whether some input satisfies the precondition.
    ///
    /// `discharge` proves `pre => post`, which is vacuously true when `pre` is
    /// unsatisfiable. This is the companion question: does the precondition
    /// describe any input at all? A `false` here means a `Valid` from
    /// [`Contract::discharge`] says nothing about the postcondition.
    pub fn precondition_is_satisfiable(&self) -> bool {
        smt::find_model(self.pre) != Verdict::Unsat
    }

    /// The precondition, as a predicate.
    pub fn precondition(&self) -> Pred {
        self.pre
    }

    /// The postcondition, as a predicate.
    pub fn postcondition(&self) -> Pred {
        self.post
    }

    /// Prove the contract and hand back a certificate, or `None` if it did not
    /// hold. This is the bridge from "a formula the prover accepted" to "a value
    /// the type system will let you use".
    pub fn certify(&self) -> Option<Certificate> {
        // The certificate attests to the implication as a whole: that is the
        // claim the prover actually established, so it is what we hand back.
        Certificate::discharge(smt::implies(self.pre, self.post))
    }
}

/// Build and discharge a contract in one call.
///
/// Discharges the implication `pre => post`, so an unsatisfiable `pre` makes the
/// result `Valid` without the postcondition having been checked. See
/// [`Contract::discharge`] and [`Contract::precondition_is_satisfiable`].
pub fn verify_contract(pre: Pred, post: Pred) -> Verdict {
    smt::prove_implies(pre, post)
}

/// A loop invariant, proved the way Hoare logic demands.
///
/// * `init` — the predicate that holds on entry to the loop. This is an
///   *assumption* about the entry state, not a theorem about every state, so it
///   appears as the antecedent.
/// * `keep` — `invariant && guard => invariant'`, where the caller has already
///   substituted the next-state expressions into `keep`.
///
/// The discharged obligation is `init => keep`, i.e. "starting from a state that
/// satisfies the invariant, one iteration preserves it".
pub fn invariant(init: Pred, keep: Pred) -> Verdict {
    smt::prove_implies(init, keep)
}

/// A verification condition for a function body: for every input satisfying
/// `pre`, the output computed by `body` satisfies `post`.
///
/// `body` is the *actual algorithm*, expressed symbolically. If you can write
/// the symbolic version next to the concrete one, this checks the real thing.
pub fn verify_body<B, P>(pre: impl Fn(Var) -> Pred, post: P, body: B) -> Verdict
where
    B: Fn(Var) -> Var,
    P: Fn(Var, Var) -> Pred,
{
    smt::with_fresh(|| {
        let input = smt::var(32);
        let pre_p = pre(input);
        let output = body(input);
        let post_p = post(input, output);
        smt::prove_implies(pre_p, post_p)
    })
}

/// A value carrying a machine-checked theorem alongside it.
///
/// The wrapper stores the *statement* the decision procedure proved, so it cannot
/// claim more than that: [`Verified::new`] discharges the statement itself, and
/// [`Verified::from_certificate`] records exactly the statement the certificate proves.
/// Either way, holding a `Verified<T>` means "the stored statement is a theorem", and
/// [`Verified::statement`] hands you that statement to check.
///
/// Two boundaries, stated plainly because the previous version of this comment
/// overstated what the type gives you.
///
/// First, the wrapper does **not** establish that `value` satisfies `statement`. The
/// statement is a predicate over *symbolic* variables and `value` is a concrete `T`;
/// there is no evaluation link between them, so no constructor can check the connection.
/// Relating the two is the caller's job — build the value so that the statement describes
/// it.
///
/// Second, and easy to miss: because the statement is a theorem, it is semantically
/// equivalent to `true`. Every theorem is. So the statement carries **no semantic content
/// about the value** — it cannot, or it would not be provable. Its value is *bookkeeping*:
/// it records which theorem was discharged, so a wrapper cannot silently carry a
/// certificate for something unrelated, and a reviewer can see the claim. The type
/// prevents mismatched bookkeeping, not an untrue claim.
#[derive(Debug, Clone, Copy)]
pub struct Verified<T> {
    value: T,
    statement: Pred,
    _cert: Certificate,
}

impl<T> Verified<T> {
    /// Wrap a value given a statement to prove. Returns `None` if the statement is not
    /// a theorem (refuted or unknown), so the wrapper cannot be built without a proof.
    pub fn new(value: T, statement: Pred) -> Option<Self> {
        Certificate::discharge(statement)
            .map(|cert| Verified { value, statement, _cert: cert })
    }

    /// Wrap a value given an existing certificate.
    ///
    /// The wrapper's statement is *derived from the certificate*, not supplied separately,
    /// so it cannot attest to anything other than what was proved. A `Contract` can be
    /// turned into a certificate with [`Contract::certify`], whose statement is the
    /// implication `pre => post`.
    ///
    /// `None` if the certificate is stale — that is, the arena has been reset since it was
    /// issued. Term ids are recycled by a reset, so a stale certificate's id now names a
    /// different formula; wrapping a value with it would tag the value with a claim nobody
    /// proved.
    pub fn from_certificate(value: T, cert: Certificate) -> Option<Self> {
        cert.statement()
            .map(|statement| Verified { value, statement, _cert: cert })
    }

    /// The statement this value is tagged with. It is a theorem.
    pub fn statement(&self) -> Pred {
        self.statement
    }

    /// Borrow the value.
    pub fn get(&self) -> &T {
        &self.value
    }

    /// Unwrap the value.
    pub fn into_inner(self) -> T {
        self.value
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn contract_is_discharged() {
        let v = smt::with_fresh(|| {
            let x = smt::var(8);
            let c = ensures(requires(smt::ult_const(x, 16)), smt::ult_const(x, 32));
            c.discharge()
        });
        assert!(v.is_proved());
    }

    #[test]
    fn weak_contract_is_refuted() {
        let v = smt::with_fresh(|| {
            let x = smt::var(8);
            let c = ensures(requires(smt::ult_const(x, 32)), smt::ult_const(x, 16));
            c.discharge()
        });
        assert!(matches!(v, Verdict::Counterexample(_)));
    }

    #[test]
    fn body_verification_works() {
        // ∀ x. x < 100  =>  x + 1 <= 100
        let v = verify_body(
            |x| smt::ult_const(x, 100),
            |_x, y| smt::ule_const(y, 100),
            |x| smt::add(x, smt::word(1, 32)),
        );
        assert!(v.is_proved(), "got {}", v);
    }

    #[test]
    fn loop_invariant_holds() {
        // Entry: i <= 10. Step: guard is i < 10, next state is i + 1, and the
        // invariant must survive: i <= 10 && i < 10  =>  i + 1 <= 10.
        let v = smt::with_fresh(|| {
            let i = smt::var(8);
            let init = smt::ule_const(i, 10);
            let ip = smt::add(i, smt::word(1, 8));
            let guard = smt::ult_const(i, 10);
            let keep = smt::implies(smt::and(init, guard), smt::ule_const(ip, 10));
            invariant(init, keep)
        });
        assert!(v.is_proved(), "got {}", v);
    }
}

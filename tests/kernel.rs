//! The proof kernel: propositions as types, proofs as values, and certificates
//! that compose. If any of this were wrong, the test would not *compile*.

use discharge::prelude::*;
use discharge::proof::{
    conj, conj_left, conj_right, id_imp, imp_intro, modus_ponens, truth_proof, And, Equals, Imp,
    Theorem, Truth, TruthProof,
};
use discharge::smt::{self, Verdict};

#[test]
fn trivial_propositions_are_provable() {
    // These are compile-time obligations: the calls only exist because the
    // kernel can produce the proof terms.
    assert_proof!(Truth);
    assert_proof!(And<Truth, Truth>);
    assert_proof!(Imp<Truth, Truth>);
    assert_proof!(Equals<u32, u32>);

    // And the proof terms can be built and taken apart.
    let both = conj::<Truth, Truth>(truth_proof(), truth_proof());
    let _left: <Truth as Theorem>::Proof = conj_left::<Truth, Truth>(both);
    let _right: <Truth as Theorem>::Proof = conj_right::<Truth, Truth>(both);
}

#[test]
fn modus_ponens_composes() {
    // Truth => Truth, applied to Truth, yields Truth.
    let imp = id_imp::<Truth>();
    let out = modus_ponens::<Truth, Truth>(imp, truth_proof());
    // `out` has type TruthProof; the assertion is really that this compiles.
    let _ = out;
}

#[test]
fn the_imp_associated_proof_type_is_a_function_between_proofs() {
    // The `Theorem` impl for `Imp` once had no bounds and used the *propositions* `P, Q`
    // as its `Proof` type, so `<Imp<Truth, Truth> as Theorem>::Proof` was
    // `ImpProof<Truth, Truth>` while `id_imp` produced `ImpProof<TruthProof, TruthProof>`.
    // Nothing caught the mismatch, because no test ever named the associated type -- and
    // the same missing bound let `assert_proof!(Imp<Truth, Falsity>)` compile, so the
    // kernel proved a falsehood. Naming the type here is what pins it: this does not
    // compile unless `Proof` is `ImpProof<P::Proof, Q::Proof>`.
    let via_constructor: <Imp<Truth, Truth> as Theorem>::Proof = id_imp::<Truth>();
    let via_intro: <Imp<Truth, Truth> as Theorem>::Proof =
        imp_intro::<Truth, Truth>(|t: TruthProof| t);
    // And the two are usable by modus ponens, which is the point of the type.
    let _a = modus_ponens::<Truth, Truth>(via_constructor, truth_proof());
    let _b = modus_ponens::<Truth, Truth>(via_intro, truth_proof());

    // The nested case: `Truth => (Truth => Truth)` is a theorem, and its proof type is a
    // function from `TruthProof` to the proof of the inner implication. A wrong `Proof`
    // type for `Imp` shows up here as a type error.
    let nested: <Imp<Truth, Imp<Truth, Truth>> as Theorem>::Proof =
        imp_intro::<Truth, Imp<Truth, Truth>>(|_| id_imp::<Truth>());
    let _c = modus_ponens::<Truth, Imp<Truth, Truth>>(nested, truth_proof());
}

#[test]
fn certificates_are_only_produced_for_truths() {
    smt::with_fresh(|| {
        let x = var(8);

        // A true statement yields a certificate.
        let c = Certificate::discharge(x.le_val(255));
        assert!(c.is_some(), "x <= 255 should be provable for u8");

        // A false statement yields nothing: there is no way to fabricate proof.
        let bad = Certificate::discharge(x.lt_val(200));
        assert!(bad.is_none(), "x < 200 must not be provable for u8");
    });
}

#[test]
fn certificates_compose_by_kernel_rules() {
    smt::with_fresh(|| {
        let x = var(8);

        let a = Certificate::discharge(x.le_val(255)).unwrap();
        let b = Certificate::discharge(x.ge_val(0)).unwrap();

        // Conjunction introduction, as a kernel rule (no re-checking needed).
        // Both certificates belong to this arena, so the rule applies.
        let both = a.and(b).expect("both certificates are current");
        assert!(matches!(smt::prove(both.statement().unwrap()), Verdict::Valid));

        // Weakening: a proved statement may be re-checked against a weaker one.
        // `x <= 255` does *not* entail `x < 255` (take x = 255), so this fails.
        assert!(a.weaken_to(x.lt_val(255)).is_none());

        // But `x >= 0` (i.e. `true`) entails `x <= 255` for a u8, so this holds.
        assert!(b.weaken_to(x.le_val(255)).is_some());
    });
}

#[test]
fn implication_modus_ponens() {
    smt::with_fresh(|| {
        let x = var(8);

        // x < 16  =>  x < 32
        let imp = Implication::discharge(x.lt_val(16), x.lt_val(32)).unwrap();
        assert_eq!(imp.antecedent(), Some(x.lt_val(16)));
        assert_eq!(imp.consequent(), Some(x.lt_val(32)));

        // `x < 16` is not a theorem for a free `u8`, so there is no certificate
        // for the bare antecedent: this is the kernel refusing to invent proof.
        assert!(Certificate::discharge(x.lt_val(16)).is_none());

        // Under the antecedent as a hypothesis, modus ponens does go through:
        // prove `(x < 16) => (x < 32)` and `(x < 32) => (x < 64)` compose.
        let guard = Certificate::discharge(x.lt_val(16).implies(x.lt_val(32))).unwrap();
        assert_eq!(guard.statement(), Some(x.lt_val(16).implies(x.lt_val(32))));
    });
}

#[test]
fn implication_cut_chains() {
    smt::with_fresh(|| {
        let x = var(8);
        let a = Implication::discharge(x.lt_val(16), x.lt_val(32)).unwrap();
        let b = Implication::discharge(x.lt_val(32), x.lt_val(64)).unwrap();
        let chained = a.then(b).expect("chain should compose");
        assert_eq!(chained.antecedent(), Some(x.lt_val(16)));
        assert_eq!(chained.consequent(), Some(x.lt_val(64)));
    });
}

#[test]
fn verified_wrapper_requires_a_certificate() {
    smt::with_fresh(|| {
        let x = var(8);
        // The wrapper records the statement the certificate proves, so it cannot be
        // tagged with a theorem about something else.
        let cert = Certificate::discharge(x.le_val(255)).unwrap();
        let v = Verified::from_certificate(42u32, cert).expect("certificate is current");
        assert_eq!(*v.get(), 42);
        assert_eq!(v.into_inner(), 42);

        // And the statement is retrievable, which is the point: the claim is checkable
        // rather than implied by the type's name.
        assert!(smt::prove(v.statement()).is_proved());

        // A statement that is not a theorem cannot be wrapped at all.
        assert!(
            Verified::new(42u32, x.lt_val(200)).is_none(),
            "a refuted statement must not yield a Verified value"
        );
        assert!(
            Verified::new(42u32, x.le_val(255)).is_some(),
            "a proved statement must yield a Verified value"
        );
    });
}

// `Falsity` is deliberately uninhabited: there is no `Theorem` impl for it, so
// `assert_proof!(Falsity)` is a compile error. That is pinned down by the
// `compile_fail` doctest on the `discharge::proof` module, which is the only place
// `cargo test --doc` actually executes.

#[test]
fn a_verified_value_records_the_statement_it_proves() {
    // The eleventh hole, and the one that undercut the crate's central promise: an
    // overclaiming abstraction. The doc said holding a `Verified<T>` was "a machine-checked
    // claim that the associated contract was proved", but `Verified` stored no contract and
    // `new(value, cert)` accepted any certificate. `tests/kernel.rs` had been doing exactly
    // the wrong thing and passing:
    //
    //   let cert = Certificate::discharge(x.le_val(255)).unwrap(); // proves x <= 255
    //   let v = Verified::new(42u32, cert);                        // value is 42u32
    //
    // Nothing connected the two, and the type's name asserted a connection.
    //
    // Now the statement is stored and retrievable, so the claim is checkable instead of
    // implied, and `from_certificate` takes the statement *from* the certificate so it
    // cannot attest to anything else.
    smt::with_fresh(|| {
        let x = var(8);
        let cert = Certificate::discharge(x.le_val(255)).unwrap();
        let v = Verified::from_certificate(42u32, cert).expect("certificate is current");
        assert_eq!(*v.get(), 42);
        // The stored statement is a theorem, and it is the one the certificate proved.
        assert!(
            smt::prove(v.statement()).is_proved(),
            "the stored statement must itself be a theorem"
        );
        // Structural identity, not semantic equivalence. Every certificate is a theorem,
        // and every theorem is semantically equivalent to `true`, so `prove_equiv` cannot
        // tell `x <= 255` from `true` here -- it would return Valid either way. The
        // structural comparison is the one with teeth: it catches a wrapper that records
        // *some* theorem instead of *the* theorem. (I first wrote this check with
        // prove_equiv and it passed against a deliberately broken wrapper, which is how
        // this distinction surfaced.)
        assert_eq!(
            v.statement(),
            x.le_val(255),
            "the statement must be the certificate's statement, not just any theorem"
        );
    });
}

#[test]
fn a_verified_value_cannot_be_built_from_a_false_statement() {
    // The teeth. `Verified::new` discharges the statement, so it refuses anything that is
    // not a theorem. Without this, a caller could tag a value with a claim the prover had
    // refuted and get a `Verified` back.
    smt::with_fresh(|| {
        let x = var(8);
        assert!(
            Verified::new(42u32, x.lt_val(200)).is_none(),
            "a refuted statement must not yield a Verified value"
        );
        assert!(
            Verified::new(42u32, x.le_val(255)).is_some(),
            "a proved statement must yield a Verified value"
        );
    });
}

#[test]
fn a_certificate_does_not_survive_an_arena_reset() {
    // The twelfth hole, and the most serious: a proof object whose *meaning* changes
    // underneath it. A `Certificate` stores a `Pred`, which is a term id, and `with_fresh`
    // resets the arena so ids restart at 0. So a certificate from one scope named a
    // different formula in the next, and a kernel rule would then produce a certificate
    // for a statement the engine itself refutes:
    //
    //   scope A statement id : Pred(Term(2))
    //   scope B predicate id : Pred(Term(2))     <- id recycled
    //   same id?             : true
    //   prove(cert.statement()) in scope B : Counterexample
    //   cert.weaken_to(y < 200) -> true          <- a certificate for a falsehood
    //
    // The engine knew `y < 200` was false and the certificate claimed it was proved. The
    // comment on `with_fresh` warned about exactly this ("use-after-free in the term
    // arena"), but a warning is not a check, and the failure is silent rather than a
    // panic. A certificate now records the arena generation and every rule re-checks it.
    let cert = smt::with_fresh(|| {
        let x = var(8);
        Certificate::discharge(x.le_val(255)).unwrap()
    });
    assert!(cert.is_current(), "the certificate is current in its own arena");

    smt::with_fresh(|| {
        let y = var(8);
        assert!(
            !cert.is_current(),
            "a reset must invalidate the certificate's generation"
        );
        assert!(
            cert.statement().is_none(),
            "a stale certificate has no statement: its id names a different formula now"
        );
        assert!(
            cert.weaken_to(y.lt_val(200)).is_none(),
            "a stale certificate must not weaken into a statement the engine refutes"
        );
        assert!(
            cert.and(cert).is_none(),
            "a stale certificate must not compose with itself"
        );
        // And the arena really does refute the statement the stale id now names.
        assert!(
            matches!(smt::prove(y.lt_val(200)), Verdict::Counterexample(_)),
            "the recycled id names a refuted formula, which is the danger"
        );
    });
}

#[test]
fn a_certificate_still_works_inside_its_own_arena() {
    // The teeth. The generation check must not reject certificates that are in scope, or
    // every kernel rule would break. Inside one arena, everything composes as before.
    smt::with_fresh(|| {
        let x = var(8);
        let a = Certificate::discharge(x.le_val(255)).unwrap();
        let b = Certificate::discharge(x.ge_val(0)).unwrap();
        assert!(a.is_current() && b.is_current());
        let both = a.and(b).expect("current certificates compose");
        assert!(matches!(smt::prove(both.statement().unwrap()), Verdict::Valid));
        assert!(b.weaken_to(x.le_val(255)).is_some());
        assert!(a.weaken_to(x.lt_val(255)).is_none(), "a false weakening still fails");

        let imp = Implication::discharge(x.lt_val(16), x.lt_val(32)).unwrap();
        assert!(imp.is_current());
        assert_eq!(imp.antecedent(), Some(x.lt_val(16)));
        let chained = imp.then(Implication::discharge(x.lt_val(32), x.lt_val(64)).unwrap());
        assert!(chained.is_some(), "current implications chain");
    });
}

#[test]
fn a_verified_value_cannot_be_built_from_a_stale_certificate() {
    // The wrapper is the other place a certificate is stored, so it needs the same check.
    // A stale certificate would tag a value with a claim nobody proved.
    let cert = smt::with_fresh(|| {
        let x = var(8);
        Certificate::discharge(x.le_val(255)).unwrap()
    });
    smt::with_fresh(|| {
        assert!(
            Verified::from_certificate(42u32, cert).is_none(),
            "a stale certificate must not produce a Verified value"
        );
    });
}

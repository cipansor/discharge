//! The proof kernel: propositions as types, proofs as values, and certificates
//! that compose. If any of this were wrong, the test would not *compile*.

use sparkrs::prelude::*;
use sparkrs::proof::{
    conj, conj_left, conj_right, id_imp, modus_ponens, truth_proof, And, Equals, Imp, Theorem,
    Truth,
};
use sparkrs::smt::{self, Verdict};

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
        let both = a.and(b);
        assert!(matches!(smt::prove(both.statement()), Verdict::Valid));

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
        assert_eq!(imp.antecedent(), x.lt_val(16));
        assert_eq!(imp.consequent(), x.lt_val(32));

        // `x < 16` is not a theorem for a free `u8`, so there is no certificate
        // for the bare antecedent: this is the kernel refusing to invent proof.
        assert!(Certificate::discharge(x.lt_val(16)).is_none());

        // Under the antecedent as a hypothesis, modus ponens does go through:
        // prove `(x < 16) => (x < 32)` and `(x < 32) => (x < 64)` compose.
        let guard = Certificate::discharge(x.lt_val(16).implies(x.lt_val(32))).unwrap();
        assert_eq!(guard.statement(), x.lt_val(16).implies(x.lt_val(32)));
    });
}

#[test]
fn implication_cut_chains() {
    smt::with_fresh(|| {
        let x = var(8);
        let a = Implication::discharge(x.lt_val(16), x.lt_val(32)).unwrap();
        let b = Implication::discharge(x.lt_val(32), x.lt_val(64)).unwrap();
        let chained = a.then(b).expect("chain should compose");
        assert_eq!(chained.antecedent(), x.lt_val(16));
        assert_eq!(chained.consequent(), x.lt_val(64));
    });
}

#[test]
fn verified_wrapper_requires_a_certificate() {
    smt::with_fresh(|| {
        let x = var(8);
        let cert = Certificate::discharge(x.le_val(255)).unwrap();
        let v = Verified::new(42u32, cert);
        assert_eq!(*v.get(), 42);
        assert_eq!(v.into_inner(), 42);
    });
}

// `Falsity` is deliberately uninhabited: there is no `Theorem` impl for it, so
// `assert_proof!(Falsity)` is a compile error. That is pinned down by the
// `compile_fail` doctest on the `sparkrs::proof` module, which is the only place
// `cargo test --doc` actually executes.

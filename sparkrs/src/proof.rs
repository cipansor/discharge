//! Machine-checked proofs, and proof composition.
//!
//! There are two layers here, and it is worth being precise about what each one
//! guarantees.
//!
//! # 1. The type-level kernel ([`Truth`], [`And`], [`Imp`], [`Equals`], ...)
//!
//! Propositions are *types*; a proof is a *value* of the proposition's `Proof`
//! type. The only way to obtain a proof is through a kernel rule, and there is
//! deliberately no rule that builds evidence for [`Falsity`]. So "proving" a
//! proposition means making `rustc` accept a term of the right type: if the
//! reasoning is wrong, the program does not compile. This is the
//! Curry–Howard–Lambek reading of the Rust type system, used as a small proof
//! kernel.
//!
//! # 2. Certificates from the embedded decision procedure ([`Certificate`])
//!
//! For statements about bit-vectors, the kernel above is not enough: the fact
//! "for all `x`, `x & 0xff < 256`" is not a *type*, it is a formula. So we pair
//! it with [`crate::smt`]: a [`Certificate`] can only be constructed from a
//! [`Verdict::Valid`] verdict, and certificates compose by the ordinary rules of
//! natural deduction (conjunction introduction, modus ponens), with each rule
//! discharging its own obligation. A certificate is therefore a proof object
//! that the artifact itself can carry, inspect, and hand to a checker.
//!
//! # A proposition that cannot be proved
//!
//! [`Falsity`] is uninhabited and has no [`Theorem`] impl, so asking the kernel
//! for its proof is a *compile* error rather than a runtime failure:
//!
//! ```compile_fail
//! use sparkrs::proof::Falsity;
//! use sparkrs::assert_proof;
//! assert_proof!(Falsity);
//! ```
//!
//! The same must hold for a *false implication*, and it is a separate check because an
//! implication is the one connective that carries reasoning. `Imp<P, Q>` is only a theorem
//! when `P` and `Q` are, so `Truth => Falsity` must not compile:
//!
//! ```compile_fail
//! use sparkrs::assert_proof;
//! use sparkrs::proof::{Falsity, Imp, Truth};
//! assert_proof!(Imp<Truth, Falsity>);
//! ```
//!
//! This example is not decoration. The `Theorem` impl for `Imp` originally carried no
//! bounds and used the *propositions* `P, Q` as its `Proof` type, so the kernel accepted
//! `Truth => Falsity` -- a proof of a falsehood, from the module whose doc says a wrong
//! proof does not compile. The two `compile_fail` examples are the teeth.
//!
//! # A proposition that is proved by the compiler
//!
//! ```
//! use sparkrs::assert_proof;
//! use sparkrs::proof::{And, Equals, Imp, Truth};
//! assert_proof!(Truth);
//! assert_proof!(And<Truth, Imp<Truth, Truth>>);
//! assert_proof!(Equals<u8, u8>);
//! ```

use crate::smt::{self, Pred, Verdict};
use core::marker::PhantomData;

// ---------------------------------------------------------------------------
// Type-level kernel
// ---------------------------------------------------------------------------

/// The proposition that is trivially true.
pub struct Truth;

/// The proposition that is false. Note: no `Theorem` impl, and none can exist.
pub enum Falsity {}

/// Conjunction of two propositions.
pub struct And<P, Q>(PhantomData<(P, Q)>);

/// Implication between two propositions.
pub struct Imp<P, Q>(PhantomData<(P, Q)>);

/// Type-level equality. Only `Equals<A, A>` is inhabited.
pub struct Equals<A, B>(PhantomData<(A, B)>);

/// A proposition we can prove.
pub trait Theorem {
    /// The proof term for this proposition.
    type Proof;
}

/// The unique proof of [`Truth`].
#[derive(Debug, Clone, Copy)]
pub struct TruthProof;

/// Proof of [`And<P, Q>`] from proofs of `P` and `Q`.
#[derive(Debug, Clone, Copy)]
pub struct AndProof<A, B> {
    /// Proof of the left conjunct.
    pub left: A,
    /// Proof of the right conjunct.
    pub right: B,
}

/// Proof of [`Imp<P, Q>`]: a function turning a proof of `P` into a proof of `Q`.
#[derive(Clone, Copy)]
pub struct ImpProof<A, B> {
    /// The witness function.
    pub run: fn(A) -> B,
}

/// Proof of [`Equals<A, A>`].
#[derive(Debug, Clone, Copy)]
pub struct Refl;

impl Theorem for Truth {
    type Proof = TruthProof;
}

impl<P: Theorem, Q: Theorem> Theorem for And<P, Q> {
    type Proof = AndProof<P::Proof, Q::Proof>;
}

impl<P: Theorem, Q: Theorem> Theorem for Imp<P, Q> {
    // A proof of `P => Q` is a function from proofs of `P` to proofs of `Q`, so the
    // parameters are the *proof* types, not the propositions.
    //
    // Both bounds are load-bearing, and the first version of this impl had neither. With
    // no bounds and `type Proof = ImpProof<P, Q>`, the associated type was the function
    // `fn(P) -> Q` over the *propositions*, which is not a function between proofs at all
    // -- and, because no bound mentioned `Theorem`, `assert_proof!(Imp<Truth, Falsity>)`
    // compiled. The kernel accepted `Truth => Falsity`, a falsehood, while correctly
    // rejecting `And<Truth, Falsity>` and `Equals<u8, u16>`; the module's own promise that
    // "if the reasoning is wrong, the program does not compile" was false for the one
    // connective that carries reasoning. `imp_intro` and `modus_ponens` already used
    // `P::Proof`/`Q::Proof`, so the constructors did not type-check against the associated
    // type either -- a mismatch nothing was testing, because no test named the associated
    // type. `tests/kernel.rs` now does.
    type Proof = ImpProof<P::Proof, Q::Proof>;
}

impl<A> Theorem for Equals<A, A> {
    type Proof = Refl;
}

/// Introduce a conjunction.
pub fn conj<P: Theorem, Q: Theorem>(p: P::Proof, q: Q::Proof) -> AndProof<P::Proof, Q::Proof> {
    AndProof { left: p, right: q }
}

/// Eliminate a conjunction (left projection).
pub fn conj_left<P: Theorem, Q: Theorem>(p: AndProof<P::Proof, Q::Proof>) -> P::Proof {
    p.left
}

/// Eliminate a conjunction (right projection).
pub fn conj_right<P: Theorem, Q: Theorem>(p: AndProof<P::Proof, Q::Proof>) -> Q::Proof {
    p.right
}

/// Introduce an implication from a function that maps proofs to proofs.
pub fn imp_intro<P: Theorem, Q: Theorem>(f: fn(P::Proof) -> Q::Proof) -> ImpProof<P::Proof, Q::Proof> {
    ImpProof { run: f }
}

/// Modus ponens: from `P => Q` and `P`, conclude `Q`.
pub fn modus_ponens<P: Theorem, Q: Theorem>(
    imp: ImpProof<P::Proof, Q::Proof>,
    p: P::Proof,
) -> Q::Proof {
    (imp.run)(p)
}

/// The one proof of reflexivity.
pub fn refl<A>() -> Refl {
    Refl
}

/// `P => P`, for any provable `P`.
pub fn id_imp<P: Theorem>() -> ImpProof<P::Proof, P::Proof> {
    ImpProof { run: |p| p }
}

/// `Truth` is provable, always.
pub fn truth_proof() -> TruthProof {
    TruthProof
}

// ---------------------------------------------------------------------------
// Certificates from the decision procedure
// ---------------------------------------------------------------------------

/// A proof of a bit-vector formula, obtained from the embedded decision
/// procedure. Constructible only from [`Verdict::Valid`].
///
/// A certificate is tied to the arena that produced it. Term ids are recycled when the
/// arena is reset ([`crate::smt::with_fresh`]), so the same id means a different formula
/// afterwards; a certificate that outlived its arena would otherwise attest to whatever
/// now occupies that id. Every rule re-checks the generation and returns `None` on a
/// mismatch, so a stale certificate composes into nothing rather than into a falsehood.
#[derive(Debug, Clone, Copy)]
pub struct Certificate {
    statement: Pred,
    generation: u32,
}

impl Certificate {
    /// Discharge `statement` symbolically. `None` means the statement was not
    /// proved (refuted or unknown) — the caller must not assume it.
    pub fn discharge(statement: Pred) -> Option<Certificate> {
        match smt::prove(statement) {
            Verdict::Valid => Some(Certificate { statement, generation: smt::generation() }),
            _ => None,
        }
    }

    /// The statement this certificate proves.
    ///
    /// `None` if the arena has been reset since: the id no longer names this formula, so
    /// there is no statement to hand back. This is the safe reading of a stale handle,
    /// not a limitation — the alternative is a formula the certificate never proved.
    pub fn statement(&self) -> Option<Pred> {
        if self.is_current() {
            Some(self.statement)
        } else {
            None
        }
    }

    /// True if this certificate still refers to the arena that produced it.
    pub fn is_current(&self) -> bool {
        self.generation == smt::generation()
    }

    /// Conjunction introduction: two proved statements yield their conjunction.
    /// This is a kernel rule, so no re-checking is required.
    ///
    /// Both certificates must belong to the current arena; otherwise this returns `None`,
    /// because a recycled id would make the conjunction say something neither proved.
    pub fn and(self, other: Certificate) -> Option<Certificate> {
        if !self.is_current() || !other.is_current() {
            return None;
        }
        Some(Certificate {
            statement: smt::and(self.statement, other.statement),
            generation: self.generation,
        })
    }

    /// Weakening: a proved statement may be re-checked against a weaker one.
    /// Returns `None` if the weakening does not hold, or if the certificate is stale.
    pub fn weaken_to(self, weaker: Pred) -> Option<Certificate> {
        if !self.is_current() {
            return None;
        }
        match smt::prove_implies(self.statement, weaker) {
            Verdict::Valid => {
                Some(Certificate { statement: weaker, generation: self.generation })
            }
            _ => None,
        }
    }
}

/// A proved implication, applicable to a certificate with [`Implication::apply`].
///
/// Like [`Certificate`], an implication is valid only in the arena that produced it; every
/// rule re-checks the generation.
#[derive(Debug, Clone, Copy)]
pub struct Implication {
    pre: Pred,
    post: Pred,
    generation: u32,
}

impl Implication {
    /// Discharge `pre => post` symbolically.
    pub fn discharge(pre: Pred, post: Pred) -> Option<Implication> {
        match smt::prove_implies(pre, post) {
            Verdict::Valid => {
                Some(Implication { pre, post, generation: smt::generation() })
            }
            _ => None,
        }
    }

    /// True if this implication still refers to the arena that produced it.
    pub fn is_current(&self) -> bool {
        self.generation == smt::generation()
    }

    /// The antecedent, or `None` if the arena has been reset since.
    pub fn antecedent(&self) -> Option<Pred> {
        if self.is_current() {
            Some(self.pre)
        } else {
            None
        }
    }

    /// The consequent, or `None` if the arena has been reset since.
    pub fn consequent(&self) -> Option<Pred> {
        if self.is_current() {
            Some(self.post)
        } else {
            None
        }
    }

    /// Modus ponens for formulas: given a certificate for the antecedent,
    /// produce a certificate for the consequent. The kernel checks that the
    /// certificate really proves the antecedent before applying the rule.
    pub fn apply(self, premise: Certificate) -> Option<Certificate> {
        if !self.is_current() || !premise.is_current() {
            return None;
        }
        match smt::prove_equiv(premise.statement, self.pre) {
            Verdict::Valid => Some(Certificate {
                statement: self.post,
                generation: self.generation,
            }),
            _ => None,
        }
    }

    /// Cut: chain two proved implications.
    pub fn then(self, next: Implication) -> Option<Implication> {
        if !self.is_current() || !next.is_current() {
            return None;
        }
        match smt::prove_equiv(self.post, next.pre) {
            Verdict::Valid => Some(Implication {
                pre: self.pre,
                post: next.post,
                generation: self.generation,
            }),
            _ => None,
        }
    }
}

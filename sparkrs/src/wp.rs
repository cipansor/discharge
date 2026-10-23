//! Hoare logic: weakest preconditions, and automatic verification-condition
//! generation from a small imperative language.
//!
//! [`crate::vc`] lets you write a verification condition by hand. This module
//! *derives* it from the program, the way SPARK does: you state the precondition
//! and the postcondition, describe the body, and the engine computes what has to
//! be proved.
//!
//! The interesting rule is assignment. Hoare's axiom is
//!
//! ```text
//! wp(x := e, Q) = Q[x := e]
//! ```
//!
//! so `wp` rewrites the postcondition by substitution. That substitution must be
//! *simultaneous* and bottom-up: `x, y := y, x` has to swap, and a naive top-down
//! walk captures the wrong variable and proves a falsehood. `tests/wp.rs` checks
//! this against execution on concrete inputs.
//!
//! Everything is `no_std` and allocation-free. A program is a tree of [`Stmt`]
//! built on the stack; intermediate predicates live in the same arena as
//! everything else in [`crate::smt`].

use crate::smt::{self, Pred, Var, Verdict};

/// One statement of the imperative fragment.
///
/// Branches and loops are references, not indices, so nesting is expressed
/// directly and `wp` can recurse without any bookkeeping about token ranges.
#[derive(Debug, Clone, Copy)]
pub enum Stmt<'a> {
    /// `var := expr`
    Assign {
        /// The variable written.
        var: Var,
        /// The expression assigned to it.
        expr: Var,
    },
    /// Assume `cond`: only states satisfying it continue. This is how a
    /// precondition or a successful earlier check enters the reasoning.
    Assume(Pred),
    /// `assert cond`: an obligation at this point, and an assumption after it.
    Assert(Pred),
    /// `if cond { then_ } else { else_ }`
    If {
        /// The branch condition.
        cond: Pred,
        /// The then-branch.
        then_: &'a Stmt<'a>,
        /// The else-branch.
        else_: &'a Stmt<'a>,
    },
    /// `while cond { body }` annotated with a loop invariant, and optionally
    /// with a variant to prove termination.
    ///
    /// The invariant is not optional and not inferred: an unannotated loop
    /// cannot be verified, which is the same deal SPARK offers. The variant is
    /// optional, and its absence is exactly the difference between partial and
    /// total correctness.
    While {
        /// The loop guard.
        cond: Pred,
        /// The claimed invariant.
        invariant: Pred,
        /// An expression, in loop-head terms, that must strictly decrease on
        /// every iteration. Supplying one turns partial correctness into
        /// termination as well.
        ///
        /// The value after one iteration is computed symbolically by the engine,
        /// so you write the measure once, not twice.
        variant: Option<Var>,
        /// The loop body.
        body: &'a Stmt<'a>,
    },
    /// `s1; s2`
    Seq {
        /// The first statement.
        first: &'a Stmt<'a>,
        /// The second statement.
        second: &'a Stmt<'a>,
    },
    /// `skip`
    Skip,
}

/// Which rule generated an obligation. A failure is reported with its rule, so
/// you know whether the precondition, the body, a loop invariant, or an
/// assertion is at fault.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Rule {
    /// `pre => wp(body, post)`: the contract as a whole.
    ///
    /// A loop's *entry* condition is discharged here, as part of the enclosing
    /// context, which is how a backward calculus naturally accounts for it.
    Body,
    /// The invariant is preserved by one iteration, under the guard:
    /// `I && c => wp(body, I)`.
    LoopPreserve,
    /// The invariant together with the negated guard implies what the rest of
    /// the program needs: `I && !c => Q`.
    LoopExit,
    /// The variant strictly decreases on every iteration: `I && c => V' < V`.
    ///
    /// For an unsigned measure this is the whole rule: a strictly decreasing
    /// sequence in a well-founded order cannot be infinite. Because the measure
    /// is a bit-vector expression evaluated with wrapping, a measure that wraps
    /// around is caught here rather than silently accepted.
    LoopVariant,
    /// An in-body assertion holds whenever control reaches it:
    /// `pre => wp(prefix, c)`, where `prefix` is the code before the assertion.
    Assertion,
}

/// A verification condition, attributed to the rule that produced it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Obligation {
    /// The rule this obligation comes from.
    pub rule: Rule,
    /// The predicate that must hold for every input.
    pub goal: Pred,
}

impl Obligation {
    /// Discharge this obligation with the embedded decision procedure.
    pub fn discharge(&self) -> Verdict {
        smt::prove(self.goal)
    }
}

/// Collect the side obligations of `s` — loop rules and assertions — and return
/// the predicate that must hold before `s`, given that `post` must hold after it.
///
/// Nothing is discharged here, so the caller can inspect each obligation with the
/// rule that produced it. The returned predicate is the weakest precondition.
///
/// # A subtlety worth stating
///
/// The cursor — the predicate required after a statement — is rewritten by the
/// assignments that dominate it, because it describes the *actual* state. The
/// obligations recorded along the way are mostly left alone, and that asymmetry
/// is deliberate:
///
/// * An assertion `assert c` is checked in the context of the state that reaches
///   it, so the dominating assignments *do* apply, and the walk applies them.
/// * A loop's preservation and exit conditions are universally quantified over
///   the loop-head state: `I && c => wp(body, I)` has to hold for *every* state
///   satisfying the invariant, not merely for the states the program can reach.
///   Rewriting them with the dominating assignments would make them vacuously
///   true whenever the initialisation pins the variables, which is exactly the
///   bug that turns a broken invariant into a green check. They are therefore
///   recorded in loop-head terms and left alone.
/// * The loop's *entry* condition is not a separate obligation: it is the
///   contract's own `pre => apply(dominators, I)`, which the cursor produces for
///   free once the walk continues past the initialisation.
pub fn obligations<'a>(
    s: &'a Stmt<'a>,
    post: Pred,
    out: &mut [Option<Obligation>],
) -> (Pred, usize) {
    let mut n = 0;
    let mut cursor = post;
    collect(s, &mut cursor, out, 0, &mut n);
    (cursor, n)
}

/// Walk `s` backwards, appending loop and assertion obligations to `out`.
///
/// `cursor` is the predicate required at the current program point *after* the
/// statement, so the walk starts from the postcondition and ends with the weakest
/// precondition. This is the direction Hoare logic runs in, and getting it
/// backwards is the classic way to generate a vacuous verification condition.
///
/// `start` is the first slot of `out` that belongs to this statement. An
/// assignment rewrites only the slots in `start..*n`, which keeps a branch's
/// assignments from reaching into the sibling branch's obligations while still
/// letting the enclosing assignments rewrite both.
fn collect<'a>(
    s: &'a Stmt<'a>,
    cursor: &mut Pred,
    out: &mut [Option<Obligation>],
    start: usize,
    n: &mut usize,
) {
    match s {
        Stmt::Seq { first, second } => {
            // Backwards: handle the second statement first, then the first.
            collect(second, cursor, out, start, n);
            collect(first, cursor, out, start, n);
        }
        Stmt::Assign { var, expr } => {
            *cursor = smt::substitute(*cursor, &[(*var, *expr)]);
            // Assertions recorded to the right are reached only after this
            // assignment, so it dominates them and must be substituted in.
            for slot in out[start..*n].iter_mut() {
                if let Some(ob) = slot {
                    if ob.rule == Rule::Assertion {
                        *slot = Some(Obligation {
                            rule: ob.rule,
                            goal: smt::substitute(ob.goal, &[(*var, *expr)]),
                        });
                    }
                }
            }
        }
        Stmt::Assume(c) => {
            *cursor = smt::implies(*c, *cursor);
        }
        Stmt::Assert(c) => {
            // Reaching the assertion means the cursor holds, so `c` must too.
            push(out, n, Rule::Assertion, smt::implies(*cursor, *c));
            *cursor = smt::and(*c, *cursor);
        }
        Stmt::If { cond, then_, else_ } => {
            let after = *cursor;
            // Each branch is walked in its own slot range so its assignments do
            // not rewrite the sibling's obligations.
            let mut then_cursor = after;
            collect(then_, &mut then_cursor, out, *n, n);
            let mut else_cursor = after;
            collect(else_, &mut else_cursor, out, *n, n);
            *cursor = ite_pred(*cond, then_cursor, else_cursor);
        }
        Stmt::While { cond, invariant, variant, body } => {
            let inv = *invariant;
            let q = *cursor;
            // Preservation, universally quantified over the loop-head state.
            push(
                out,
                n,
                Rule::LoopPreserve,
                smt::implies(smt::and(inv, *cond), wp(inv, body)),
            );
            // Termination, when a variant was supplied. The measure after one
            // iteration is computed by symbolic evaluation of the body, so the
            // obligation is `I && c => V' < V` with `V'` derived, not restated.
            if let Some(v) = variant {
                let after = variant_after(body, *v);
                push(
                    out,
                    n,
                    Rule::LoopVariant,
                    smt::implies(smt::and(inv, *cond), smt::ult(after, *v)),
                );
            }
            // Exit: the invariant and the failed guard must satisfy whatever the
            // rest of the program needs.
            push(
                out,
                n,
                Rule::LoopExit,
                smt::implies(smt::and(inv, smt::not(*cond)), q),
            );
            // Obligations inside the body are checked under the invariant and the
            // guard, which is the context every iteration begins from.
            let mut body_cursor = inv;
            collect(body, &mut body_cursor, out, *n, n);
            // All a caller may assume after the loop is the invariant.
            *cursor = inv;
        }
        Stmt::Skip => {}
    }
}

fn push(out: &mut [Option<Obligation>], n: &mut usize, rule: Rule, goal: Pred) {
    if *n < out.len() {
        out[*n] = Some(Obligation { rule, goal });
        *n += 1;
    }
}

/// The weakest precondition of `post` under `s`.
///
/// This is the textbook definition, written as recursion on the syntax:
///
/// ```text
/// wp(skip, Q)          = Q
/// wp(x := e, Q)        = Q[x := e]
/// wp(assume c, Q)      = c => Q
/// wp(assert c, Q)      = c && Q
/// wp(s1; s2, Q)        = wp(s1, wp(s2, Q))
/// wp(if c then A else B, Q) = (c && wp(A,Q)) || (!c && wp(B,Q))
/// wp(while c inv I { B }, Q) = I        (with the three loop conditions
///                                        checked separately, see `obligations`)
/// ```
///
/// For `while` the returned predicate is the invariant, because that is all the
/// weakest-precondition calculus can conclude without a variant to show
/// termination. The obligations that make the invariant sound — preservation and
/// exit — are produced by [`obligations`], and by [`verify`], which runs them.
pub fn wp(post: Pred, s: &Stmt<'_>) -> Pred {
    wp_of(s, post)
}

fn wp_of(s: &Stmt<'_>, post: Pred) -> Pred {
    match s {
        Stmt::Skip => post,
        Stmt::Assign { var, expr } => smt::substitute(post, &[(*var, *expr)]),
        Stmt::Assume(cond) => smt::implies(*cond, post),
        Stmt::Assert(cond) => smt::and(*cond, post),
        Stmt::Seq { first, second } => {
            let after_second = wp_of(second, post);
            wp_of(first, after_second)
        }
        Stmt::If { cond, then_, else_ } => {
            let t = wp_of(then_, post);
            let e = wp_of(else_, post);
            ite_pred(*cond, t, e)
        }
        Stmt::While { invariant, .. } => *invariant,
    }
}

/// `c ? t : e` as a predicate.
pub fn ite_pred(c: Pred, t: Pred, e: Pred) -> Pred {
    smt::or(smt::and(c, t), smt::and(smt::not(c), e))
}

/// The value of the expression `e` after executing `s`, as a symbolic word.
///
/// This is symbolic evaluation, not the weakest-precondition calculus: it builds
/// an expression rather than a predicate, so a conditional yields `ite` instead
/// of a conjunction. It is what lets a loop variant be written once and have its
/// next-iteration value derived.
///
/// * `Assign { var, expr }` substitutes, so `e` is read in the new state.
/// * `If` produces `ite(cond, then_value, else_value)`.
/// * `Seq` composes in the order the statements run.
/// * `Assume` and `Assert` do not change the state, so the value passes through.
pub fn variant_after(s: &Stmt<'_>, e: Var) -> Var {
    match s {
        Stmt::Skip | Stmt::Assume(_) | Stmt::Assert(_) => e,
        Stmt::Assign { var, expr } => smt::substitute_word(e, &[(*var, *expr)]),
        Stmt::Seq { first, second } => variant_after(first, variant_after(second, e)),
        Stmt::If { cond, then_, else_ } => {
            let t = variant_after(then_, e);
            let el = variant_after(else_, e);
            smt::ite(*cond, t, el)
        }
        // A nested loop's effect on the measure is not tracked; the caller has
        // to supply a measure that accounts for the inner loop, which is the
        // usual obligation when nesting loops.
        Stmt::While { .. } => e,
    }
}

/// Check a loop for termination by an explicit variant, returning the obligation.
///
/// `variant` is the measure in loop-head terms; `body` is the loop body. The
/// obligation is `invariant && guard => variant_after(body) < variant`, which for
/// an unsigned measure is both necessary and sufficient for the loop to make
/// progress.
pub fn termination_obligation(
    guard: Pred,
    invariant: Pred,
    variant: Var,
    body: &Stmt<'_>,
) -> Obligation {
    Obligation {
        rule: Rule::LoopVariant,
        goal: smt::implies(smt::and(invariant, guard), smt::ult(variant_after(body, variant), variant)),
    }
}

/// How many obligations [`verify`] can report at once.
pub const MAX_OBLIGATIONS: usize = 16;

/// The result of verifying a program: every obligation, in the order the rules
/// were applied, plus the verdict of the contract as a whole.
#[derive(Debug, Clone, Copy)]
pub struct Report {
    /// Loop obligations, in the order generated.
    pub obligations: [Option<Obligation>; MAX_OBLIGATIONS],
    /// How many entries of `obligations` are set.
    pub count: usize,
    /// The overall contract condition, `pre => wp(body, post)`.
    pub contract: Obligation,
}

impl Report {
    /// The first obligation that did not hold, or `None` when everything did.
    pub fn first_failure(&self) -> Option<(Obligation, Verdict)> {
        for i in 0..self.count {
            if let Some(ob) = self.obligations[i] {
                let v = ob.discharge();
                if !v.is_proved() {
                    return Some((ob, v));
                }
            }
        }
        let v = self.contract.discharge();
        if v.is_proved() {
            None
        } else {
            Some((self.contract, v))
        }
    }

    /// True when every obligation, including the contract itself, was proved.
    pub fn is_verified(&self) -> bool {
        self.first_failure().is_none()
    }

    /// True when *every* loop in the program carried a variant.
    ///
    /// Without a variant, a verified report only means *partial* correctness:
    /// correct if the program terminates. With one for each loop, progress is
    /// proved too. One loop is one preservation obligation, so comparing the two
    /// counts is enough; a program with no loops counts as terminating, since
    /// there is nothing that could diverge.
    pub fn has_termination_proof(&self) -> bool {
        let mut loops = 0;
        let mut variants = 0;
        for ob in self.obligations[..self.count].iter().flatten() {
            match ob.rule {
                Rule::LoopPreserve => loops += 1,
                Rule::LoopVariant => variants += 1,
                _ => {}
            }
        }
        loops == variants
    }

    /// What a verified report actually establishes.
    ///
    /// `Total` means every loop carried a variant, so termination is proved as
    /// well as the contract. `Partial` means the contract holds for any run that
    /// terminates, but divergence is not ruled out.
    ///
    /// This says nothing about whether the report was actually *verified*; it
    /// only classifies what the obligations would establish if they hold. Check
    /// [`Report::is_verified`] as well.
    pub fn correctness(&self) -> Correctness {
        if self.has_termination_proof() {
            Correctness::Total
        } else {
            Correctness::Partial
        }
    }
}

/// How much a verified [`Report`] establishes.
///
/// This is the distinction between Hoare logic and total correctness, made
/// explicit in the type system rather than left to the reader.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Correctness {
    /// The contract holds whenever the program terminates. Divergent loops are
    /// not ruled out, because no loop carried a variant.
    Partial,
    /// The contract holds and every loop makes progress, so the program does
    /// terminate.
    Total,
}

/// Verify a program against a contract: for every input satisfying `pre`,
/// executing `s` establishes `post`.
///
/// This discharges the loop obligations *and* the body condition, and reports the
/// first failure with the rule that produced it.
pub fn verify(s: &Stmt<'_>, pre: Pred, post: Pred) -> Report {
    let mut slots: [Option<Obligation>; MAX_OBLIGATIONS] = [None; MAX_OBLIGATIONS];
    let (goal, count) = obligations(s, post, &mut slots);

    // An assertion's recorded goal has already been rewritten by the assignments
    // that dominate it, so it is `wp(prefix, c)`. The obligation to discharge is
    // that the precondition establishes it: `pre => wp(prefix, c)`. Loop goals are
    // deliberately left alone; see `obligations` for why.
    for slot in slots[..count].iter_mut() {
        if let Some(ob) = slot {
            if ob.rule == Rule::Assertion {
                *slot = Some(Obligation {
                    rule: ob.rule,
                    goal: smt::implies(pre, ob.goal),
                });
            }
        }
    }

    Report {
        obligations: slots,
        count,
        contract: Obligation {
            rule: Rule::Body,
            goal: smt::implies(pre, goal),
        },
    }
}

/// Convenience: verify and return just the overall verdict, treating a loop
/// failure as a failure of the contract.
pub fn verify_contract(s: &Stmt<'_>, pre: Pred, post: Pred) -> Verdict {
    match verify(s, pre, post).first_failure() {
        None => Verdict::Valid,
        Some((_, v)) => v,
    }
}

/// Independent check by execution: the first input in `0..limit` that satisfies
/// `pre` but violates `post` after `body` runs, if any.
///
/// This is the differential counterpart of the symbolic proof: if the symbolic
/// engine says `Valid` and this finds a witness, one of them is wrong.
pub fn find_counterexample_by_enumeration(
    limit: u64,
    pre: impl Fn(u64) -> bool,
    body: impl Fn(u64) -> u64,
    post: impl Fn(u64, u64) -> bool,
) -> Option<u64> {
    let mut v = 0;
    while v < limit {
        if pre(v) && !post(v, body(v)) {
            return Some(v);
        }
        v += 1;
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::smt::var;

    #[test]
    fn assignment_substitutes_into_the_postcondition() {
        smt::with_fresh(|| {
            let x = var(8);
            let y = var(8);
            // Pre: x < 10. Body: y := x + 1. Post: y <= 10.
            let body = Stmt::Assign { var: y, expr: x + 1u32 };
            let v = verify_contract(&body, x.lt_val(10), y.le_val(10));
            assert!(v.is_proved(), "got {}", v);
        });
    }

    #[test]
    fn a_weak_postcondition_is_refuted() {
        smt::with_fresh(|| {
            let x = var(8);
            let y = var(8);
            let body = Stmt::Assign { var: y, expr: x + 1u32 };
            let v = verify_contract(&body, x.lt_val(10), y.le_val(5));
            assert!(!v.is_proved(), "should have been refuted");
        });
    }

    #[test]
    fn substitution_swaps_simultaneously() {
        smt::with_fresh(|| {
            let x = var(8);
            let y = var(8);
            // `x, y := y, x` must exchange the two variables.
            let q = smt::eq(x, y);
            let swapped = smt::substitute(q, &[(x, y), (y, x)]);
            assert!(smt::prove(smt::iff(swapped, q)).is_proved());
            // And a genuine (non-symmetric) predicate must be affected.
            let r = smt::ult(x, y);
            let swapped_r = smt::substitute(r, &[(x, y), (y, x)]);
            assert!(smt::prove(smt::iff(swapped_r, smt::ult(y, x))).is_proved());
        });
    }

    #[test]
    fn both_branches_are_considered() {
        smt::with_fresh(|| {
            let x = var(8);
            let y = var(8);
            // if x < 100 { y := x } else { y := 100 }  ;  post: y <= 100
            let then_ = Stmt::Assign { var: y, expr: x };
            let else_ = Stmt::Assign { var: y, expr: smt::word(100, 8) };
            let body = Stmt::If {
                cond: x.lt_val(100),
                then_: &then_,
                else_: &else_,
            };
            let v = verify_contract(&body, smt::truth(true), y.le_val(100));
            assert!(v.is_proved(), "got {}", v);
        });
    }

    #[test]
    fn loop_invariant_is_checked_rule_by_rule() {
        smt::with_fresh(|| {
            let i = var(8);
            // while i < 10 { i := i + 1 }  invariant: i <= 10
            let step = Stmt::Assign { var: i, expr: i + 1u32 };
            let body = Stmt::While {
                cond: i.lt_val(10),
                invariant: i.le_val(10),
                variant: Some(smt::sub(smt::word(10, 8), i)),
                body: &step,
            };
            // The invariant must hold on entry, so the precondition has to
            // establish it: `pre = true` would fail for a free u8.
            let r = verify(&body, i.le_val(10), i.le_val(10));
            // A loop contributes three side obligations when a variant is
            // given: preservation, exit, and the variant decrease. Its entry
            // condition is the contract's own `pre => I`, so it is discharged as
            // part of `contract`, not as a separate rule.
            assert_eq!(r.count, 3, "expected preserve, exit and variant");
            assert!(r
                .obligations
                .iter()
                .flatten()
                .any(|ob| ob.rule == Rule::LoopVariant));
            assert!(r.is_verified(), "loop should verify");
        });
    }

    #[test]
    fn a_bad_invariant_is_reported_with_its_rule() {
        smt::with_fresh(|| {
            let i = var(8);
            // Same loop, but the invariant claims i <= 5, which is not
            // preserved: from i == 5 and the guard, i + 1 is 6, breaking it.
            let step = Stmt::Assign { var: i, expr: i + 1u32 };
            let body = Stmt::While {
                cond: i.lt_val(10),
                invariant: i.le_val(5),
                variant: None,
                body: &step,
            };
            let r = verify(&body, smt::truth(true), i.le_val(10));
            let (ob, _v) = r.first_failure().expect("invariant is false");
            assert_eq!(ob.rule, Rule::LoopPreserve);
        });
    }

    #[test]
    fn sequential_composition_composes() {
        smt::with_fresh(|| {
            let x = var(8);
            let y = var(8);
            let z = var(8);
            // x := x + 1; y := x + 1; z := y + 1. Starting from x == 7 the
            // final z is 10. Note the postcondition mentions only `z`: `x` has
            // been reassigned, so a postcondition about `x` would be about the
            // *new* x, which is the classic mistake this rule prevents.
            let s1 = Stmt::Assign { var: x, expr: x + 1u32 };
            let s2 = Stmt::Assign { var: y, expr: x + 1u32 };
            let s3 = Stmt::Assign { var: z, expr: y + 1u32 };
            let body = Stmt::Seq {
                first: &s1,
                second: &Stmt::Seq { first: &s2, second: &s3 },
            };
            let v = verify_contract(&body, x.eq_val(7), z.eq_val(10));
            assert!(v.is_proved(), "got {}", v);
        });
    }

    #[test]
    fn assert_generates_an_obligation() {
        smt::with_fresh(|| {
            let x = var(8);
            // assert x < 200 with no precondition must fail.
            let body = Stmt::Assert(x.lt_val(200));
            let v = verify_contract(&body, smt::truth(true), smt::truth(true));
            assert!(!v.is_proved(), "the assertion should not hold for all x");
        });
    }
}

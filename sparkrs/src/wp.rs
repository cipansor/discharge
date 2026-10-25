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

/// A procedure: a body together with the contract it must satisfy.
///
/// The body and the contract live in one value because a call is only sound when
/// both are known: the *contract* is what the caller may assume, and the *body* is
/// what has to be verified once. Keeping them together makes it impossible to
/// assume a postcondition nobody ever proved — the mistake that turns modular
/// verification into a way of proving anything you like.
#[derive(Debug, Clone, Copy)]
pub struct Proc<'a> {
    /// The name, used in diagnostics.
    pub name: &'static str,
    /// The callee's precondition. A call discharges an obligation to establish it.
    pub requires: Pred,
    /// The callee's postcondition. A call may assume it, and the body must
    /// establish it.
    pub ensures: Pred,
    /// The body. Verified by [`verify_proc`].
    pub body: &'a Stmt<'a>,
}

/// One statement of the imperative fragment.
///
/// Branches and loops are references, not indices, so nesting is expressed
/// directly and `wp` can recurse without any bookkeeping about token ranges.
/// A [`Stmt::Call`] refers to a [`Proc`], which carries its own contract, so a
/// program is a tree of statements plus the procedures they call.
#[derive(Debug, Clone, Copy)]
pub enum Stmt<'a> {
    /// `var := expr`
    Assign {
        /// The variable written.
        var: Var,
        /// The expression assigned to it.
        expr: Var,
    },
    /// A simultaneous multi-assignment, `v1, v2, ... := e1, e2, ...`.
    ///
    /// Every right-hand side is read in the *old* state, so this is a parallel
    /// assignment, not a sequence of single ones. It exists so that a memory write
    /// composes with verification-condition generation: [`crate::mem::Mem::store_binds`]
    /// produces the binding list for a store, and handing it here makes the write
    /// part of the program the engine reasons about.
    AssignMany {
        /// The `(target, expression)` pairs. Targets must be distinct; a repeated
        /// target would make the semantics depend on evaluation order, which is
        /// exactly what a simultaneous assignment is meant to rule out.
        binds: &'a [(Var, Var)],
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
    /// A call to a procedure, reasoned about through its contract.
    ///
    /// The body is *not* re-verified here. Instead the call is sound only if the
    /// caller has proved the callee's precondition at the point of the call, and
    /// after the call the caller may assume the callee's postcondition. That is
    /// what makes verification modular: a procedure is checked once against its
    /// contract, and every call site costs only the two implications.
    ///
    /// [`Stmt::frame`] must hold for the call to be sound at all; the constructor
    /// checks it.
    Call {
        /// The procedure being called.
        proc_: &'a Proc<'a>,
        /// `(global, local)` pairs. The callee's `requires` is evaluated over
        /// `local`, so a call *renames* the procedure's variables to the caller's
        /// arguments.
        ///
        /// The caller's variables that are *not* listed are treated as unchanged
        /// by the call, which is sound only when the callee cannot touch them. See
        /// [`Stmt::frame`] for the discipline that makes that true.
        actuals: &'a [(Var, Var)],
        /// Variables the callee may modify, in the callee's own names.
        ///
        /// `Stmt::frame` is derived from this list, so it does not have to be
        /// written out by hand and cannot drift from it.
        writes: &'a [Var],
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
    /// A call site establishes the callee's precondition:
    /// `wp(rest, post) => requires[actuals]`.
    ///
    /// Failing this means the caller is asking the callee to work in a state the
    /// callee does not accept. It is *not* a fault in the callee.
    CallRequires,
    /// A call could not be modelled at all: the callee may write a variable the
    /// caller did not name, so the caller's state after the call is unknown.
    ///
    /// This is not a proof failure but a modelling one, and it is reported rather
    /// than asserted so that a whole program can be checked in one run.
    CallFrame,
    /// The program has more side obligations than the report can hold, so some were
    /// not checked.
    ///
    /// This exists because silently dropping them is unsound. The cap is
    /// [`MAX_OBLIGATIONS`], and a dropped obligation is one nobody looked at — so a
    /// program could report `Total` while a failing `LoopExit` sat in the part that did
    /// not fit. Reporting the overflow as a *failure* is the only honest answer: the
    /// claim has to shrink to what was actually checked. See `obligations` for where the
    /// flag is raised, and `too_many_obligations_is_reported_not_swallowed` in
    /// `tests/wp.rs`.
    ObligationOverflow,
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
    let (goal, n, _) = obligations_checked(s, post, out);
    (goal, n)
}

/// [`obligations`], plus whether any claim-carrying obligation had to be dropped.
///
/// The flag is the whole point: [`MAX_OBLIGATIONS`] is a fixed-size buffer, and a
/// program larger than it must not be reported as verified on the strength of the part
/// that fit. [`verify`] turns a raised flag into a failing [`Rule::ObligationOverflow`]
/// obligation.
fn obligations_checked<'a>(
    s: &'a Stmt<'a>,
    post: Pred,
    out: &mut [Option<Obligation>],
) -> (Pred, usize, bool) {
    let mut n = 0;
    let mut overflow = false;
    let mut cursor = post;
    collect(s, &mut cursor, out, 0, &mut n, &mut overflow);
    (cursor, n, overflow)
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
    overflow: &mut bool,
) {
    match s {
        Stmt::Seq { first, second } => {
            // Backwards: handle the second statement first, then the first.
            collect(second, cursor, out, start, n, overflow);
            collect(first, cursor, out, start, n, overflow);
        }
        Stmt::Assign { var, expr } => {
            *cursor = smt::substitute(*cursor, &[(*var, *expr)]);
            // Assertions recorded to the right are reached only after this
            // assignment, so it dominates them and must be substituted in.
            for slot in out[start..*n].iter_mut() {
                if let Some(ob) = slot {
                    if ob.rule == Rule::Assertion || ob.rule == Rule::CallRequires {
                        *slot = Some(Obligation {
                            rule: ob.rule,
                            goal: smt::substitute(ob.goal, &[(*var, *expr)]),
                        });
                    }
                }
            }
        }
        Stmt::AssignMany { binds } => {
            debug_assert!(distinct_targets(binds), "AssignMany targets must be distinct");
            *cursor = smt::substitute(*cursor, binds);
            for slot in out[start..*n].iter_mut() {
                if let Some(ob) = slot {
                    if ob.rule == Rule::Assertion || ob.rule == Rule::CallRequires {
                        *slot = Some(Obligation {
                            rule: ob.rule,
                            goal: smt::substitute(ob.goal, binds),
                        });
                    }
                }
            }
        }
        Stmt::Call { proc_, actuals, writes } => {
            if !Stmt::frame(proc_, actuals, writes) {
                // Unmodelled, not merely unproved. Report it as an obligation that
                // can never hold, rather than asserting and aborting: a verifier
                // that panics on a bad input is a verifier you cannot run on a
                // program you do not yet trust.
                push_checked(out, n, overflow, Rule::CallFrame, smt::truth(false));
                *cursor = smt::truth(false);
                return;
            }
            // `requires[actuals]` is what the caller must establish *at this
            // point*, so it is recorded like an assertion: the assignments that
            // dominate it rewrite it, and `verify` wraps it with the precondition.
            // The rename is simultaneous, so `requires` and `ensures` are
            // substituted independently.
            push_checked(
                out,
                n,
                overflow,
                Rule::CallRequires,
                smt::substitute(proc_.requires, actuals),
            );
            // After the call, `ensures[actuals]` may be *assumed*. Assumption in a
            // backward calculus is implication: `ensures => Q`, not `ensures && Q`.
            // Conjoining would demand that the callee's result satisfy the caller's
            // postcondition on its own, which is not the rule and makes every
            // interesting call unprovable.
            //
            // The written variables are *havoced* first: each caller-side target is
            // renamed to a fresh variable, in both the assumption and the
            // continuation. Without this the two sides share a name, and then the
            // value the variable held *before* the call is mistaken for the value it
            // holds after — so `c := 99; c := bump(a)` would "prove" `c == 99`. The
            // fresh name is universally quantified by the prover, which is exactly
            // the right reading: the caller must be correct for *every* result the
            // contract permits.
            let renamed_ensures = smt::substitute(proc_.ensures, actuals);
            let (havoc, n_havoc) = havoc_writes(actuals, writes);
            let renamed_ensures = smt::substitute(renamed_ensures, &havoc[..n_havoc]);
            let continuation = smt::substitute(*cursor, &havoc[..n_havoc]);
            *cursor = smt::implies(renamed_ensures, continuation);
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
            collect(then_, &mut then_cursor, out, *n, n, overflow);
            let mut else_cursor = after;
            collect(else_, &mut else_cursor, out, *n, n, overflow);
            *cursor = ite_pred(*cond, then_cursor, else_cursor);
        }
        Stmt::While { cond, invariant, variant, body } => {
            let inv = *invariant;
            let q = *cursor;
            // Preservation, universally quantified over the loop-head state.
            push_checked(
                out,
                n,
                overflow,
                Rule::LoopPreserve,
                smt::implies(smt::and(inv, *cond), wp(inv, body)),
            );
            // Termination, when a variant was supplied. The measure after one
            // iteration is computed by symbolic evaluation of the body, so the
            // obligation is `I && c => V' < V` with `V'` derived, not restated.
            if let Some(v) = variant {
                let after = variant_after(body, *v);
                push_checked(
                    out,
                    n,
                    overflow,
                    Rule::LoopVariant,
                    smt::implies(smt::and(inv, *cond), smt::ult(after, *v)),
                );
            }
            // Exit: the invariant and the failed guard must satisfy whatever the
            // rest of the program needs.
            push_checked(
                out,
                n,
                overflow,
                Rule::LoopExit,
                smt::implies(smt::and(inv, smt::not(*cond)), q),
            );
            // Obligations inside the body are checked under the invariant and the
            // guard, which is the context every iteration begins from.
            let mut body_cursor = inv;
            collect(body, &mut body_cursor, out, *n, n, overflow);
            // All a caller may assume after the loop is the invariant.
            *cursor = inv;
        }
        Stmt::Skip => {}
    }
}

/// Fresh variables standing for the caller-side targets a call may write.
///
/// Returns a `(target, fresh)` substitution. Applying it to both the assumed
/// postcondition and the continuation keeps the pre-call and post-call values of a
/// written variable apart, which is what makes the call rule sound; see the comment
/// in [`collect`].
fn havoc_writes(actuals: &[(Var, Var)], writes: &[Var]) -> ([(Var, Var); MAX_CALL_ARGS], usize) {
    let mut out = [(Var::SENTINEL, Var::SENTINEL); MAX_CALL_ARGS];
    let mut n = 0;
    for w in writes.iter() {
        let Some((_, local)) = actuals.iter().find(|(g, _)| g == w) else {
            continue;
        };
        if out[..n].iter().any(|(t, _)| t == local) {
            continue;
        }
        if n < MAX_CALL_ARGS {
            out[n] = (*local, smt::var(smt::bits(*local)));
            n += 1;
        }
    }
    (out, n)
}

impl<'a> Stmt<'a> {
    /// Whether a call can be justified: every variable the callee may write must
    /// appear in the caller's `actuals`, so that the write has somewhere to land.
    ///
    /// This is the frame condition of a call, and it is the whole reason a call is
    /// sound to reason about locally. If the callee could write a variable the
    /// caller did not name, the caller would go on believing that variable's value
    /// — and no amount of proof about the callee's own contract would catch it.
    ///
    /// Returning `false` means the call is unmodelled, not merely unproved, so
    /// [`verify`] reports it as a failure rather than silently assuming the frame.
    ///
    /// # What the check rules out, and why each one is needed
    ///
    /// 0. **`writes` must be complete.** This is the one that matters most, and it
    ///    was missing at first. The declared frame is compared against the frame
    ///    *derived from the body* by [`writes`], and every derived write must be
    ///    declared. Without this, a caller could declare an empty frame for a callee
    ///    that clobbers a variable, and the engine would happily prove that the
    ///    variable survived — a proof about a program that does not exist. See
    ///    `under_declaring_the_frame_is_rejected` in `tests/call.rs`.
    ///
    /// 1. **Every write must have a target.** Otherwise the callee writes a
    ///    variable the caller does not name, the caller's state after the call is
    ///    unknown, and any proof built on it is unsound.
    /// 2. **The rename must be a function.** A repeated global would make the
    ///    substitution depend on which pair the engine happened to see last.
    /// 3. **No two writes may land on the same variable.** That is an
    ///    order-dependent simultaneous assignment, which is exactly what a
    ///    simultaneous rename is supposed to exclude.
    /// 4. **A write may not land on a variable the call also reads.** This one is
    ///    not obvious, and it is a genuine soundness hole rather than tidiness.
    ///    `ensures` is *assumed* after the call, so with `x -> a, r -> a` the
    ///    assumption becomes `a == a + a`, which silently forces `a == 0` on the
    ///    caller. The engine then proves anything at all about `a`. In-place
    ///    update is not expressible by a rename: the caller must capture the old
    ///    value into a temporary first, exactly as it must for a memory swap
    ///    (`oi := m[i]`). `tests/call.rs` pins this.
    ///
    /// # What is still trusted
    ///
    /// The *rename* is not checked for meaning. A caller who maps the callee's
    /// result onto the wrong variable passes every check here and still proves
    /// nonsense about the variable it actually reads. Likewise a contract whose body
    /// never established it will be believed by every caller. Neither is fixable by
    /// a smarter check: the remedy is [`verify_proc`] on every body, and the
    /// limitation is stated here rather than left to be discovered.
    pub fn frame(proc_: &Proc<'_>, actuals: &[(Var, Var)], declared: &[Var]) -> bool {
        // 0. The declared frame must cover the real one. This is a *soundness*
        //    requirement, not a tidiness one: an under-declared frame lets the
        //    caller assume a variable survived a call that overwrote it.
        let (derived, n_derived) = writes(proc_.body);
        if !derived[..n_derived].iter().all(|w| declared.contains(w)) {
            return false;
        }
        // Everything below is about the *shape* of the rename, which the derived
        // frame above already relies on to be meaningful.
        let writes = declared;
        // 1. Every write has a target in the caller.
        if !writes
            .iter()
            .all(|w| actuals.iter().any(|(global, _)| *global == *w))
        {
            return false;
        }
        // 2. The rename is a function.
        if !actuals
            .iter()
            .enumerate()
            .all(|(i, (g, _))| !actuals[..i].iter().any(|(earlier, _)| earlier == g))
        {
            return false;
        }
        // Split the images: written variables against read-only ones.
        let image = |g: &Var| actuals.iter().find(|(global, _)| global == g).map(|(_, l)| *l);
        let mut written: [Option<Var>; MAX_CALL_ARGS] = [None; MAX_CALL_ARGS];
        let mut n_written = 0;
        for w in writes {
            let Some(l) = image(w) else { return false };
            // 3. No two writes land on the same variable.
            if written[..n_written].iter().flatten().any(|prev| *prev == l) {
                return false;
            }
            if n_written < MAX_CALL_ARGS {
                written[n_written] = Some(l);
                n_written += 1;
            } else {
                return false;
            }
        }
        // 4. No write lands on a variable the call also reads.
        for (global, local) in actuals {
            if writes.contains(global) {
                continue;
            }
            if written[..n_written].iter().flatten().any(|prev| prev == local) {
                return false;
            }
        }
        true
    }
}

/// The last slot of a report's buffer is reserved for a report-level finding, so the
/// program's own obligations never fill it. See [`push_notice`].
fn program_limit(out: &[Option<Obligation>]) -> usize {
    out.len().saturating_sub(1)
}

/// Record an obligation about the program, if there is room below the reserved slot.
///
/// Used for assertions, where dropping one is not a soundness problem: a dropped
/// assertion still poisons the weakest precondition, so the contract obligation catches
/// it. Claim-carrying obligations use [`push_checked`], which reports the drop.
fn push(out: &mut [Option<Obligation>], n: &mut usize, rule: Rule, goal: Pred) {
    if *n < program_limit(out) {
        out[*n] = Some(Obligation { rule, goal });
        *n += 1;
    }
}

/// Record a report-level finding, which is allowed to use the reserved last slot.
///
/// The distinction matters: an overflow notice that is itself dropped by the full
/// buffer is worse than useless, because the report then looks clean. That is exactly
/// how the first attempt at this fix failed.
fn push_notice(out: &mut [Option<Obligation>], n: &mut usize, rule: Rule, goal: Pred) {
    if *n < out.len() {
        out[*n] = Some(Obligation { rule, goal });
        *n += 1;
    }
}

/// Like [`push`], but records that an obligation was dropped when the buffer is full.
///
/// Used for the obligations that carry a *claim*: a dropped loop rule or call rule is a
/// missing proof, and the report has to say so. Dropping one silently would let
/// `verified` mean "the obligations that fit were fine", which is not what a reader
/// takes it to mean.
fn push_checked(
    out: &mut [Option<Obligation>],
    n: &mut usize,
    overflow: &mut bool,
    rule: Rule,
    goal: Pred,
) {
    if *n < program_limit(out) {
        out[*n] = Some(Obligation { rule, goal });
        *n += 1;
    } else {
        *overflow = true;
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
        Stmt::AssignMany { binds } => smt::substitute(post, binds),
        Stmt::Call { proc_, actuals, writes } => {
            // Same rule as `collect`, including the havoc; see the comment there.
            let renamed = smt::substitute(proc_.ensures, actuals);
            let (havoc, n_havoc) = havoc_writes(actuals, writes);
            let renamed = smt::substitute(renamed, &havoc[..n_havoc]);
            let post = smt::substitute(post, &havoc[..n_havoc]);
            smt::implies(renamed, post)
        }
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

/// Whether every target in a simultaneous assignment is distinct.
///
/// A repeated target would make the result depend on evaluation order, which is
/// the one thing a simultaneous assignment is supposed to rule out. This is
/// quadratic, but only runs under `debug_assertions` and the lists are short.
fn distinct_targets(binds: &[(Var, Var)]) -> bool {
    for (i, (target, _)) in binds.iter().enumerate() {
        for (other, _) in binds.iter().skip(i + 1) {
            if target == other {
                return false;
            }
        }
    }
    true
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
        // A measure over a variable the call does not write survives it, because the
        // derived frame is complete. A measure over one the call *does* write has an
        // unknown value afterwards, so it is havoced: the resulting obligation then
        // mentions a fresh variable and cannot be discharged, which is the honest
        // answer — a call that writes the measure makes termination unprovable.
        Stmt::Call { actuals, writes, .. } => {
            let (havoc, n_havoc) = havoc_writes(actuals, writes);
            smt::substitute_word(e, &havoc[..n_havoc])
        }
        Stmt::Assign { var, expr } => smt::substitute_word(e, &[(*var, *expr)]),
        Stmt::AssignMany { binds } => smt::substitute_word(e, binds),
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
///
/// A [`Report`] actually carries one more slot than this, so that a report-level finding
/// such as [`Rule::ObligationOverflow`] always has somewhere to go. Without that extra
/// slot the overflow notice would itself be dropped by the full buffer — which is exactly
/// how this was missed the first time.
pub const MAX_OBLIGATIONS: usize = 16;

/// The most arguments a call may pass, so the frame check needs no allocator.
pub const MAX_CALL_ARGS: usize = 16;

/// The most variables one procedure may write.
pub const MAX_WRITES: usize = 16;

/// The caller's variables a call is guaranteed to leave unchanged.
///
/// This is the two-state story, and it turns out to need no `old` operator. A
/// variable the callee cannot write has the same value before and after the call, so
/// `old(v)` and `v` are the same thing — *provided* the frame is honest, which
/// [`Stmt::frame`] now checks. What was missing was not a way to write `old(v)` but a
/// way to **ask** whether `v` survives, because the engine was already assuming it
/// silently.
///
/// So this is a query, not an assumption. For a variable the callee does write, no
/// query can help: the caller must capture the entry value into a temporary before
/// the call, exactly as for a memory swap. `two_state_specs_via_a_caller_snapshot`
/// in `tests/call.rs` runs that pattern end to end.
///
/// The answer is computed from the *derived* frame, not the declared one, so a caller
/// cannot talk this query into a wrong answer.
///
/// The result is in the **caller's** names, which is what a caller can act on: the
/// arguments the call names but does not write. A caller variable the call never names
/// is also unchanged, by completeness of the derived frame; the query cannot enumerate
/// those, because it has never seen the caller's variable set.
pub fn unchanged_vars<'a>(
    proc_: &Proc<'_>,
    actuals: &[(Var, Var)],
    out: &'a mut [Var; MAX_CALL_ARGS],
) -> &'a [Var] {
    // The caller-side images of everything the body may write.
    let (derived, n) = writes(proc_.body);
    let mut n_changed = 0;
    let mut changed = [Var::SENTINEL; MAX_CALL_ARGS];
    for g in derived[..n].iter() {
        if let Some((_, l)) = actuals.iter().find(|(global, _)| global == g) {
            if !changed[..n_changed].contains(l) && n_changed < MAX_CALL_ARGS {
                changed[n_changed] = *l;
                n_changed += 1;
            }
        }
    }
    let mut k = 0;
    for (_, local) in actuals {
        // A variable the call names is unchanged exactly when its image is not
        // written. A caller variable the call does not name is unchanged because the
        // derived frame is complete, and `frame` refuses to model a call whose
        // declared frame disagrees with its body.
        if !changed[..n_changed].contains(local) && k < MAX_CALL_ARGS {
            out[k] = *local;
            k += 1;
        }
    }
    &out[..k]
}

/// Whether a call is guaranteed to leave the caller's variable `g` unchanged.
///
/// `g` is a **caller** variable, and it may be named by the call or not; both cases
/// are answered from the derived frame. See [`unchanged_vars`] for why this needs no
/// `old` operator.
///
/// The declared frame is deliberately *not* an argument. The answer comes from the
/// body, so a caller cannot talk the query into a wrong answer — and
/// [`Stmt::frame`] has already refused to model a call whose declared frame disagrees
/// with its body.
pub fn unchanged(proc_: &Proc<'_>, actuals: &[(Var, Var)], g: Var) -> bool {
    let (derived, n) = writes(proc_.body);
    !derived[..n].iter().any(|w| {
        actuals
            .iter()
            .any(|(global, local)| global == w && *local == g)
    })
}

/// The variables a statement may write, derived from its syntax.
///
/// This is the *real* frame of a statement, as opposed to the frame its author
/// claims. The distinction is the whole point: a caller that under-declares what a
/// callee writes can make the engine believe a variable survived a call that
/// clobbered it, which is unsound. [`Stmt::frame`] therefore compares the two.
///
/// A write inside a branch or a loop still counts. The frame rule is conservative
/// by construction — "may write" is what matters, not "does write on this path" —
/// because a caller cannot know which path was taken.
///
/// A nested call contributes the caller-side images of its callee's writes, mapped
/// through that call's `actuals`.
pub fn writes(s: &Stmt<'_>) -> ([Var; MAX_WRITES], usize) {
    // Slot 0 is never a real variable: `var()` starts indices at 0, but a
    // sentinel is all the initialisation needs and it is overwritten before use.
    let mut out = [Var::SENTINEL; MAX_WRITES];
    let mut n = 0;
    collect_written(s, &mut out, &mut n);
    (out, n)
}

fn note_written(out: &mut [Var; MAX_WRITES], n: &mut usize, v: Var) {
    if out[..*n].contains(&v) {
        return;
    }
    if *n < MAX_WRITES {
        out[*n] = v;
        *n += 1;
    }
}

fn collect_written(s: &Stmt<'_>, out: &mut [Var; MAX_WRITES], n: &mut usize) {
    match s {
        Stmt::Assign { var, .. } => note_written(out, n, *var),
        Stmt::AssignMany { binds } => {
            for (v, _) in binds.iter() {
                note_written(out, n, *v);
            }
        }
        Stmt::Seq { first, second } => {
            collect_written(first, out, n);
            collect_written(second, out, n);
        }
        Stmt::If { then_, else_, .. } => {
            collect_written(then_, out, n);
            collect_written(else_, out, n);
        }
        Stmt::While { body, .. } => collect_written(body, out, n),
        Stmt::Call { proc_, actuals, .. } => {
            // The callee's writes land on whichever caller variables its `actuals`
            // name. A callee write with no image in the caller is dropped here, and
            // the *enclosing* frame check is what rejects that situation.
            let (inner, m) = writes(proc_.body);
            for g in inner[..m].iter() {
                if let Some((_, l)) = actuals.iter().find(|(global, _)| global == g) {
                    note_written(out, n, *l);
                }
            }
        }
        Stmt::Assume(_) | Stmt::Assert(_) | Stmt::Skip => {}
    }
}

/// The result of verifying a program: every obligation, in the order the rules
/// were applied, plus the verdict of the contract as a whole.
#[derive(Debug, Clone, Copy)]
pub struct Report {
    /// Loop, assertion and call obligations, in the order generated, plus one spare
    /// slot at the end for a report-level finding. See [`MAX_OBLIGATIONS`].
    pub obligations: [Option<Obligation>; MAX_OBLIGATIONS + 1],
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

    /// True when every loop in the program carried a variant **that was proved to
    /// decrease**.
    ///
    /// Without a variant, a verified report only means *partial* correctness: correct
    /// if the program terminates. With a discharged variant for each loop, progress is
    /// proved too. A program with no loops counts as terminating, since there is
    /// nothing that could diverge.
    ///
    /// The variant obligations must be *discharged*, not merely present. A variant that
    /// is supplied but does not decrease proves nothing, so a report is `Total` only
    /// when each one was established. This was a real defect: counting variants instead
    /// of discharging them let a report call itself `Total` on the strength of a measure
    /// it had failed to justify. `a_variant_that_does_not_decrease_is_not_termination`
    /// in `tests/wp.rs` pins it.
    pub fn has_termination_proof(&self) -> bool {
        let mut loops = 0;
        let mut variants = 0;
        for ob in self.obligations[..self.count].iter().flatten() {
            match ob.rule {
                Rule::LoopPreserve => loops += 1,
                // Present *and* proved: an obligation that did not discharge is not
                // evidence of progress.
                Rule::LoopVariant if ob.discharge().is_proved() => variants += 1,
                _ => {}
            }
        }
        loops == variants
    }

    /// What a verified report actually establishes.
    ///
    /// `Total` means every loop carried a variant that was proved to decrease, so
    /// termination is established as well as the contract. `Partial` means the contract
    /// holds for any run that terminates, but divergence is not ruled out.
    ///
    /// For a report that *is* verified, this is the honest classification. For one that
    /// is not, read it as the best case: it classifies what the obligations would
    /// establish if they all held. Check [`Report::is_verified`] first, or use
    /// [`Report::establishes`], which asks both questions at once.
    pub fn correctness(&self) -> Correctness {
        if self.has_termination_proof() {
            Correctness::Total
        } else {
            Correctness::Partial
        }
    }

    /// The single question a caller usually means to ask: what, if anything, did this
    /// report actually establish?
    ///
    /// [`Report::is_verified`] and [`Report::correctness`] answer two halves of that
    /// question, and asking only one of them is easy to get wrong — a `Total` claim
    /// from an unverified report is worth nothing. This asks both, so the answer cannot
    /// be read off the wrong half.
    pub fn establishes(&self) -> Established {
        if !self.is_verified() {
            Established::Nothing
        } else if self.has_termination_proof() {
            Established::Total
        } else {
            Established::Partial
        }
    }
}

/// What a [`Report`] actually established, as one value.
///
/// [`Report::establishes`] produces this. It exists because "is it verified?" and
/// "does it cover termination?" are two questions whose answers are only useful
/// together, and a caller who reads one of them in isolation can conclude the wrong
/// thing from a report that failed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Established {
    /// Nothing: the report was not verified, so no claim was established. The other two
    /// variants say nothing about a report in this state, which is why this one exists.
    Nothing,
    /// The contract holds for any run that terminates; divergence is not ruled out.
    Partial,
    /// The contract holds and every loop was proved to make progress.
    Total,
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
    let mut slots: [Option<Obligation>; MAX_OBLIGATIONS + 1] = [None; MAX_OBLIGATIONS + 1];
    let (goal, mut count, overflow) = obligations_checked(s, post, &mut slots);

    // An assertion's recorded goal has already been rewritten by the assignments
    // that dominate it, so it is `wp(prefix, c)`. The obligation to discharge is
    // that the precondition establishes it: `pre => wp(prefix, c)`. Loop goals are
    // deliberately left alone; see `obligations` for why.
    for slot in slots[..count].iter_mut() {
        if let Some(ob) = slot {
            if ob.rule == Rule::Assertion || ob.rule == Rule::CallRequires {
                *slot = Some(Obligation {
                    rule: ob.rule,
                    goal: smt::implies(pre, ob.goal),
                });
            }
        }
    }

    // A dropped obligation is a claim that was never checked. Record it as a failure
    // rather than letting `verified` mean "the ones that fit were fine": the report has
    // to shrink to what was actually proved. `false` is the goal because the obligation
    // is not about the program's state — it is about the report's own completeness.
    if overflow {
        push_notice(&mut slots, &mut count, Rule::ObligationOverflow, smt::truth(false));
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

/// Verify one procedure against its own contract: for every input satisfying
/// `p.requires`, executing `p.body` establishes `p.ensures`.
///
/// This is the "once" half of modular verification. Do it for every procedure in
/// the program, then [`verify_modular`] can reason about the calls without looking
/// at any body again.
///
/// It is deliberately thin. `verify_proc` and [`verify`] differ only in which
/// predicate they take as the precondition, and that is the point: a procedure is
/// nothing more than a body with a contract attached, so it must not need a
/// different prover.
pub fn verify_proc(p: &Proc<'_>) -> Report {
    verify(p.body, p.requires, p.ensures)
}

/// The report for a program, with the *call obligations* attached to the
/// procedures they belong to.
///
/// [`verify`] checks a program's own loops and assertions. A call adds two things:
/// the obligation that the caller establishes the callee's precondition (checked
/// here), and the right to assume the callee's postcondition (which is sound only
/// if someone verified the callee's body — see [`verify_proc`]).
///
/// The obligation to establish a precondition is attached to the *caller*, not the
/// callee, because that is whose fault a failure is. This function returns the
/// caller's report; the callee's obligations come from [`verify_proc`].
pub fn verify_modular(s: &Stmt<'_>, pre: Pred, post: Pred) -> Report {
    verify(s, pre, post)
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

//! Symbolic execution of MIR, one path at a time.
//!
//! The executor walks basic blocks, keeping a *path condition* and a map from
//! MIR locals to symbolic values. At each `assert` it asks the engine whether
//! the negated condition is reachable under the path condition; at each `return`
//! it asks whether the postcondition holds. Nothing here trusts the code: the
//! only way to get a `Valid` out is for the engine to prove the obligation for
//! *every* input on *every* explored path.
//!
//! # Bounded, like every bounded checker
//!
//! Two budgets keep this from running forever, and both are reported rather than
//! hidden:
//!
//! * [`DEFAULT_UNWIND`] — a back edge taken more than this many times ends the
//!   path as unknown. Loops are *not* assumed to exit.
//! * [`DEFAULT_INLINE_DEPTH`] — calls into the same dump are inlined to this
//!   depth; deeper calls make the path unknown.
//!
//! A third, implicit budget is the engine's own BDD arena. When it fills, the
//! verdict is `Unknown` and the obligation is left open. Every one of these
//! failures lands on the "I could not decide" side, never on "valid".

use std::collections::BTreeMap;

use crate::mir::parse::{
    BinOp, Block, Callee, Const, MirFn, MirProgram, Operand, Place, Proj, Rvalue, Stmt, Term, Ty, UnOp,
};
use crate::smt::{self, Pred, Var, Verdict};

/// How many times a back edge may be taken before a path is abandoned as
/// unknown. Nine is enough for the shift-amount and bounds loops that dominate
/// the interesting safety cases, and small enough to stay fast.
pub const DEFAULT_UNWIND: u32 = 9;

/// How deep same-dump calls are inlined.
pub const DEFAULT_INLINE_DEPTH: u32 = 4;

/// How many paths one function may explore before the search is abandoned.
///
/// `DEFAULT_UNWIND` bounds each *loop*, but a function can still generate an
/// unbounded number of paths without any single loop exceeding its bound: every
/// branch inside an unwound loop multiplies the path count, and the engine's
/// BDD cost per path grows with the path condition. Measured on
/// `while i < n { if i % 2 == 0 { c += 1; } i += 1; }` the search was still
/// running after 170 seconds with only two paths reported unknown -- it was not
/// looping forever, but it had no way to stop either.
///
/// That matters because the frontend's contract, stated in `mir/mod.rs`, is
/// that a cutoff is reported as a cutoff and a path is never assumed to exit.
/// A search that never returns cannot report anything, so the promise needs a
/// bound on *paths*, not just on loop iterations. Reaching this budget marks
/// the function incomplete, exactly like an unwound loop: the obligations found
/// so far stand, and the un-explored remainder is named rather than guessed at.
///
/// The value is calibrated against cost, not against a round number. The same
/// function above took 16s at 200 paths and was still running after 90s at
/// 2000, because each path's BDD is larger than the last -- so a larger budget
/// buys no extra coverage, only latency. Sixty-four keeps the worst case in the
/// low seconds while still deciding everything the shipped corpora decide: the
/// corpus scoreboard is unchanged with this bound and with none.
///
/// Loops carrying an `invariant:` no longer reach this budget at all -- they are
/// cut rather than unwound -- so this bound now governs only the loops that have
/// no invariant to prove them with.
pub const DEFAULT_PATH_BUDGET: usize = 64;

/// A symbolic value.
///
/// `Unknown` propagates: any operation on it stays unknown, and a path that
/// returns or asserts an unknown value is not evidence of anything. That is the
/// single rule that keeps this frontend honest — there is no place where an
/// unmodelled construct is quietly given a convenient meaning.
#[derive(Clone, Copy, Debug)]
pub enum Val {
    /// A bit-vector of a known width.
    Sym(Var),
    Bool(Pred),
    /// An aggregate (array or tuple). Its parts live in the environment's
    /// `elems`/`fields` maps, keyed by the aggregate's own local.
    Agg,
    Unknown,
}

/// What an obligation is about, for the report.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ObligationKind {
    /// A rustc-emitted panic condition (overflow, divide by zero, shift, bounds).
    Panic {
        /// The message `rustc` attached to the `assert`, which names the
        /// operation that would fail.
        message: String,
    },
    /// The declared postcondition at a `return`.
    Postcondition,
    /// An `unreachable` that the path condition can reach.
    Unreachable,
    /// The precondition is unsatisfiable, so the contract proves nothing.
    VacuousPrecondition,
    /// The declared loop invariant holds the first time the loop head is
    /// reached. This is the base case of the induction.
    LoopInvariantInit,
    /// The declared loop invariant is left true by one iteration. This is the
    /// step of the induction.
    LoopInvariantPreserve,
}

impl std::fmt::Display for ObligationKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ObligationKind::Panic { message } => write!(f, "panic: {message}"),
            ObligationKind::Postcondition => write!(f, "postcondition"),
            ObligationKind::Unreachable => write!(f, "reachable `unreachable`"),
            ObligationKind::VacuousPrecondition => write!(f, "vacuous precondition"),
            ObligationKind::LoopInvariantInit => write!(f, "loop invariant holds on entry"),
            ObligationKind::LoopInvariantPreserve => write!(f, "loop invariant preserved"),
        }
    }
}

/// One obligation found while walking a path.
#[derive(Clone, Debug)]
pub struct Obligation {
    /// What the obligation is about.
    pub kind: ObligationKind,
    /// The engine's answer. `Valid` means proved; `Counterexample` carries the
    /// failing input.
    pub verdict: Verdict,
}

impl Obligation {
    /// Whether this obligation was discharged.
    ///
    /// The polarity is *not* the same for every kind, and reading it as one is a
    /// soundness hole in either direction:
    ///
    /// * A [`ObligationKind::Postcondition`] is discharged when it is `Valid`:
    ///   the predicate holds for every input. `Unsat` here is the strongest
    ///   possible failure — the postcondition is false for every input.
    /// * A [`ObligationKind::Panic`] is discharged only when it is `Unsat`: the
    ///   query asks "can this panic happen", so `Unsat` means it cannot.
    ///   `Counterexample` means it can, on the inputs it names; `Valid` means it
    ///   happens for every input — the worst case, and the one that has no
    ///   counterexample to show.
    /// * An [`ObligationKind::Unreachable`] is the same query shape as a panic:
    ///   `Unsat` proves the `unreachable` is never reached.
    /// * A [`ObligationKind::VacuousPrecondition`] is discharged when it is
    ///   *refuted*: some input satisfies the precondition. Its `Unsat` verdict is
    ///   the finding, not a proof.
    /// * Both [`ObligationKind::LoopInvariantInit`] and
    ///   [`ObligationKind::LoopInvariantPreserve`] are discharged when they are
    ///   `Valid`: the query asks "does the invariant hold here, for every input
    ///   that reaches this point", so `Valid` is the proof and a `Counterexample`
    ///   is a real input that breaks the invariant. Reading them as a panic query
    ///   (discharged on `Unsat`) would invert the answer, which is exactly the
    ///   mistake the per-kind polarity exists to prevent.
    ///
    /// `Unknown` is never discharged. A caller that tests only
    /// [`Verdict::is_proved`] gets the postcondition case right and every other
    /// case backwards, which is why this method exists.
    pub fn is_discharged(&self) -> bool {
        match self.kind {
            ObligationKind::Postcondition
            | ObligationKind::LoopInvariantInit
            | ObligationKind::LoopInvariantPreserve => self.verdict.is_proved(),
            ObligationKind::Panic { .. } | ObligationKind::Unreachable => {
                matches!(self.verdict, Verdict::Unsat)
            }
            ObligationKind::VacuousPrecondition => {
                !matches!(self.verdict, Verdict::Unsat | Verdict::Unknown)
            }
        }
    }

    /// A concrete input that falsifies the intent, when one exists.
    ///
    /// For a postcondition, a `Counterexample` is a real failing input. For a
    /// panic or an `unreachable`, the failing case is a `Counterexample` too —
    /// the inputs on which the panic or the `unreachable` is reached. The two
    /// failures with no witness are the *opposite* verdicts of each other, and
    /// [`Obligation::failure_detail`] is what tells them apart.
    pub fn failure_witness(&self) -> Option<&crate::smt::Cex> {
        match &self.verdict {
            Verdict::Counterexample(c) => Some(c),
            _ => None,
        }
    }

    /// A one-line diagnosis of why this obligation was not discharged.
    ///
    /// The witness alone is not enough, because the two kinds fail on *opposite*
    /// verdicts and both leave no counterexample:
    ///
    /// * An `Unsat` postcondition holds for **no** input — the strongest failure.
    /// * A `Valid` panic holds for **every** input — the panic always fires.
    ///
    /// Rendering both as "holds for every input" reverses the first: it describes
    /// an impossible postcondition as a universal truth, which is the opposite of
    /// the finding. So the string is built per kind and per verdict, and the
    /// `Unsat` postcondition says what actually happened.
    pub fn failure_detail(&self) -> String {
        match &self.verdict {
            Verdict::Counterexample(c) => c.to_string(),
            Verdict::Valid => match self.kind {
                // A panic query is `path => can_happen`; `Valid` means it always
                // happens, and there is no single witness to name.
                ObligationKind::Panic { .. } | ObligationKind::Unreachable => {
                    "holds for every input (the failure fires on all of them)".to_string()
                }
                // A postcondition or invariant query is `path => P`; `Valid` is
                // the *pass* case, so reaching here with a non-discharged
                // obligation would be a classifier bug. Say so rather than guess.
                ObligationKind::Postcondition
                | ObligationKind::VacuousPrecondition
                | ObligationKind::LoopInvariantInit
                | ObligationKind::LoopInvariantPreserve => {
                    "invalid: a `Valid` verdict is a discharge for this kind".to_string()
                }
            },
            Verdict::Unsat => match self.kind {
                // `path => post` false on every input: the postcondition holds for
                // none of them. This is the case the old shared string got wrong.
                ObligationKind::Postcondition => {
                    "the postcondition holds for no input (false on every input)".to_string()
                }
                // `path => I` false on every input: the invariant can never be
                // established (or re-established), so the loop proves nothing.
                ObligationKind::LoopInvariantInit | ObligationKind::LoopInvariantPreserve => {
                    "the invariant holds for no input (false on every input)".to_string()
                }
                // The good answer for a reachability query, so this is a discharge.
                ObligationKind::Panic { .. } | ObligationKind::Unreachable => {
                    "invalid: an `Unsat` verdict is a discharge for this kind".to_string()
                }
                // The precondition describes no input, so the contract is vacuous.
                ObligationKind::VacuousPrecondition => {
                    "no input satisfies the precondition (the contract is vacuous)".to_string()
                }
            },
            Verdict::Unknown => "the engine could not decide this obligation".to_string(),
        }
    }
}

/// The result of verifying one function.
#[derive(Clone, Debug, Default)]
pub struct MirReport {
    /// The function these obligations belong to.
    pub function: String,
    /// Every obligation found, with the engine's answer for each.
    pub obligations: Vec<Obligation>,
    /// Paths that ended in a budget cutoff or an unmodelled operation. Non-empty
    /// means the verification is *incomplete*, whatever the obligations say.
    pub unknown_paths: Vec<String>,
    /// Paths explored to a `return`.
    pub returned_paths: usize,
}

impl MirReport {
    /// True when every obligation was discharged and no path was left unknown.
    ///
    /// "Discharged" is per-kind — see [`Obligation::is_discharged`]. A panic is
    /// discharged by an `Unsat` query, a postcondition by a `Valid` one, and a
    /// vacuous-precondition check by a refutation. Testing `is_proved` on every
    /// obligation instead would count a panic that happens for *every* input as a
    /// proof, and a postcondition that holds for *no* input as one too.
    pub fn is_proved(&self) -> bool {
        self.unknown_paths.is_empty() && self.obligations.iter().all(|o| o.is_discharged())
    }

    /// The first obligation that was not discharged and that the engine could
    /// decide, i.e. a definite failure rather than an open one.
    ///
    /// Returns the obligation itself so the caller can ask it for the kind, the
    /// witness, and the diagnosis without re-deriving which obligation it was.
    /// A failure outranks incompleteness, so this is the first thing a caller
    /// should look at.
    pub fn first_failure(&self) -> Option<&Obligation> {
        self.obligations
            .iter()
            .find(|o| !o.is_discharged() && !matches!(o.verdict, Verdict::Unknown))
    }

    /// The first counterexample found, if any obligation has one to show.
    pub fn counterexample(&self) -> Option<(&ObligationKind, &crate::smt::Cex)> {
        self.obligations.iter().find_map(|o| o.failure_witness().map(|c| (&o.kind, c)))
    }

    /// Panics that were proved impossible: an `Unsat` "can this panic" query.
    pub fn panics_ruled_out(&self) -> usize {
        self.obligations
            .iter()
            .filter(|o| matches!(o.kind, ObligationKind::Panic { .. }) && o.is_discharged())
            .count()
    }

    /// Obligations the engine could not decide.
    pub fn undecided(&self) -> usize {
        self.obligations
            .iter()
            .filter(|o| matches!(o.verdict, Verdict::Unknown))
            .count()
    }
}

impl std::fmt::Display for MirReport {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(
            f,
            "{}: {} obligation(s), {} path(s) returned",
            self.function,
            self.obligations.len(),
            self.returned_paths
        )?;
        for o in &self.obligations {
            writeln!(f, "  [{}] {}", o.verdict, o.kind)?;
        }
        for u in &self.unknown_paths {
            writeln!(f, "  [unknown] {u}")?;
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Environment
// ---------------------------------------------------------------------------

/// Local-to-symbolic environment, with side maps for aggregate parts.
#[derive(Clone, Debug)]
struct Env {
    locals: BTreeMap<u32, Val>,
    /// Array elements, keyed by (local, index).
    elems: BTreeMap<(u32, u64), Val>,
    /// Tuple fields, keyed by (local, field).
    fields: BTreeMap<(u32, u32), Val>,
}

impl Env {
    fn new() -> Env {
        Env { locals: BTreeMap::new(), elems: BTreeMap::new(), fields: BTreeMap::new() }
    }

    fn get(&self, p: &Place) -> Val {
        let mut cur = match self.locals.get(&p.local) {
            Some(v) => *v,
            None => return Val::Unknown,
        };
        for pr in &p.proj {
            cur = match pr {
                Proj::Field(i) => *self.fields.get(&(p.local, *i)).unwrap_or(&Val::Unknown),
                Proj::Index(i) => *self.elems.get(&(p.local, *i)).unwrap_or(&Val::Unknown),
            };
        }
        cur
    }

    fn set(&mut self, p: &Place, v: Val) {
        if p.proj.is_empty() {
            self.locals.insert(p.local, v);
            return;
        }
        match p.proj.as_slice() {
            [Proj::Field(i)] => {
                self.fields.insert((p.local, *i), v);
            }
            [Proj::Index(i)] => {
                self.elems.insert((p.local, *i), v);
            }
            // A nested projection would need a place tree. Modelling it
            // approximately would be a soundness hole, so it is dropped and a
            // later read of that place yields `Unknown`.
            _ => {}
        }
    }
}

/// A frame on the inlining stack.
#[derive(Clone, Debug)]
struct Frame {
    /// Index into `MirProgram::fns` of the function being executed.
    func: usize,
    /// Where the caller resumes once this frame returns.
    ret_target: usize,
    /// The caller place that receives the return value, if any.
    ret_dest: Option<Place>,
    /// The caller's environment, saved when the call was entered.
    ///
    /// Each function numbers its MIR locals from `_0`, so a local index means
    /// something only inside the function that declared it. Entering a call
    /// therefore has to build a fresh `Env` for the callee, and the caller's own
    /// must be put aside: without this, resuming the caller would use the
    /// callee's locals, so a caller that saved `a` in `_3`, called `g(b)`, and
    /// returned `_3` would read `g`'s `_3` instead. That made a false
    /// postcondition provable, which is the failure mode this crate exists to
    /// avoid.
    saved_env: Option<Env>,
    /// The caller's frame, or `None` for the root.
    caller: Option<Box<Frame>>,
}

/// One state on the worklist.
#[derive(Clone, Debug)]
struct State {
    /// The current function, plus the chain of callers to resume into.
    frame: Frame,
    block: usize,
    path: Pred,
    env: Env,
    /// Back-edge counts per (function index, block), for the unwind bound.
    visits: BTreeMap<(usize, usize), u32>,
    /// How many calls deep this path currently is.
    depth: u32,
    /// The loop this path is currently inside, when it was cut by an invariant.
    ///
    /// `None` for every path in a function with no invariant. When set, the
    /// header is assumed to satisfy the invariant on entry and the back edge is
    /// checked against it instead of being unwound.
    cut: Option<Cut>,
}

/// A loop that is proved by its invariant rather than by unwinding.
///
/// The shape is the standard one for a CFG. The invariant is *asserted* on every
/// edge into the header -- that single obligation covers both induction cases,
/// because it is `path => I` and the path condition already carries the guard:
///
/// * From outside the loop, `path => I` is *initialisation*: the invariant holds
///   the first time the header is reached.
/// * From a back edge, it is *preservation*: assuming `I` at the head, one more
///   iteration leaves it true.
///
/// The two differ only in what happens next. After a back edge the edge is *not*
/// followed: the assertion has closed the induction, and re-entering would be
/// the unwinding this exists to avoid. After an entry edge the header continues
/// with `I` conjoined onto the path, so the exit edge inherits `I && !guard` --
/// which is what a postcondition is entitled to assume after a loop.
#[derive(Clone, Debug)]
struct Cut {
    /// Index of the function the loop belongs to. An inlined callee numbers its
    /// own blocks from `bb0`, so without this a callee's `bb1` could be mistaken
    /// for the caller's loop header and checked against the caller's invariant.
    func: usize,
    /// The loop header. An edge into it asserts the invariant.
    header: usize,
    /// Blocks with an edge back to `header`. An edge from one of these asserts
    /// the invariant and then stops, rather than re-entering the header.
    back_edges: Vec<usize>,
    /// The locals the loop can write, over-approximated.
    ///
    /// At the header these are replaced by fresh values before the invariant is
    /// assumed. This is not an optimisation, it is what makes the proof sound:
    /// without it the exit edge would only ever be taken from the state of the
    /// *first* iteration, so a loop that corrupts the return value on a later
    /// iteration would still verify. An invariant that is true on entry but too
    /// weak to imply the postcondition would then pass -- measured, and it did.
    ///
    /// Over-approximating is safe in the one direction that matters: havocing a
    /// local the loop does not actually write only discards information, so it
    /// can turn a proof into an open obligation but never an open obligation
    /// into a proof.
    havoc: Vec<u32>,
    /// The invariant's text, re-evaluated in the post-state of each incoming
    /// edge, because only the executor knows what the locals hold there.
    text: String,
}

/// Verify one function from a parsed program.
///
/// `pre` is the declared precondition (or `None` for `true`); `post` is the
/// declared postcondition over the return value, or `None` to check only panic
/// freedom. Both are built by the caller, which is where the source-level
/// `#[requires]` / `#[ensures]` attributes become symbolic predicates.
///
/// The postcondition is fallible on purpose. An `ensures` the parser cannot read
/// must not become `true`, because then the function would verify with no
/// postcondition checked at all -- a false contract passing as a true one. An
/// error here is turned into an unmodelled path, which is reported rather than
/// discharged.
///
/// `invariant` is the loop induction hypothesis, when the source supplied one.
/// It is the *text* of the `invariant:` clause; the executor resolves the names
/// against the current symbolic values itself, because only it knows what each
/// local holds at the loop head. Passing text rather than a pre-built predicate
/// is what makes preservation expressible: the same text is evaluated a second
/// time in the post-state of one iteration, and a predicate built once could not
/// see that state. Without an invariant a loop is unwound, as before.
pub fn verify_fn<F>(
    prog: &MirProgram,
    f: &MirFn,
    pre: Option<Pred>,
    post: Option<F>,
    invariant: Option<&str>,
) -> MirReport
where
    F: Fn(Var) -> Result<Pred, String>,
{
    let mut report = MirReport { function: f.name.clone(), ..Default::default() };

    // Does the precondition even describe an input? An unsatisfiable `requires`
    // makes every downstream proof vacuous, which is a finding, not a success.
    if let Some(p) = pre {
        if smt::find_model(p) == Verdict::Unsat {
            report.obligations.push(Obligation {
                kind: ObligationKind::VacuousPrecondition,
                // `Unsat` is exactly the finding: the engine reports that no
                // input satisfies the precondition.
                verdict: Verdict::Unsat,
            });
            return report;
        }
    }

    let root = match prog.fns.iter().position(|g| std::ptr::eq(g, f)) {
        Some(i) => i,
        None => {
            report.unknown_paths.push("function is not part of the parsed program".into());
            return report;
        }
    };

    let mut env = Env::new();
    for &l in &f.arg_locals {
        let ty = f.ty_of(l).cloned().unwrap_or(Ty::Other("?".into()));
        let v = match ty.width() {
            Some(1) => Val::Bool(smt::var_named(l, 1).eq_val(1)),
            Some(w) => Val::Sym(smt::var_named(l, w)),
            None => Val::Unknown,
        };
        env.locals.insert(l, v);
    }

    let start = match f.blocks.first() {
        Some(b) => b.id,
        None => {
            report.unknown_paths.push("function has no basic blocks".into());
            return report;
        }
    };

    // A loop carried by an invariant is not unwound. The loop is located before
    // the walk starts, and a function with an invariant but no detectable back
    // edge is refused rather than silently unwound: the contract made a claim
    // and the tool must either honour it or say it could not.
    let cut = match invariant {
        None => None,
        Some(text) => match detect_loop(f) {
            Some((header, back_edges)) => {
                let havoc = loop_writes(f, header);
                Some(Cut { func: root, header, back_edges, havoc, text: text.to_string() })
            }
            None => {
                report.unknown_paths.push(
                    "an `invariant:` was declared but no loop was found to attach it to".into(),
                );
                return report;
            }
        },
    };

    let mut work = vec![State {
        frame: Frame {
            func: root,
            ret_target: usize::MAX,
            ret_dest: None,
            saved_env: None,
            caller: None,
        },
        block: start,
        path: pre.unwrap_or_else(|| smt::truth(true)),
        env,
        visits: BTreeMap::new(),
        depth: 0,
        cut,
    }];

    let mut explored: usize = 0;
    while let Some(st) = work.pop() {
        // Bound the *number of paths*, not just each loop. A branch inside an
        // unwound loop multiplies paths without any single loop exceeding
        // `DEFAULT_UNWIND`, so this is the guard that makes the search
        // terminate; see [`DEFAULT_PATH_BUDGET`]. Stopping here is reported, not
        // hidden: the function becomes incomplete and says why.
        if explored >= DEFAULT_PATH_BUDGET {
            report.unknown_paths.push(format!(
                "path budget exhausted after {DEFAULT_PATH_BUDGET} paths; the remainder was not explored"
            ));
            break;
        }
        explored += 1;
        run_state(prog, st, &post, &mut report, &mut work);
    }
    report
}

/// Locate the loop a function's invariant is about.
///
/// Returns the header and the blocks that jump back to it. The header is taken
/// to be the target of a back edge, and every edge into it is an induction
/// obligation, so the choice only has to be *a* loop head rather than the
/// canonical one rustc would name: for a single loop they coincide, and for a
/// function with more than one the contract is refused by the caller.
///
/// A "back edge" is an edge to a block that appears earlier in the block order.
/// MIR prints blocks in layout order and a loop body comes after its header, so
/// the edge from the latch back to the header is the one that goes backwards.
/// An edge that goes forward is a branch, not a back edge.
fn detect_loop(f: &MirFn) -> Option<(usize, Vec<usize>)> {
    let position: BTreeMap<usize, usize> =
        f.blocks.iter().enumerate().map(|(i, b)| (b.id, i)).collect();
    let mut header: Option<usize> = None;
    let mut back_edges: Vec<usize> = Vec::new();
    for b in &f.blocks {
        for target in successors(&b.term) {
            let (Some(&from), Some(&to)) = (position.get(&b.id), position.get(&target)) else {
                continue;
            };
            // `to <= from` is the whole test. It excludes the entry edge, whose
            // source precedes the header, and includes a header that loops to
            // itself. A block listed here can only ever be asked "is this a back
            // edge" when its edge targets the chosen header, and the chosen
            // header is the earliest backward target -- so a block with a
            // backward edge is never earlier than it, and a forward edge into the
            // header from an earlier block is never misclassified.
            if to <= from {
                // The header is the earliest block a back edge returns to, so
                // the choice stays stable when a latch closes two loops.
                match header {
                    Some(h) if position[&h] <= to => {}
                    _ => header = Some(target),
                }
                if !back_edges.contains(&b.id) {
                    back_edges.push(b.id);
                }
            }
        }
    }
    header.map(|h| (h, back_edges))
}

/// Every block a terminator can jump to.
fn successors(t: &Term) -> Vec<usize> {
    match t {
        Term::Goto(b) => vec![*b],
        Term::SwitchInt { cases, otherwise, .. } => {
            let mut v: Vec<usize> = cases.iter().map(|(_, b)| *b).collect();
            v.push(*otherwise);
            v
        }
        Term::Call { target, .. } => vec![*target],
        Term::Assert { target, .. } => vec![*target],
        Term::Return | Term::Unreachable | Term::Unknown(_) => Vec::new(),
    }
}

/// The locals a loop can write: every local assigned in a block reachable from
/// the header without leaving the loop.
///
/// Reachability is taken over the whole function rather than the loop body,
/// because a precise loop-body extraction is a dominator computation and this
/// only needs an over-approximation: havocing a local the loop never writes
/// loses information but cannot make an unsound proof sound.
///
/// `_0`, the return place, is always included. A loop is allowed to write the
/// return value (`s` in `sum_to` is `_0`), and leaving it out would leave the
/// exit edge holding the *pre-loop* return value -- which is precisely the hole
/// this set exists to close.
fn loop_writes(f: &MirFn, header: usize) -> Vec<u32> {
    let mut writes: BTreeMap<u32, ()> = BTreeMap::new();
    writes.insert(0, ());
    let mut seen: BTreeMap<usize, ()> = BTreeMap::new();
    let mut stack = vec![header];
    while let Some(b) = stack.pop() {
        if seen.insert(b, ()).is_some() {
            continue;
        }
        let Some(block) = f.block(b) else { continue };
        for s in &block.stmts {
            if let Stmt::Assign(dest, _) = s {
                writes.insert(dest.local, ());
            }
        }
        for t in successors(&block.term) {
            stack.push(t);
        }
    }
    writes.into_keys().collect()
}

/// The names an invariant may use: every local with a `debug` name, mapped to the
/// symbolic value that local holds.
///
/// Built from the *current* environment rather than from the types, because the
/// invariant is evaluated in the middle of a walk and has to name what the
/// variables hold there.
fn invariant_names(f: &MirFn, env: &Env) -> BTreeMap<String, Var> {
    let mut out = BTreeMap::new();
    for (&local, name) in &f.local_names {
        if let Some(Val::Sym(v)) = env.locals.get(&local) {
            out.insert(name.clone(), *v);
        }
    }
    out
}

/// The source names of signed locals, so an invariant's comparisons use the
/// signed relation for them.
fn signed_names(f: &MirFn) -> std::collections::BTreeSet<String> {
    let mut out = std::collections::BTreeSet::new();
    for (&local, name) in &f.local_names {
        if f.ty_of(local).map(|t| t.is_signed()).unwrap_or(false) {
            out.insert(name.clone());
        }
    }
    out
}

/// Evaluate the invariant in the current state, as a predicate.
///
/// An error means a name in the invariant does not resolve to a symbolic value --
/// a local still holding an aggregate, say. That is reported as an unmodelled
/// path rather than folded into `true`, because an invariant that silently became
/// `true` would discharge both induction obligations and prove nothing.
fn eval_invariant_here(f: &MirFn, env: &Env, text: &str) -> Result<Pred, String> {
    let names = invariant_names(f, env);
    crate::mir::spec::eval_invariant(text, &names, &signed_names(f)).map_err(|e| e.to_string())
}

/// Push the successor states of an edge to `target`, applying the loop cut when
/// this edge enters the invariant's header.
///
/// Every edge in the walk goes through here so the cut cannot be bypassed by a
/// terminator that happens to be spelled differently -- a `goto` and a `switchInt`
/// arm into the same header are the same induction case.
fn advance(
    prog: &MirProgram,
    mut st: State,
    target: usize,
    report: &mut MirReport,
    work: &mut Vec<State>,
) {
    let cut = match st.cut.clone() {
        Some(c) if c.func == st.frame.func && c.header == target => c,
        _ => {
            work.push(State { block: target, ..st });
            return;
        }
    };
    let cur = &prog.fns[st.frame.func];
    let inv = match eval_invariant_here(cur, &st.env, &cut.text) {
        Ok(p) => p,
        Err(e) => {
            report.unknown_paths.push(format!("unreadable `invariant`: {e}"));
            return;
        }
    };
    let back = cut.back_edges.contains(&st.block);
    let kind = if back {
        ObligationKind::LoopInvariantPreserve
    } else {
        ObligationKind::LoopInvariantInit
    };
    report.obligations.push(Obligation {
        kind,
        verdict: smt::prove_implies(st.path, inv),
    });
    // The cut closes here. A back edge is not followed: the assertion above is
    // the induction step, and re-entering the header would be the unwinding this
    // replaces.
    if back {
        return;
    }
    // An entry edge continues, but not with the values the path arrived with.
    // The loop is about to run, and the invariant says what is true of the header
    // *whenever* it is reached -- not what happens to be true the first time. So
    // the locals the loop can write are replaced by fresh values and the
    // invariant is assumed over those. Only then does the exit edge carry
    // `I && !guard`, which is what lets a postcondition be proved for every state
    // the loop can leave rather than for the one state the first pass produced.
    for &l in &cut.havoc {
        if let Some(ty) = cur.ty_of(l) {
            if let Some(w) = ty.width() {
                // `var`, not `var_named`: a fresh variable is the point. A named
                // one would return the very variable being replaced, and the
                // havoc would be a no-op.
                let fresh = if w == 1 {
                    Val::Bool(smt::var(1).eq_val(1))
                } else {
                    Val::Sym(smt::var(w))
                };
                st.env.locals.insert(l, fresh);
            }
        }
    }
    let inv = match eval_invariant_here(cur, &st.env, &cut.text) {
        Ok(p) => p,
        Err(e) => {
            report.unknown_paths.push(format!("unreadable `invariant`: {e}"));
            return;
        }
    };
    st.path = smt::and(st.path, inv);
    work.push(State { block: target, ..st });
}

fn run_state<F>(prog: &MirProgram, mut st: State, post: &Option<F>, report: &mut MirReport, work: &mut Vec<State>)
where
    F: Fn(Var) -> Result<Pred, String>,
{
    let cur = &prog.fns[st.frame.func];
    let block: Block = match cur.block(st.block) {
        Some(b) => b.clone(),
        None => {
            report.unknown_paths.push(format!("missing block bb{}", st.block));
            return;
        }
    };

    // Unwind bound: count visits, and stop the path rather than assume exit.
    let key = (st.frame.func, st.block);
    let n = st.visits.entry(key).or_insert(0);
    *n += 1;
    if *n > DEFAULT_UNWIND {
        report.unknown_paths.push(format!(
            "loop unwound past {DEFAULT_UNWIND} at bb{} of {}; assuming it exited would be unsound",
            st.block, cur.name
        ));
        return;
    }

    // Statements.
    for s in &block.stmts {
        match s {
            Stmt::Nop => {}
            Stmt::Unknown(text) => {
                report.unknown_paths.push(format!("unmodelled statement: {text}"));
                return;
            }
            Stmt::Assign(dest, rv) => {
                let v = eval_rvalue(cur, &mut st.env, dest, rv);
                st.env.set(dest, v);
            }
        }
    }

    // Terminator. Every successor goes through `advance`, which is where a loop
    // edge into the invariant's header is checked instead of followed.
    match &block.term {
        Term::Goto(b) => advance(prog, st, *b, report, work),
        Term::Return => {
            let ret = st.env.get(&Place::new(0));
            match st.frame.caller.take() {
                // The root returned: check the postcondition here.
                None => {
                    report.returned_paths += 1;
                    if let Some(post) = post {
                        match ret {
                            Val::Sym(rv) => match post(rv) {
                                Ok(p) => {
                                    let v = smt::prove_implies(st.path, p);
                                    report.obligations.push(Obligation {
                                        kind: ObligationKind::Postcondition,
                                        verdict: v,
                                    });
                                }
                                Err(e) => report
                                    .unknown_paths
                                    .push(format!("unreadable `ensures`: {e}")),
                            },
                            Val::Bool(rp) => {
                                // A `bool` return is a one-bit word, so the
                                // postcondition is evaluated against that bit.
                                // Proving `path => rp` alone would check only
                                // that the returned bool is *true*, which is not
                                // the contract at all: `ensures: ret == false`
                                // would be ignored and a false postcondition
                                // would verify.
                                let rv = smt::ite(rp, smt::word(1, 1), smt::word(0, 1));
                                match post(rv) {
                                    Ok(p) => {
                                        let v = smt::prove_implies(st.path, p);
                                        report.obligations.push(Obligation {
                                            kind: ObligationKind::Postcondition,
                                            verdict: v,
                                        });
                                    }
                                    Err(e) => report
                                        .unknown_paths
                                        .push(format!("unreadable `ensures`: {e}")),
                                }
                            }
                            _ => report
                                .unknown_paths
                                .push("return value is not modelled, postcondition not checked".into()),
                        }
                    }
                }
                // A callee returned: hand its value to the caller's destination
                // and continue at the call site. This continuation is what makes
                // an inlined call mean what the real call means.
                Some(caller) => {
                    // Resume in the *caller's* environment, not the callee's. The
                    // two number their locals independently, so carrying the
                    // callee's env back would hand the caller the callee's
                    // values under the caller's local numbers. Only the return
                    // value crosses the boundary, written to the call's
                    // destination.
                    let mut env = caller.saved_env.clone().unwrap_or_else(Env::new);
                    if let Some(dest) = &caller.ret_dest {
                        env.set(dest, ret);
                    }
                    work.push(State {
                        block: caller.ret_target,
                        frame: *caller,
                        path: st.path,
                        env,
                        visits: st.visits,
                        depth: st.depth.saturating_sub(1),
                        cut: st.cut.clone(),
                    });
                }
            }
        }
        Term::Unreachable => {
            report.obligations.push(Obligation {
                kind: ObligationKind::Unreachable,
                verdict: smt::find_model(st.path),
            });
        }
        Term::Assert { cond, negated, msg, target, .. } => {
            // `assert(c)` panics when `c` is false, so a panic is possible
            // exactly when `path ∧ ¬c` is satisfiable. rustc prints the
            // overflow and divide-by-zero checks as `assert(!bit)`, so `negated`
            // flips which polarity is the failing one.
            let c = operand(&st.env, cond);
            let holds = match c {
                Val::Bool(p) => p,
                // A bit-vector condition is true when it is non-zero.
                Val::Sym(v) => smt::not(smt::eq_const(v, 0)),
                Val::Agg | Val::Unknown => {
                    report.unknown_paths.push(format!("unmodelled assert condition: {msg}"));
                    return;
                }
            };
            let satisfied = if *negated { smt::not(holds) } else { holds };
            let bad = smt::and(st.path, smt::not(satisfied));
            report.obligations.push(Obligation {
                kind: ObligationKind::Panic { message: msg.clone() },
                verdict: smt::find_model(bad),
            });
            // An assert that did *not* fire is an assumption, and the fall-through
            // path has to carry it. Without this the guard is discarded, which is
            // merely *imprecise* when the guard is what keeps the code safe, but
            // still wrong: `x << n` is only meaningful under `n < w`, and a caller
            // that writes the guard itself expects it to be assumed here too.
            // Sound because the guard is proved separately above: a path where it
            // fails is reported as a panic, and assuming it on this path cannot
            // hide one. Both asserts and `debug_assert`s are lowered to this
            // terminator, so the guard is assumed for either.
            let path = smt::and(st.path, satisfied);
            let next = State { block: *target, path, ..st };
            advance(prog, next, *target, report, work);
        }
        Term::SwitchInt { discr, cases, otherwise } => {
            let d = operand(&st.env, discr);
            let arm = |k: u128, positive: bool| -> Option<Pred> {
                match d {
                    Val::Bool(p) => Some(if (k != 0) == positive { p } else { smt::not(p) }),
                    Val::Sym(v) => {
                        let eq = smt::eq_const(v, k as u64);
                        Some(if positive { eq } else { smt::not(eq) })
                    }
                    _ => None,
                }
            };
            for (k, target) in cases {
                let Some(cond) = arm(*k, true) else {
                    report.unknown_paths.push("unmodelled switch discriminant".into());
                    return;
                };
                let mut visits = st.visits.clone();
                visits.insert(key, 0);
                let next = State {
                    block: *target,
                    path: smt::and(st.path, cond),
                    env: st.env.clone(),
                    visits,
                    frame: st.frame.clone(),
                    depth: st.depth,
                    cut: st.cut.clone(),
                };
                advance(prog, next, *target, report, work);
            }
            let mut negs = Vec::new();
            for (k, _) in cases {
                let Some(n) = arm(*k, false) else {
                    report.unknown_paths.push("unmodelled switch discriminant".into());
                    return;
                };
                negs.push(n);
            }
            let mut visits = st.visits.clone();
            visits.insert(key, 0);
            let next = State {
                block: *otherwise,
                path: smt::and(st.path, smt::all(&negs)),
                env: st.env.clone(),
                visits,
                frame: st.frame.clone(),
                depth: st.depth,
                cut: st.cut.clone(),
            };
            advance(prog, next, *otherwise, report, work);
        }
        Term::Call { callee, args, dest, target } => {
            let Callee::Name(name) = callee else {
                report.unknown_paths.push("indirect call not modelled".into());
                return;
            };
            if st.depth + 1 >= DEFAULT_INLINE_DEPTH {
                report.unknown_paths.push(format!("call depth limit reached at `{name}`"));
                return;
            }
            // Only same-dump calls can be inlined. Assuming a return value for
            // anything else would be assuming the conclusion, so it is unknown.
            let Some(idx) = prog
                .fns
                .iter()
                .position(|g| g.name == *name || g.name.rsplit("::").next() == Some(name.as_str()))
            else {
                report.unknown_paths.push(format!("call to unmodelled function `{name}`"));
                return;
            };
            let callee_fn = &prog.fns[idx];
            let Some(b0) = callee_fn.blocks.first() else {
                report.unknown_paths.push(format!("callee `{name}` has no body"));
                return;
            };
            let mut env = Env::new();
            for (i, a) in args.iter().enumerate() {
                let v = operand(&st.env, a);
                if let Some(&l) = callee_fn.arg_locals.get(i) {
                    env.locals.insert(l, v);
                }
            }
            let caller = Frame {
                func: st.frame.func,
                ret_target: *target,
                ret_dest: Some(dest.clone()),
                // The caller's locals are put aside here and restored on return.
                // `env` below is the callee's, freshly built from the arguments.
                saved_env: Some(st.env.clone()),
                caller: st.frame.caller.clone(),
            };
            let mut visits = st.visits;
            visits.insert((idx, b0.id), 0);
            work.push(State {
                frame: Frame {
                    func: idx,
                    ret_target: usize::MAX,
                    ret_dest: None,
                    saved_env: None,
                    caller: Some(Box::new(caller)),
                },
                block: b0.id,
                path: st.path,
                env,
                visits,
                depth: st.depth + 1,
                // A callee is a different function with its own locals, so the
                // caller's loop cut does not apply inside it.
                cut: None,
            });
        }
        Term::Unknown(text) => {
            report.unknown_paths.push(format!("unmodelled terminator: {text}"));
        }
    }
}

/// Resolve an operand to a symbolic value.
fn operand(env: &Env, o: &Operand) -> Val {
    match o {
        Operand::Copy(p) | Operand::Move(p) => env.get(p),
        Operand::Const(c) => match c {
            Const::UInt(v, ty) => match ty.as_ref().and_then(|t| t.width()) {
                Some(1) => Val::Bool(smt::truth(*v == 1)),
                Some(w) => Val::Sym(smt::word(*v as u64, w)),
                None => Val::Unknown,
            },
            Const::Bool(b) => Val::Bool(smt::truth(*b)),
            Const::Unit | Const::Other(_) => Val::Unknown,
        },
    }
}

/// Evaluate an rvalue into a symbolic value.
fn eval_rvalue(f: &MirFn, env: &mut Env, dest: &Place, rv: &Rvalue) -> Val {
    let dest_w = width_of(f, dest);
    match rv {
        Rvalue::Use(o) => {
            // A literal assigned to a typed place takes the place's width when
            // the dump did not print a suffix.
            if let Operand::Const(Const::UInt(v, None)) = o {
                if let Some(w) = dest_w {
                    return Val::Sym(smt::word(*v as u64, w));
                }
            }
            operand(env, o)
        }
        Rvalue::Binary(op, a, b) => {
            let (x, y) = (operand(env, a), operand(env, b));
            // The signedness of the *left* operand decides what `Shr` means; the
            // amount's type is irrelevant and rustc keeps it a distinct `u32`.
            let signed = operand_is_signed(f, a);
            eval_binary(*op, x, y, dest_w, signed)
        }
        Rvalue::CheckedBinary(op, a, b) => {
            // The tuple is `(result, overflowed)`. Field 0 gets the wrapped
            // result and field 1 the overflow predicate, so the `assert(!(_3.1))`
            // that follows has a real condition to check.
            // `_3` is `(uN, bool)`, which has no width; the operand width is
            // field 0's. Reading the width from the tuple instead gives 64 for
            // every type, which silently mis-sizes the overflow test.
            let w = width_of(f, &Place { local: dest.local, proj: vec![Proj::Field(0)] })
                .or(dest_w)
                .unwrap_or(64);
            let x = operand(env, a);
            let y = operand(env, b);
            let signed = operand_is_signed(f, a);
            let res = eval_binary(*op, x, y, Some(w), signed);
            env.set(&Place { local: dest.local, proj: vec![Proj::Field(0)] }, res);
            match overflow_pred(*op, x, y, w, signed) {
                Some(p) => {
                    env.set(&Place { local: dest.local, proj: vec![Proj::Field(1)] }, Val::Bool(p));
                }
                None => {
                    // No sound predicate is available for this operator at this
                    // width, so the overflow bit is unknown and the `assert` that
                    // reads it will report the path as unmodelled.
                    env.set(&Place { local: dest.local, proj: vec![Proj::Field(1)] }, Val::Unknown);
                }
            }
            Val::Agg
        }
        Rvalue::Unary(op, a) => {
            let v = operand(env, a);
            match (op, v) {
                (_, Val::Unknown) => Val::Unknown,
                (UnOp::Not, Val::Bool(p)) => Val::Bool(smt::not(p)),
                (UnOp::Not, Val::Sym(s)) => match dest_w {
                    Some(w) => Val::Sym(smt::bxor(s, smt::all_ones(w))),
                    None => Val::Unknown,
                },
                // `-x` is `0 - x`, which is the right bit pattern for every input
                // including `MIN` (it wraps back to `MIN`, which is what rustc's
                // own `assert(x != MIN)` guards and then computes anyway).
                (UnOp::Neg, Val::Sym(s)) => match dest_w {
                    Some(w) => Val::Sym(smt::sub(smt::word(0, w), s)),
                    None => Val::Unknown,
                },
                _ => Val::Unknown,
            }
        }
        Rvalue::Cast(o, ty) => {
            let v = operand(env, o);
            match (v, ty.width()) {
                (Val::Sym(s), Some(w)) => Val::Sym(smt::truncate(s, w)),
                (Val::Bool(p), Some(1)) => Val::Bool(p),
                (Val::Bool(p), Some(w)) => Val::Sym(smt::ite(p, smt::word(1, w), smt::word(0, w))),
                _ => Val::Unknown,
            }
        }
        Rvalue::Aggregate(ops) => {
            for (i, o) in ops.iter().enumerate() {
                let v = operand(env, o);
                env.set(&Place { local: dest.local, proj: vec![Proj::Index(i as u64)] }, v);
            }
            Val::Agg
        }
        Rvalue::Ref(_) | Rvalue::Len(_) | Rvalue::Unknown(_) => Val::Unknown,
    }
}

/// The declared width of a place, following one level of tuple/array projection.
fn width_of(f: &MirFn, p: &Place) -> Option<u8> {
    let mut ty = f.ty_of(p.local)?.clone();
    for pr in &p.proj {
        ty = match (pr, &ty) {
            (Proj::Field(i), Ty::Tuple(ts)) => ts.get(*i as usize)?.clone(),
            (Proj::Index(_), Ty::Array(inner, _)) => (**inner).clone(),
            _ => return None,
        };
    }
    match &ty {
        Ty::Ref(inner) => inner.width(),
        t => t.width(),
    }
}

/// Whether the operand's declared type is a signed integer.
///
/// `Shr` is arithmetic for a signed operand and logical for an unsigned one, and
/// the bit pattern alone does not say which. Guessing would be a wrong answer for
/// every signed shift, so the type is read rather than assumed.
fn operand_is_signed(f: &MirFn, o: &Operand) -> bool {
    match o {
        Operand::Copy(p) | Operand::Move(p) => {
            f.ty_of(p.local).map(Ty::is_signed).unwrap_or(false)
        }
        Operand::Const(_) => false,
    }
}

/// Which of the engine's three shifts a MIR `Shl`/`Shr` means.
///
/// The operand's signedness decides what `Shr` means, and the engine needs it
/// stated rather than guessed, so it is read from the type.
fn shift_kind(op: BinOp, signed: bool) -> smt::Shift {
    match (op, signed) {
        (BinOp::Shl, _) => smt::Shift::Left,
        (_, true) => smt::Shift::ArithmeticRight,
        (_, false) => smt::Shift::LogicalRight,
    }
}

/// Apply a binary operator, respecting the destination width.
fn eval_binary(op: BinOp, a: Val, b: Val, width: Option<u8>, signed: bool) -> Val {
    match op {
        BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
            let (x, y) = match (a, b) {
                (Val::Sym(x), Val::Sym(y)) => (x, y),
                (Val::Bool(x), Val::Bool(y)) => {
                    return Val::Bool(match op {
                        BinOp::Eq => smt::iff(x, y),
                        BinOp::Ne => smt::xor(x, y),
                        _ => return Val::Unknown,
                    })
                }
                _ => return Val::Unknown,
            };
            Val::Bool(match op {
                BinOp::Eq => smt::eq(x, y),
                BinOp::Ne => smt::not(smt::eq(x, y)),
                // Signedness matters here and only here: `<` on an `i8` is not
                // `<` on a `u8`, and the unsigned form calls `-1` the largest
                // value. rustc picks signed or unsigned by the operand type, so
                // the type is what decides -- a wrong choice is not a missed
                // proof but a wrong branch, which is a wrong answer.
                BinOp::Lt if signed => smt::slt(x, y),
                BinOp::Le if signed => smt::sle(x, y),
                BinOp::Gt if signed => smt::sgt(x, y),
                BinOp::Ge if signed => smt::sge(x, y),
                BinOp::Lt => smt::ult(x, y),
                BinOp::Le => smt::ule(x, y),
                BinOp::Gt => smt::ult(y, x),
                BinOp::Ge => smt::ule(y, x),
                _ => unreachable!(),
            })
        }
        _ => {
            let (x, y) = match (a, b) {
                (Val::Sym(x), Val::Sym(y)) => (x, y),
                // Bitwise operators on `bool`. rustc lowers `p && q` to
                // `BitAnd(p, q)` and the OR/XOR forms likewise, so a contract
                // assert whose condition was written with `&&` arrives here as a
                // bitwise op on two booleans. Refusing it would leave the assert
                // unmodelled and the obligation open, which is a coverage hole
                // rather than a wrong answer -- but an avoidable one.
                (Val::Bool(p), Val::Bool(q)) => {
                    return Val::Bool(match op {
                        BinOp::BitAnd => smt::and(p, q),
                        BinOp::BitOr => smt::or(p, q),
                        BinOp::BitXor => smt::xor(p, q),
                        _ => return Val::Unknown,
                    })
                }
                _ => return Val::Unknown,
            };
            if width.is_none() {
                return Val::Unknown;
            }
            Val::Sym(match op {
                BinOp::Add => smt::add(x, y),
                BinOp::Sub => smt::sub(x, y),
                BinOp::Mul => smt::mul(x, y),
                BinOp::BitAnd => smt::band(x, y),
                BinOp::BitOr => smt::bor(x, y),
                BinOp::BitXor => smt::bxor(x, y),
                // Division and remainder go through the engine's restoring
                // divider, which is exact. `y == 0` has a defined value there,
                // and rustc's own divide-by-zero assert is what turns that into
                // a reported panic, so the pair is consistent. A signed operand
                // needs the *signed* divider: the unsigned one would return a
                // huge positive quotient for `-7 / 2`, which is a wrong value
                // and not merely a weaker proof.
                BinOp::Div | BinOp::Rem => {
                    let signed_pair = (signed, op);
                    match signed_pair {
                        (true, BinOp::Div) => smt::sdiv(x, y),
                        (true, BinOp::Rem) => smt::srem(x, y),
                        (false, BinOp::Div) => smt::udiv(x, y),
                        _ => smt::urem(x, y),
                    }
                }
                // A *variable* shift amount is a barrel shifter (see
                // `smt::shift_var`). rustc guards it with `assert(n < w)`
                // immediately before, so the amount is in range on every path that
                // reaches here. A constant amount keeps the cheap `Op::Shl` path,
                // which is also what makes `x << 3` prove without any guard at all.
                BinOp::Shl | BinOp::Shr => {
                    let Some(w) = width else { return Val::Unknown };
                    match smt::const_of(y) {
                        // rustc's guard says `k < w`; a constant outside that range
                        // is a compile error, so this is defensive only.
                        Some(k) if k < w as u64 => {
                            let v = match shift_kind(op, signed) {
                                smt::Shift::Left => smt::shl(x, k as u32),
                                smt::Shift::LogicalRight => smt::lshr(x, k as u32),
                                smt::Shift::ArithmeticRight => smt::ashr(x, k as u32),
                            };
                            return Val::Sym(v);
                        }
                        Some(_) => return Val::Unknown,
                        None => {
                            return Val::Sym(smt::shift_var(shift_kind(op, signed), x, y));
                        }
                    }
                }
                _ => return Val::Unknown,
            })
        }
    }
}

/// The predicate that says "this operation wraps at width `w`", or `None` when no
/// sound predicate is available.
///
/// This is the load-bearing part of the whole frontend, so it is worth being
/// precise about. rustc lowers `a + b` to `AddWithOverflow` plus an
/// `assert(!overflow)`, and it is that assert which makes the check meaningful.
/// If `overflow_pred` returned something too weak, the assert would look
/// dischargeable and an overflowing program would be reported panic-free — the
/// exact failure mode the README calls out, where an unsound engine reports a
/// *better-looking* result than the truth.
fn overflow_pred(op: BinOp, a: Val, b: Val, w: u8, signed: bool) -> Option<Pred> {
    let (x, y) = match (a, b) {
        (Val::Sym(x), Val::Sym(y)) => (x, y),
        _ => return None,
    };
    Some(match op {
        // Unsigned `x + y` wraps exactly when the sum is below `x`: that is the
        // carry out of the top bit, and the unsigned order tracks it.
        //
        // Signed addition is a *different* condition, and getting it wrong is
        // unsound rather than merely weak. The carry test is not enough: `127 + 1`
        // at `i8` carries into a result that is *below* `127` read unsigned, so
        // the unsigned test happens to fire there — but it also fires on `-1 + 1`
        // (no overflow, result `0`), and it misses `-128 + -1`, whose sum `127u8`
        // carries yet lands below `127`... in a direction that depends on which
        // operand you compare against. The sign rule is the sound one and has no
        // such cases: the result is wrong exactly when the operands agree in sign
        // and the result disagrees with them.
        BinOp::Add if signed => {
            let sum = smt::add(x, y);
            let same_sign = smt::iff(smt::negative(x), smt::negative(y));
            smt::and(same_sign, smt::xor(smt::negative(x), smt::negative(sum)))
        }
        BinOp::Add => smt::ult(smt::add(x, y), x),
        // Unsigned `x - y` wraps exactly when `x < y` (the borrow).
        //
        // Signed subtraction wraps when the operands *differ* in sign and the
        // result takes the sign of the subtrahend: `x - y` is wrong exactly when
        // `x` and `y` disagree and the result agrees with `y`.
        BinOp::Sub if signed => {
            let diff = smt::sub(x, y);
            let differ = smt::xor(smt::negative(x), smt::negative(y));
            smt::and(differ, smt::iff(smt::negative(y), smt::negative(diff)))
        }
        BinOp::Sub => smt::ult(x, y),
        // `x * y` wraps exactly when the exact product needs more than `w` bits.
        //
        // The engine has no wide multiplication, so the high half is computed by
        // widening: `smt::truncate` zero-extends when the target width is larger,
        // so the operands are widened to `2w`, multiplied exactly there, and the
        // overflow test is `>= 2^w`. That is exact rather than a sufficient
        // condition, which matters because a too-weak predicate here would make
        // the `assert` look dischargeable and report an overflowing function as
        // panic-free.
        //
        // Widening is where signedness matters, and the direction is worth being
        // exact about. rustc computes the *sign-extended* product and then tests
        // whether it equals the `w`-bit result sign-extended back to `2w`. That
        // test is about magnitudes, so it is neither "the unsigned product is
        // below `2^w`" (which fires spuriously for `-1 * -1` at `i8`) nor the
        // `2^(2w-1)` magnitude rule (which fires spuriously for `-128 * 1`). The
        // sign-extended product is built here, and the equality is what is
        // checked.
        BinOp::Mul => {
            let wide = w.saturating_mul(2).min(64);
            if wide <= w {
                // At the widest supported width there is nowhere to widen to, so
                // no sound predicate is available.
                return None;
            }
            // The widened product is a BDD-hostile shape: a `2w`-bit multiplier
            // is the scaling wall this crate documents. Past 16 bits the query
            // is not worth posing, so no predicate is produced and the path is
            // reported unknown. That is the deliberate trade -- a verifier that
            // declines is better than one that hangs, and a *weaker* predicate
            // here would be worse than either, because it would make an
            // overflowing function look panic-free.
            if wide > 16 {
                return None;
            }
            if signed {
                // Sign-extend the operands, so the product is exact; the
                // `2w`-bit product of two `w`-bit signed values always fits in
                // `2w` signed bits, so this multiply cannot itself wrap.
                let exact = smt::mul(smt::sign_extend(x, wide), smt::sign_extend(y, wide));
                // The exact product is right exactly when it equals the `w`-bit
                // wrapped result *sign-extended* back to `2w`. Sign-extending the
                // wrapped result is what makes this rustc's test rather than a
                // magnitude test -- comparing a zero-extended result would fire
                // on every negative product.
                let want = smt::sign_extend(smt::mul(x, y), wide);
                smt::not(smt::eq(exact, want))
            } else {
                let exact = smt::mul(smt::truncate(x, wide), smt::truncate(y, wide));
                // 2^w, as a constant in the widened width.
                let limit = 1u64 << (w - 1);
                let limit = limit.saturating_mul(2);
                smt::uge_const(exact, limit)
            }
        }
        _ => return None,
    })
}
#[cfg(test)]
mod tests {
    //! The oracle for the per-kind discharge polarity, and for the report
    //! aggregation built on it.
    //!
    //! Every other check on this logic lives in `tests/mir.rs`, which needs
    //! `DISCHARGE_RUSTC` pointing at a nightly compiler and *skips itself* without
    //! one. A skipped test still reports `ok`, so the suite count is the same
    //! whether the polarity is exercised or not: 325 with the nightly, 325
    //! without. On a stable-only machine the rule below had no teeth at all.
    //!
    //! The rule is also the kind of thing a single-polarity reading gets wrong in
    //! both directions. An `Unsat` answer *discharges* a panic query ("it cannot
    //! happen") and *refutes* a postcondition ("it holds for no input"). Collapsing
    //! the match into `verdict.is_proved()` -- which is what a caller reaching for
    //! `Verdict::is_proved` would write -- left the whole nightly suite green until
    //! `tests/mir.rs` was run with the compiler present, and it is exactly the
    //! soundness hole this method exists to close.
    //!
    //! So the oracle enumerates the whole truth table rather than sampling it, and
    //! asserts the cross-kind asymmetry that no single-polarity reading can satisfy.

    use super::*;
    use crate::smt;

    /// A real counterexample. A `Cex` has private fields and only the engine can
    /// build one, so this asks for a satisfiable-but-not-valid query rather than
    /// fabricating a witness.
    fn counterexample() -> Verdict {
        smt::with_fresh(|| {
            let x = smt::var(8);
            // `x < 3` has models (0, 1, 2) and is not valid, so `find_model`
            // refutes it and hands back one of them.
            smt::find_model(smt::ult_const(x, 3))
        })
    }

    fn panic_kind() -> ObligationKind {
        ObligationKind::Panic { message: "attempt to compute overflow".into() }
    }

    fn ob(kind: ObligationKind, verdict: Verdict) -> Obligation {
        Obligation { kind, verdict }
    }

    /// The truth table for `is_discharged`, written out rather than derived from
    /// the implementation, so the test states the intended semantics instead of
    /// echoing the code.
    ///
    /// The interesting rows are the ones that differ by kind at a fixed verdict:
    /// `Unsat` discharges a panic and refutes a postcondition; `Counterexample`
    /// refutes a postcondition and discharges a vacuity check.
    #[test]
    fn discharge_polarity_is_per_kind_not_per_verdict() {
        let cex = counterexample();
        assert!(
            matches!(cex, Verdict::Counterexample(_)),
            "the fixture needs a real counterexample, got {cex}"
        );

        // (kind, verdict, discharged)
        let table = [
            // A postcondition is discharged only by `Valid`: it must hold for all
            // inputs. `Unsat` is the strongest failure, not a pass.
            (ObligationKind::Postcondition, Verdict::Valid, true),
            (ObligationKind::Postcondition, Verdict::Unsat, false),
            (ObligationKind::Postcondition, cex, false),
            (ObligationKind::Postcondition, Verdict::Unknown, false),
            // A panic is discharged only by `Unsat`: the query is "can it happen",
            // so `Unsat` is the good answer and `Valid` is the worst case.
            (panic_kind(), Verdict::Valid, false),
            (panic_kind(), Verdict::Unsat, true),
            (panic_kind(), cex, false),
            (panic_kind(), Verdict::Unknown, false),
            // An `unreachable` is the same query shape as a panic.
            (ObligationKind::Unreachable, Verdict::Valid, false),
            (ObligationKind::Unreachable, Verdict::Unsat, true),
            (ObligationKind::Unreachable, cex, false),
            (ObligationKind::Unreachable, Verdict::Unknown, false),
            // A vacuity check is discharged when it is *refuted*: some input
            // satisfies the precondition. `Unsat` here is the finding.
            (ObligationKind::VacuousPrecondition, Verdict::Valid, true),
            (ObligationKind::VacuousPrecondition, Verdict::Unsat, false),
            (ObligationKind::VacuousPrecondition, cex, true),
            (ObligationKind::VacuousPrecondition, Verdict::Unknown, false),
        ];

        for (kind, verdict, expected) in table {
            let o = ob(kind.clone(), verdict);
            assert_eq!(
                o.is_discharged(),
                expected,
                "{} with verdict `{verdict}`: expected discharged={expected}",
                kind
            );
        }
    }

    /// The asymmetry the truth table rests on, stated on its own so a regression
    /// names the exact confusion rather than one row of a table.
    #[test]
    fn the_same_verdict_is_opposite_for_a_panic_and_a_postcondition() {
        let panic = ob(panic_kind(), Verdict::Unsat);
        let post = ob(ObligationKind::Postcondition, Verdict::Unsat);

        assert!(
            panic.is_discharged(),
            "an `Unsat` panic query means the panic cannot happen: a discharge"
        );
        assert!(
            !post.is_discharged(),
            "an `Unsat` postcondition holds for no input: the strongest failure"
        );
    }

    /// `Unknown` is never a discharge, for any kind. This is the one rule that is
    /// shared, and it is the reason the engine may decline to answer safely.
    #[test]
    fn an_undecided_obligation_is_never_discharged() {
        for kind in [
            ObligationKind::Postcondition,
            panic_kind(),
            ObligationKind::Unreachable,
            ObligationKind::VacuousPrecondition,
        ] {
            let o = ob(kind.clone(), Verdict::Unknown);
            assert!(!o.is_discharged(), "{kind} must not be discharged on `Unknown`");
        }
    }

    /// The two failures that leave no witness are opposite findings, and both
    /// render with no counterexample. The detail string has to tell them apart:
    /// a shared "holds for every input" describes an impossible postcondition as
    /// a universal truth, which is the reverse of what happened.
    #[test]
    fn the_two_witnessless_failures_are_told_apart() {
        let post = ob(ObligationKind::Postcondition, Verdict::Unsat);
        let panic = ob(panic_kind(), Verdict::Valid);

        assert!(post.failure_witness().is_none(), "an `Unsat` postcondition has no witness");
        assert!(panic.failure_witness().is_none(), "an always-firing panic has no witness");

        let post_detail = post.failure_detail();
        let panic_detail = panic.failure_detail();

        assert!(
            post_detail.contains("no input"),
            "an `Unsat` postcondition holds for NO input; detail was: {post_detail}"
        );
        assert!(
            panic_detail.contains("every input"),
            "a `Valid` panic fires on EVERY input; detail was: {panic_detail}"
        );
        assert_ne!(
            post_detail, panic_detail,
            "opposite findings must not share a diagnosis"
        );
        assert!(
            !post_detail.contains("every input") || post_detail.contains("no input"),
            "the postcondition detail must not read as a universal truth: {post_detail}"
        );
    }

    /// The classifier sentinels: a non-discharged obligation whose verdict is the
    /// discharge case for its kind would be a bug in `is_discharged`, so the
    /// detail says so instead of inventing a diagnosis.
    #[test]
    fn a_non_discharged_obligation_in_its_discharge_case_says_it_is_invalid() {
        // `Valid` is the pass case for a postcondition, so reaching the failure
        // path with it means the classifier disagreed with itself.
        let post = ob(ObligationKind::Postcondition, Verdict::Valid);
        assert!(
            post.failure_detail().contains("invalid"),
            "expected the invalid-classifier sentinel, got: {}",
            post.failure_detail()
        );

        // `Unsat` is the discharge case for a panic query, likewise.
        let panic = ob(panic_kind(), Verdict::Unsat);
        assert!(
            panic.failure_detail().contains("invalid"),
            "expected the invalid-classifier sentinel, got: {}",
            panic.failure_detail()
        );
    }

    /// A cutoff is not a proof, however many obligations passed.
    #[test]
    fn a_report_with_an_unknown_path_is_never_proved() {
        let report = MirReport {
            function: "f".into(),
            obligations: vec![ob(ObligationKind::Postcondition, Verdict::Valid)],
            unknown_paths: vec!["loop budget exhausted".into()],
            returned_paths: 1,
        };
        assert!(
            !report.is_proved(),
            "an unexplored path means the verification is incomplete"
        );
    }

    /// A decided failure outranks an undecided obligation, and the undecided one
    /// is counted separately rather than folded into the failure.
    #[test]
    fn a_decided_failure_outranks_an_undecided_obligation() {
        let cex = counterexample();
        let report = MirReport {
            function: "f".into(),
            obligations: vec![
                ob(ObligationKind::Postcondition, Verdict::Unknown),
                ob(panic_kind(), cex),
            ],
            unknown_paths: vec![],
            returned_paths: 1,
        };

        let failure = report
            .first_failure()
            .expect("a decided failure must be reported even when an earlier obligation is undecided");
        assert!(
            matches!(failure.kind, ObligationKind::Panic { .. }),
            "the panic is the decided failure, not the undecided postcondition"
        );
        assert_eq!(report.undecided(), 1, "the `Unknown` obligation is still counted");
        assert!(!report.is_proved(), "a failure means the function is not proved");
    }

    /// `panics_ruled_out` counts discharged panic obligations only: not other
    /// kinds, and not panics that were refuted.
    #[test]
    fn panics_ruled_out_counts_only_discharged_panics() {
        let cex = counterexample();
        let report = MirReport {
            function: "f".into(),
            obligations: vec![
                ob(panic_kind(), Verdict::Unsat),
                ob(panic_kind(), cex),
                ob(ObligationKind::Postcondition, Verdict::Valid),
            ],
            unknown_paths: vec![],
            returned_paths: 1,
        };
        assert_eq!(report.panics_ruled_out(), 1);
    }

    /// A vacuous precondition is a finding, and it must not read as a clean
    /// report: the obligation is not discharged, so the function is not proved.
    #[test]
    fn a_vacuous_precondition_is_a_finding_not_a_pass() {
        let report = MirReport {
            function: "f".into(),
            obligations: vec![ob(ObligationKind::VacuousPrecondition, Verdict::Unsat)],
            unknown_paths: vec![],
            returned_paths: 1,
        };
        assert!(!report.is_proved(), "an unsatisfiable precondition proves nothing");
        let failure = report.first_failure().expect("the vacuity is a decided failure");
        assert_eq!(failure.kind, ObligationKind::VacuousPrecondition);
        assert!(
            failure.failure_detail().contains("vacuous"),
            "the detail must name the vacuity, got: {}",
            failure.failure_detail()
        );
    }

    /// A branch inside an unwound loop multiplies paths without any single loop
    /// exceeding `DEFAULT_UNWIND`, so the loop bound alone does not make the
    /// search terminate.
    ///
    /// This is the regression for a real hang: `count_evens` below -- the exact
    /// MIR `rustc -O` emits for `while i < n { if i % 2 == 0 { c += 1; } i += 1; }`
    /// -- ran for minutes without returning, and the tool therefore reported
    /// *nothing* about it. The frontend's contract is that a cutoff is named as a
    /// cutoff; a search that never returns cannot name anything, so this test
    /// pins the property that matters: the call returns, and the incompleteness
    /// is reported rather than hidden.
    ///
    /// The MIR is embedded so the test runs on stable. `tests/mir.rs` covers the
    /// same function end-to-end but skips itself without `DISCHARGE_RUSTC`.
    #[test]
    fn a_branching_loop_reports_a_path_budget_rather_than_running_forever() {
        const COUNT_EVENS_MIR: &str = r#"
fn count_evens(_1: u8) -> u8 {
    debug n => _1;
    let mut _0: u8;
    let mut _2: u8;
    let mut _3: bool;
    let mut _4: u8;
    let mut _5: u8;
    let mut _6: u8;

    bb0: {
        _0 = const 0_u8;
        _2 = const 0_u8;
        goto -> bb1;
    }

    bb1: {
        _4 = copy _2;
        _3 = Lt(move _4, copy _1);
        switchInt(move _3) -> [0: bb6, otherwise: bb2];
    }

    bb2: {
        _6 = copy _2;
        _5 = Rem(move _6, const 2_u8);
        switchInt(copy _5) -> [0: bb3, otherwise: bb4];
    }

    bb3: {
        _0 = Add(copy _0, const 1_u8);
        goto -> bb5;
    }

    bb4: {
        goto -> bb5;
    }

    bb5: {
        _2 = Add(copy _2, const 1_u8);
        goto -> bb1;
    }

    bb6: {
        return;
    }
}
"#;
        // Go through the real entry point, not `verify_fn` directly. The hang
        // needs the corpus's postcondition closure as well as its precondition:
        // the postcondition is evaluated on every path and its BDD grows with
        // the path condition, which is what makes each successive path cost more
        // than the last. A hand-built `verify_fn` call without it settles
        // quickly, so it would not reproduce the defect.
        let src = "/// requires: n <= 8\n/// ensures: ret <= 8\npub fn count_evens(n: u8) -> u8 { n }\n";
        let specs = crate::mir::spec::extract(src);
        // Run on a thread with a large stack. The engine recurses through the
        // BDD and the frontend recurses through the term graph, so this workload
        // needs more stack than the test harness's default thread gives; the
        // real driver (`examples/mir_coverage.rs`) runs on the main thread and
        // never sees this. The stack size is not the property under test -- the
        // reported cutoff is -- so giving it room keeps the test about the fix.
        let outcome = std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(move || {
                let prog = crate::mir::parse::parse_program(COUNT_EVENS_MIR);
                let f = prog.get("count_evens").expect("the dump must parse");
                crate::smt::with_fresh(|| {
                    crate::mir::verify::verify_function(&prog, f, &specs)
                })
            })
            .expect("the test thread must spawn")
            .join()
            .expect("the verification must return rather than hang or overflow");
        let reasons = match &outcome {
            crate::mir::verify::FnOutcome::Incomplete { reasons, .. } => reasons.clone(),
            other => panic!("expected an incomplete outcome, got {other:?}"),
        };
        assert!(
            reasons.iter().any(|r| r.contains("path budget exhausted")),
            "the cutoff must be named; reasons were {reasons:?}"
        );
    }

    /// `count_up`: the exact MIR `rustc -O` emits for
    /// `let mut i = 0u8; while i < n { i += 1; } i`.
    ///
    /// Here the loop *is* the return value (`i` is `_0`), so a proof needs the
    /// invariant to carry the exit condition: after the loop `i >= n` and
    /// `i <= n`, hence `i == n`.
    const COUNT_UP_MIR: &str = r#"
fn count_up(_1: u8) -> u8 {
    debug n => _1;
    let mut _0: u8;
    let mut _2: bool;
    let mut _3: u8;
    scope 1 {
        debug i => _0;
    }

    bb0: {
        _0 = const 0_u8;
        goto -> bb1;
    }

    bb1: {
        _3 = copy _0;
        _2 = Lt(move _3, copy _1);
        switchInt(move _2) -> [0: bb3, otherwise: bb2];
    }

    bb2: {
        _0 = Add(copy _0, const 1_u8);
        goto -> bb1;
    }

    bb3: {
        return;
    }
}
"#;

    /// Verify an embedded MIR dump against a contract written as doc lines.
    fn verify_with(mir: &str, name: &str, contract: &str) -> crate::mir::verify::FnOutcome {
        let src = format!("{contract}pub fn {name}() {{}}\n");
        let specs = crate::mir::spec::extract(&src);
        let prog = crate::mir::parse::parse_program(mir);
        let name = name.to_string();
        // A large stack: the engine recurses through the BDD and the frontend
        // through the term graph, and the harness's default thread stack is
        // smaller than the main thread's.
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(move || {
                let f = prog.get(&name).expect("the dump must parse");
                crate::smt::with_fresh(|| crate::mir::verify::verify_function(&prog, f, &specs))
            })
            .expect("the test thread must spawn")
            .join()
            .expect("verification must return")
    }

    #[test]
    fn an_invariant_decides_a_loop_that_unwinding_could_not() {
        let out = verify_with(
            COUNT_UP_MIR,
            "count_up",
            "/// requires: n <= 4\n/// invariant: i <= n\n/// ensures: ret == n\n",
        );
        assert!(
            matches!(out, crate::mir::verify::FnOutcome::Verified { .. }),
            "the loop should be decided by its invariant, got {out:?}"
        );
    }

    /// The soundness test, and the reason the header havocs the locals it can
    /// write.
    ///
    /// `i <= n` is a *true* invariant of `count_up` -- it holds on entry and is
    /// preserved by every iteration -- so the induction itself succeeds. But it
    /// says nothing that implies `ret == 0`, and for `n = 1` the loop returns
    /// `1`, so the postcondition is false.
    ///
    /// The discriminating detail is *which* state the exit edge is checked in.
    /// The guard forces `n == 0` on the very first pass, and there `i == 0` too,
    /// so a verifier that assumed the invariant at the header and then walked the
    /// exit edge from that first-iteration state would see `ret == 0` and report
    /// a proof of a false postcondition. That is the version this test was first
    /// written against, and it *passed* -- which is how the hole was found.
    ///
    /// With the havoc the exit state is any `i` with `i <= n` and `i >= n`, and
    /// `i == n == 1` refutes the postcondition. So this must not verify. The
    /// assertion is the weak form -- "not verified" -- because the engine may
    /// report a counterexample or leave the obligation open; what it must never
    /// do is claim a proof.
    #[test]
    fn an_invariant_too_weak_for_the_postcondition_is_not_a_proof() {
        let out = verify_with(
            COUNT_UP_MIR,
            "count_up",
            "/// requires: n <= 4\n/// invariant: i <= n\n/// ensures: ret == 0\n",
        );
        assert!(
            !matches!(out, crate::mir::verify::FnOutcome::Verified { .. }),
            "a false postcondition must not verify, got {out:?}"
        );
    }

    /// An invariant that is false on entry proves nothing, and must be reported
    /// as a definite failure rather than quietly ignored.
    #[test]
    fn an_invariant_false_on_entry_is_a_failure() {
        let out = verify_with(
            COUNT_UP_MIR,
            "count_up",
            "/// requires: n <= 4\n/// invariant: i == n + 1\n/// ensures: ret == n\n",
        );
        assert!(
            matches!(out, crate::mir::verify::FnOutcome::Failed { .. }),
            "a false invariant must fail, got {out:?}"
        );
    }

    /// An invariant that is preserved but *wrong* must not verify either. This
    /// is the case a naive "assert at the back edge" gets right only if the
    /// assertion really is made; a version that skipped preservation would accept
    /// this.
    #[test]
    fn an_invariant_not_preserved_is_not_a_proof() {
        let out = verify_with(
            COUNT_UP_MIR,
            "count_up",
            "/// requires: n <= 4\n/// invariant: i == 0\n/// ensures: ret == n\n",
        );
        assert!(
            !matches!(out, crate::mir::verify::FnOutcome::Verified { .. }),
            "an invariant that is not preserved must not verify, got {out:?}"
        );
    }
}

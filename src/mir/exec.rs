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

use std::collections::{BTreeMap, BTreeSet};

use crate::mir::intrinsics::{self, Outcome};
use crate::mir::spec::{self, FieldEnv};
use crate::mir::parse::{
    BinOp, Block, Callee, Const, EnumLayout, MirFn, MirProgram, Operand, Place, Proj, Rvalue, Stmt,
    Term, Ty, UnOp, USIZE_WIDTH,
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
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Sign {
    /// The type is `i8`/`i16`/`i32`/`i64`/`i128`/`isize`.
    Signed,
    /// The type is unsigned, or has no integer signedness at all.
    Unsigned,
    /// The dump did not print enough type for the sign to be read -- a literal
    /// with no suffix, and nothing in scope to take it from.
    ///
    /// This variant is why the enum has three cases rather than two. The bug the
    /// type exists to prevent was a *default*: a site that could not read the
    /// sign fell back to unsigned, and unsigned `0 < a` on an `i8` calls
    /// `i8::MIN` the largest value. With only two variants that fallback is
    /// always available to write; with three, every signedness-sensitive site has
    /// to handle `Unknown` explicitly and the compiler names the ones that do not.
    Unknown,
}

impl Sign {
    /// The sign `ty` declares.
    ///
    /// A type with no integer signedness (`bool`, an aggregate, a reference)
    /// answers `Unsigned`, which is the right reading for *widening* it (zero
    /// fill) but not for a comparison -- but rustc gives such a type no
    /// comparison to make, so `Unsigned` is not a fallback here, it is the
    /// reading.
    pub fn of(ty: &Ty) -> Sign {
        if ty.is_signed() {
            Sign::Signed
        } else {
            Sign::Unsigned
        }
    }

    /// The sign, or `None` when it could not be read.
    ///
    /// Deliberately *not* named `is_signed`: a `bool` answer would let a
    /// signedness-sensitive site write `if v.is_signed()` and silently take the
    /// unsigned branch on `Unknown`, which is the false proof the type prevents.
    /// Every caller has to say what it does when the sign is missing.
    pub fn known(self) -> Option<bool> {
        match self {
            Sign::Signed => Some(true),
            Sign::Unsigned => Some(false),
            Sign::Unknown => None,
        }
    }

    /// The sign a bare `bool` (as the seeds and the `Indexed` store carry it)
    /// stands for. Kept as a constructor so the conversion is in one place: a
    /// `bool` read the wrong way round is exactly the bug this type exists to
    /// make impossible.
    pub fn of_bool(signed: bool) -> Sign {
        if signed {
            Sign::Signed
        } else {
            Sign::Unsigned
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub enum Val {
    /// A bit-vector of a known width, *and* the signedness its type declares.
    ///
    /// The sign lives in the value rather than beside it because the bug it
    /// prevents was precisely a signedness threaded alongside: each call site
    /// asked `operand_signedness` and a site that forgot got `Unsigned`. `0 < a`
    /// on an `i8` became an unsigned test (so `i8::MIN` read as positive), and
    /// `-1i8 as i16` zero-filled to `255` -- two reachable false proofs, both
    /// from a missing sign. Here a missing sign is a construction-site error.
    Sym(Var, Sign),
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
    /// A recursive call's arguments satisfy the function's own precondition. The
    /// call is not inlined, so the contract is *assumed* -- and the precondition is
    /// what makes that assumption an induction hypothesis rather than a
    /// restatement of the goal.
    RecursivePrecondition,
    /// The `decreases:` measure is strictly smaller at a recursive call than at
    /// entry. This is the well-founded basis the induction needs; without it the
    /// assumption would be circular.
    RecursiveDecreases,
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
            ObligationKind::RecursivePrecondition => {
                write!(f, "recursive call satisfies the precondition")
            }
            ObligationKind::RecursiveDecreases => {
                write!(f, "recursive call decreases the measure")
            }
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
            | ObligationKind::LoopInvariantPreserve
            | ObligationKind::RecursivePrecondition
            | ObligationKind::RecursiveDecreases => self.verdict.is_proved(),
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
                | ObligationKind::LoopInvariantPreserve
                | ObligationKind::RecursivePrecondition
                | ObligationKind::RecursiveDecreases => {
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
                ObligationKind::LoopInvariantInit
                | ObligationKind::LoopInvariantPreserve
                | ObligationKind::RecursivePrecondition
                | ObligationKind::RecursiveDecreases => {
                    "the property holds for no input (false on every input)".to_string()
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
    /// An element of an array reached through a *field path*: `o.a[0]` is keyed by
    /// `(local, [the field chain before the index], index)`.
    ///
    /// A separate store from [`Self::elems`] because that one is keyed by `(local, index)`
    /// only, so `o.a[0]` and `o.b[0]` would collide on `(local, 0)` -- reading the wrong
    /// array's element. And separate from [`Self::indexed`], which is keyed by local and holds
    /// an *argument*'s array or slice; a field array is not the local itself. Only elements
    /// this run explicitly wrote are served from here; a read of an element that was never
    /// written is `Unknown`, never a seed or a literal.
    elems_path: BTreeMap<(u32, Vec<u32>, u64), Val>,
    /// Tuple fields, keyed by (local, field).
    fields: BTreeMap<(u32, u32), Val>,
    /// A *nested* field path, keyed by (local, the projection chain from the
    /// local to the leaf). `o.i.v` on a `&Outer` is `(1, [0, 0])`.
    ///
    /// The single-field store cannot answer a nested path: its key is one field
    /// index, and `(((*_1).0).0)` would look up `(1, 0)` twice and return the
    /// *outer* field's value for the leaf. A path is a walk, not a field, so it
    /// gets its own store and its own key. Only paths a contract binds are
    /// seeded; a nested read the contract did not name finds nothing here and
    /// stays `Unknown`, which is the same refusal the reader gives today.
    nested: BTreeMap<(u32, Vec<u32>), Val>,
    /// Locals written as a *whole* place (an empty projection), so the call
    /// return merge can tell "the callee assigned `*v`" from "the callee left
    /// `v` alone". Copying the callee's value back unconditionally would replace
    /// the caller's variable with the callee's unseeded `Unknown` for a helper
    /// that never wrote through the reference, turning a contract the caller
    /// could have proved into an incomplete one.
    whole_writes: BTreeSet<u32>,
    /// Enum payloads, keyed by (local, variant), with the payload's width.
    /// Written by the `checked_*` model and read through a `Proj::Downcast`.
    payloads: BTreeMap<(u32, u64), (Val, u8)>,
    /// Enum tags, keyed by local, as symbolic values: `1` where the operation is
    /// defined and `0` where it is not. Not a constant, because whether
    /// `checked_add` returns `Some` depends on the operands.
    discriminants: BTreeMap<u32, Val>,
    /// Locals whose type is a reference, and which may therefore be dereferenced.
    ///
    /// A dereference is only transparent for a local the frontend introduced as a
    /// `&T` *argument*. `Ty::Ref` is modelled as its referent, so `*_1` and `_1`
    /// name the same symbolic value; that is the single-owner reading of a
    /// reference, not an aliasing model. A local that is not in this set has no
    /// such backing, and a deref of it reads `Unknown` rather than inventing a
    /// value.
    deref_ok: BTreeMap<u32, ()>,
    /// The place a reference local addresses: `_2 = &_1` records `2 -> _1`, and
    /// `_3 = &_1.0` records `3 -> _1.0`.
    ///
    /// This is what lets `*_2` read what `_2` addresses. The frontend does not
    /// track aliasing (see the module docs on scope), so a reference is modelled
    /// as the *single* place it was created from, not as a value that could be
    /// pointed anywhere: `let r = &c; r.lo` reads `c.lo`, which is sound for the
    /// shape rustc lowers a local borrow to, and `_2 = &_1; _2 = &_3` overwrites
    /// the mapping rather than keeping both. A reference this store has no entry
    /// for reads `Unknown`, which is the honest answer for a pointer whose
    /// target the run never saw.
    addressed: BTreeMap<u32, Place>,
    /// For a reference local, the *caller's* local whose address it was built from,
    /// carried across a call boundary when the reference is passed as an argument.
    ///
    /// `addressed` cannot cross a call: a callee's `&mut u8` argument is a fresh
    /// local whose `addressed` entry is the caller's place, but when the callee
    /// returns that reference the caller's destination needs a place in the
    /// *caller's* frame, and the callee's local indices mean nothing there. This
    /// records the origin in terms the caller can use -- `_3 = &mut _1` records
    /// `3 -> _1` -- so a returned reference can be resolved to the caller's storage
    /// rather than dropped. Without it `let r = identity(&mut x); *r = 5` lost the
    /// write: `_2 = identity(_3)` left `_2` with no address, `*_2 = 5` was a write to
    /// a local no caller reads, and the false `ret == 0` was **proved**.
    ref_origin: BTreeMap<u32, Place>,
    /// For a reference *argument* of the callee, the place it denotes in the
    /// *caller's* frame. The callee's local indices are meaningless to the caller,
    /// so a reference the callee returns through such a local is translated back
    /// through this map -- which is how `*c.lo_mut() = 5` finds `c.lo`.
    arg_source: BTreeMap<u32, Place>,
    /// Values addressed by an index, with a length: slice arguments (`&[T]`) and
    /// array arguments (`[T; N]`), keyed by the local the argument lives in.
    ///
    /// A slice has no length in its type, so its length is a fresh symbolic input
    /// -- it is whatever the caller passed. An array's length is the constant in
    /// its type. Either way the length is a *word* here, and the elements are
    /// distinct inputs per index, so `xs[0]` and `xs[1]` are two values and
    /// `xs[0] == xs[1]` is not provable; see `Indexed::elems`.
    indexed: BTreeMap<u32, Indexed>,
    /// The program's enum layouts, so a variant *construction* constant
    /// (`Mode::Idle`) resolves to its discriminant.
    ///
    /// Carried by value rather than borrowed: the map is small, and a borrow
    /// would put a lifetime on `Env` for every call site of `operand` -- a table
    /// read once per constant is not worth that.
    enums: BTreeMap<String, EnumLayout>,
    /// The program's named `const` items, so a use site (`_0 = const K`) folds to
    /// the literal the item was defined with instead of staying unknown. See
    /// [`crate::mir::parse::MirProgram::consts`].
    consts: BTreeMap<String, Const>,
    /// The width of each modelled enum tag, keyed by local.
    ///
    /// A tag's width is the *discriminants'*, not the dump's `isize`. Recording
    /// it here keeps `discriminant` reading the tag back at the width the
    /// contract's comparison was checked at, instead of widening a small tag to
    /// 64.
    tag_widths: BTreeMap<u32, u8>,
}

/// A modelled value with a length and elements: a slice or an array.
#[derive(Clone, Debug)]
struct Indexed {
    /// The length. A symbolic input for a slice, the type's constant for an
    /// array; the executor only needs it to be a word of `usize` width.
    len: Var,
    /// The width of one element, which is the *referent's* width (`u8` for
    /// `&[u8]` or `[u8; 4]`), not the length's. Taking it from `len` would make
    /// every element 64 bits wide and mis-size every read.
    elem_w: u8,
    /// The signedness of one element. Every element of an array or slice has the
    /// same type, so one sign serves them all; an element read out of this store
    /// carries it, which is what keeps `xs[0] < 0` a signed test on an `&[i8]`.
    elem_signed: bool,
    /// `index value -> element variable`. Only indices whose value the run can
    /// resolve can be looked up here; a symbolic index that cannot be pinned is
    /// refused rather than guessed.
    elems: BTreeMap<u64, Var>,
    /// The array's fixed length, when it is an array rather than a slice.
    ///
    /// A slice's length is a symbolic input, so there is no finite domain to
    /// enumerate and a symbolic subscript stays refused. An array's length is in
    /// its type, so `a[i]` can be modelled as an ite chain over `0..N` -- exactly,
    /// which is what this field makes possible.
    fixed_len: Option<u64>,
    /// How many steps a *slice's* symbolic chain enumerates, when the contract
    /// established that its length is within `MAX_INDEX_CHAIN`.
    ///
    /// A slice has no length in its type, so unlike `fixed_len` there is no
    /// constant to take from the type. This is `Some(MAX_INDEX_CHAIN)` only when
    /// the contract's precondition was proved to imply `len <= MAX_INDEX_CHAIN`,
    /// which is what makes enumerating that many steps an exact model of *every*
    /// index in the slice. Without it a symbolic slice subscript stays refused:
    /// the chain would have to stop somewhere, and stopping before the length
    /// would fall through to a wrong element.
    slice_steps: Option<u64>,
    /// Whether an element write invalidated the seeded elements.
    ///
    /// `elems` is seeded with one variable per element the contract named, and
    /// the ite chain is built from them. A write to an element the store cannot
    /// represent per index -- an aggregate element, or a symbolic index -- makes
    /// every element unknown rather than leaving the seeded value readable: a
    /// stale element is not a missing proof, it is a *wrong* one, and it is
    /// exactly what `a[0] = 0; a[i]` would otherwise prove. The length survives,
    /// because a write does not change it.
    poisoned: bool,
}

impl Env {
    fn new() -> Env {
        Env {
            locals: BTreeMap::new(),
            elems: BTreeMap::new(),
            elems_path: BTreeMap::new(),
            fields: BTreeMap::new(),
            nested: BTreeMap::new(),
            payloads: BTreeMap::new(),
            discriminants: BTreeMap::new(),
            deref_ok: BTreeMap::new(),
            addressed: BTreeMap::new(),
            ref_origin: BTreeMap::new(),
            arg_source: BTreeMap::new(),
            indexed: BTreeMap::new(),
            whole_writes: BTreeSet::new(),
            enums: BTreeMap::new(),
            consts: BTreeMap::new(),
            tag_widths: BTreeMap::new(),
        }
    }

    /// Same as [`Env::new`], with the program's enum layouts and `const` items
    /// attached.
    fn with_enums(enums: &BTreeMap<String, EnumLayout>, consts: &BTreeMap<String, Const>) -> Env {
        Env { enums: enums.clone(), consts: consts.clone(), ..Env::new() }
    }

    /// The element variable for `index` of an indexed value (slice or array)
    /// `local`, created on first use.
    ///
    /// Two different indices are two different variables, and the same index read
    /// twice is the same variable, which is what makes an indexed read a
    /// *function* of the index rather than an arbitrary value per read.
    fn index_elem(&mut self, local: u32, index: u64) -> Option<(Var, Sign)> {
        let s = self.indexed.get_mut(&local)?;
        if s.poisoned {
            return None;
        }
        let sign = Sign::of_bool(s.elem_signed);
        if let Some(v) = s.elems.get(&index) {
            return Some((*v, sign));
        }
        let w = s.elem_w;
        let v = smt::var(w);
        s.elems.insert(index, v);
        Some((v, sign))
    }

    /// The ite chain standing for `a[i]` on a fixed-length array or on a slice
    /// whose length the contract bounded, or `None` when neither applies.
    ///
    /// An array has a finite domain, so `a[i]` is *exactly* `ite(i == 0, e0, ...)`
    /// over `0..N`. Every element is created if it does not exist yet, so the
    /// chain is a function of `i` and the same `i` read twice is the same value.
    /// The caller must be under `i < N`: the bounds assert rustc emits supplies
    /// that, and without it the chain would fall through to the last element,
    /// which is a wrong value rather than a missing one.
    ///
    /// A slice's length is symbolic, so there is no type length to enumerate. Its
    /// chain enumerates `0..MAX_INDEX_CHAIN`, which is exact for *every* index the
    /// slice can hold -- and therefore for the index the body reads -- but only
    /// because the contract established `len <= MAX_INDEX_CHAIN` first. Without
    /// that the entry is absent and this returns `None`, which is the refusal a
    /// slice's symbolic subscript had before.
    fn index_chain(&mut self, local: u32, index: Var) -> Option<Val> {
        let (n, elem_w, elem_signed) = {
            let s = self.indexed.get(&local)?;
            // An array's steps come from its type; a slice's from the contract.
            (s.fixed_len.or(s.slice_steps)?, s.elem_w, s.elem_signed)
        };
        if n > crate::mir::spec::MAX_INDEX_CHAIN {
            return None;
        }
        let mut elems = Vec::with_capacity(n as usize);
        for k in 0..n {
            elems.push(self.index_elem(local, k)?.0);
        }
        let mut chain = smt::word(0, elem_w);
        for k in (0..n).rev() {
            chain = smt::ite(smt::eq_const(index, k), elems[k as usize], chain);
        }
        // The chain's *value* is an element, so it carries the element's sign.
        Some(Val::Sym(chain, Sign::of_bool(elem_signed)))
    }

    /// Read `(*_1)[_2]` — an indexed element (a slice or an array) subscripted by
    /// a local.
    ///
    /// Returns `None` when the place is not an indexed read at all, so the caller
    /// falls through to the ordinary path; returns `Some(Unknown)` when it *is*
    /// one but the index cannot be pinned, so an unresolvable subscript is a
    /// missing value rather than an arbitrary element.
    ///
    /// The element is created on first read, which is why this takes `&mut self`
    /// and `get` cannot: the first read of `xs[0]` has no variable yet, and the
    /// second read must find the same one.
    fn read_indexed(&mut self, p: &Place) -> Option<Val> {
        if !self.indexed.contains_key(&p.local) {
            return None;
        }
        // An element write this store could not represent per index leaves every
        // element unknown, so the read is a missing value rather than the seeded
        // one the body overwrote.
        if self.indexed.get(&p.local).is_some_and(|s| s.poisoned) {
            return Some(Val::Unknown);
        }
        let index = match p.proj.as_slice() {
            [Proj::Deref, Proj::Index(k)] | [Proj::Index(k)] => *k,
            [Proj::Deref, Proj::IndexVar(li)] | [Proj::IndexVar(li)] => {
                match self.locals.get(li) {
                    Some(Val::Sym(v, _)) => {
                        let v = *v;
                        match smt::evaluate(v, |_| None) {
                            Some(k) => k,
                            // A symbolic index on an array or on a
                            // contract-bounded slice is modelled as an ite chain;
                            // on an unbounded slice there is no finite domain, so
                            // the element is genuinely unknown and stays a refusal.
                            None => return self.index_chain(p.local, v),
                        }
                    }
                    _ => return Some(Val::Unknown),
                }
            }
            _ => return None,
        };
        Some(match self.index_elem(p.local, index) {
            Some((v, sign)) => Val::Sym(v, sign),
            None => Val::Unknown,
        })
    }

    /// Rewrite a place whose head is a dereference of an addressed local, so
    /// `_2 = &_1; *_2` reads `_1`.
    ///
    /// The rewrite is a *substitution*, not a copy of the value: `*_2` becomes
    /// the place `_2` addresses, so a later write through the reference and a
    /// later read of the target meet in one store, which is the whole point of
    /// borrowing. `_2 = &_1.0; (*_2)` becomes `_1.0`, and a reference to a
    /// reference (`_4 = &(*_2)`) resolves again, which the loop allows for. The
    /// bound is the same shape as the other unwind bounds: a chain longer than
    /// this is a shape the frontend does not produce, and stopping leaves the
    /// deref to read `Unknown` rather than looping.
    ///
    /// A deref of a local that is *not* in `addressed` is left alone, so the
    /// `deref_ok` argument case (`_1: &[u8]`, `*_1`) still reaches `get`'s own
    /// `Proj::Deref` arm.
    fn resolve(&self, p: &Place) -> Place {
        let mut cur = p.clone();
        for _ in 0..8 {
            if !matches!(cur.proj.first(), Some(Proj::Deref)) {
                break;
            }
            let Some(target) = self.addressed.get(&cur.local) else { break };
            let mut proj = target.proj.clone();
            proj.extend_from_slice(&cur.proj[1..]);
            cur = Place { local: target.local, proj };
        }
        cur
    }

    /// Follow one level of *value* indirection: the place a pointer local's
    /// value addresses.
    ///
    /// This is the step `resolve` deliberately does not take. `resolve` rewrites
    /// an explicit `*_2`; `pointee` answers "where does `_2` point", which is what
    /// `PtrMetadata(_2)` asks -- the metadata belongs to the pointee, not to the
    /// pointer. A local with no recorded address is returned unchanged, so the
    /// `&[T]` argument case (`_1` is the slice) falls through to `indexed`.
    fn pointee(&self, p: &Place) -> Place {
        let r = self.resolve(p);
        match (r.proj.is_empty(), self.addressed.get(&r.local)) {
            (true, Some(t)) => self.resolve(t),
            _ => r,
        }
    }

    /// A place whose `IndexVar` steps are replaced by the literal they hold *in
    /// this frame*.
    ///
    /// A returned reference's origin is a place in the callee's terms, and a
    /// `&mut self.a[0]` records the *local* that held `0` -- `_2` -- not the
    /// literal, because `_2` is the index the dump names. That local dies at the
    /// call boundary, so a caller that translates the origin gets a place no
    /// `elems_path` entry is ever keyed by, and a write through the returned
    /// reference is dropped. Resolving the index here, while the callee's locals
    /// are still live, turns it into the literal the caller's store agrees on.
    ///
    /// A symbolic index is left as it is: its value is not a single element the
    /// caller could name either, so refusing to pin it is what keeps the write
    /// from landing on an arbitrary element.
    fn pin_index_vars(&self, p: &Place) -> Place {
        let mut proj = p.proj.clone();
        for step in &mut proj {
            if let Proj::IndexVar(li) = step {
                if let Some(Val::Sym(x, _)) = self.locals.get(li) {
                    if let Some(k) = smt::evaluate(*x, |_| None) {
                        *step = Proj::Index(k);
                    }
                }
            }
        }
        Place { local: p.local, proj }
    }

    /// Move the parts stored under `src` to `dst`, re-rooting them when either place is
    /// nested, and report whether there were any.
    ///
    /// This generalises [`Self::copy_parts`], which is the whole-place-to-whole-place case and
    /// carries the element, payload, tag and index stores as well. This one is reached when a
    /// nested place is on at least one side, and it moves the two field-shaped stores:
    ///
    /// - a struct literal into a nested field, `o.i = InnerBox { v: 9 }` -> `(_1.0) = move _2`
    ///   (whole source, nested destination);
    /// - a nested-to-nested move, `o.i = o.j` -> `_2 = move (_1.1); (_1.0) = move _2` (the
    ///   first step is a nested source into a whole temp, the second a whole source into a
    ///   nested destination).
    ///
    /// [`Self::copy_parts`] is reached only when both places are whole, so without this the
    /// parts never land under the nested place and the later read (`(_1.0).0`, the nested
    /// store keyed by the whole chain) finds nothing. The body's value is then unknown, and a
    /// contract that *is* false of the body is reported unreadable instead of refuted.
    ///
    /// Both projections are read as field paths (`field_steps`), and both are *resolved*
    /// first, so a write through a reference (`((*_1).0) = move _2`) reaches the target's
    /// field path rather than stopping at the leading deref -- what makes the write and the
    /// read meet in one store. Any other projection (an index, a downcast, a second deref)
    /// names a store this helper does not re-root, and writing a part where no read consults
    /// it would be a lost proof at best, so those are refused.
    ///
    /// A part is re-keyed relative to the source's own path: the entry at `(src.local, sp)`
    /// (or the single-field entry whose key *is* `sp`) is the value at `src`, and it lands at
    /// the destination's path. A whole destination replaces every part it had, so its old
    /// parts are dropped first; a nested destination keeps its siblings, because only the
    /// paths under it are being written. A path that re-roots to the whole local (a field of
    /// one moved into a whole place) becomes the local's value.
    fn rebase_parts(&mut self, src: &Place, dst: &Place) -> bool {
        let src = self.resolve(src);
        let dst = self.resolve(dst);
        let Some(sp) = field_steps(&src.proj) else { return false };
        let Some(dp) = field_steps(&dst.proj) else { return false };
        if src.local == dst.local && sp == dp {
            return false;
        }
        let s = src.local;
        // The source's parts, keyed relative to the source's own path. The `nested` store is
        // the chain-shaped one (length two or more) and the `fields` store the single-field
        // one; a source path `sp` selects the entries under it, and the entry *at* it (a
        // single-field source) is the whole moved value.
        let mut rels: Vec<(Vec<u32>, Val)> = Vec::new();
        for ((l, chain), v) in &self.nested {
            if *l == s {
                if let Some(tail) = chain.strip_prefix(sp.as_slice()) {
                    rels.push((tail.to_vec(), *v));
                }
            }
        }
        for ((l, k), v) in &self.fields {
            if *l != s {
                continue;
            }
            if sp.is_empty() {
                rels.push((vec![*k], *v));
            } else if sp.as_slice() == [*k] {
                rels.push((Vec::new(), *v));
            }
        }
        // Elements of field-path arrays under the source path move with the value, re-keyed the
        // same way. An element *at* the source path (its chain equals `sp`) is an element of the
        // whole destination value, which the plain `elems` store answers; a deeper one keeps its
        // tail under the destination path.
        let mut elem_rels: Vec<(Vec<u32>, u64, Val)> = Vec::new();
        for ((l, chain, k), v) in &self.elems_path {
            if *l == s {
                if let Some(tail) = chain.strip_prefix(sp.as_slice()) {
                    elem_rels.push((tail.to_vec(), *k, *v));
                }
            }
        }
        // A whole-local array's elements live in `elems`, not `elems_path`, and they move with
        // the value too. Without this, an array that is a struct *field* built by a literal
        // (`ArrInner { a: [9, 1, 2, 3] }`) lost its elements at the assignment: `_2.0` held the
        // array's value but not its parts, so `o.i.a[0]` read `Unknown` and the contract stayed
        // `Incomplete` in both directions -- a coverage hole, not a false proof, since a missing
        // value proves nothing. Only a *whole* source has `elems` (a nested source's elements
        // are in `elems_path` and are handled above), so this is gated on an empty `sp`.
        let mut whole_elem_rels: Vec<(u64, Val)> = Vec::new();
        if sp.is_empty() {
            for ((l, k), v) in &self.elems {
                if *l == s {
                    whole_elem_rels.push((*k, *v));
                }
            }
        }
        let any = !rels.is_empty() || !elem_rels.is_empty() || !whole_elem_rels.is_empty();
        // A whole destination is replaced outright, so its previous parts must not survive; a
        // nested destination keeps the parts outside the written path.
        if dp.is_empty() && s != dst.local {
            self.forget_parts(dst.local);
        } else if !dp.is_empty() {
            self.elems_path
                .retain(|(l, c, _), _| *l != dst.local || !c.starts_with(dp.as_slice()));
        }
        for (tail, k, v) in elem_rels {
            let mut full = dp.clone();
            full.extend(tail);
            if full.is_empty() {
                self.elems.insert((dst.local, k), v);
            } else {
                self.elems_path.insert((dst.local, full, k), v);
            }
        }
        // A whole-local element of the source lands on the destination at the same shape: a
        // whole destination takes it as a whole-local element, and a nested destination takes
        // it under the destination's field chain.
        for (k, v) in whole_elem_rels {
            if dp.is_empty() {
                self.elems.insert((dst.local, k), v);
            } else {
                self.elems_path.insert((dst.local, dp.clone(), k), v);
            }
        }
        for (rel, v) in rels {
            let mut full = dp.clone();
            full.extend(rel);
            match full.len() {
                // The value *at* the source path becomes the whole destination value.
                0 => {
                    self.locals.insert(dst.local, v);
                }
                1 => {
                    self.fields.insert((dst.local, full[0]), v);
                }
                _ => {
                    self.nested.insert((dst.local, full), v);
                }
            }
        }
        any
    }

    /// Copy every derived part of `src`'s local onto `dst`, and report whether the
    /// source had any.
    ///
    /// A whole-struct assignment (`c = d`) copies a value the frontend models as
    /// its *parts*: `d`'s fields live in `fields`, not in `locals`, and `d` itself
    /// is a struct with no bit-vector meaning. Copying only the local would move an
    /// `Unknown` and leave `c.lo` reading nothing, which is why
    /// `c = d; c.lo` stayed unreadable. Copying the parts is what makes the
    /// assignment mean what it says.
    ///
    /// The destination's own parts are dropped first: a whole-value assignment
    /// replaces all of them, so a field the source does not carry must not survive
    /// from the destination's previous value -- that stale field is a *wrong*
    /// value, and it is the failure mode this store guards against everywhere else.
    fn copy_parts(&mut self, src: &Place, dst: u32) -> bool {
        let src = self.resolve(src);
        if !src.proj.is_empty() || src.local == dst {
            return false;
        }
        let s = src.local;
        let fields: Vec<(u32, Val)> =
            self.fields.iter().filter(|((l, _), _)| *l == s).map(|((_, k), v)| (*k, *v)).collect();
        let elems: Vec<(u64, Val)> =
            self.elems.iter().filter(|((l, _), _)| *l == s).map(|((_, k), v)| (*k, *v)).collect();
        let payloads: Vec<(u64, (Val, u8))> =
            self.payloads.iter().filter(|((l, _), _)| *l == s).map(|((_, k), v)| (*k, *v)).collect();
        let disc = self.discriminants.get(&s).copied();
        let indexed = self.indexed.get(&s).cloned();
        // Nested paths are parts too, keyed by the local *and* the chain. A copy
        // that moved only the single-field parts would leave `c`'s own `c.i.v`
        // seed in place after `c = d`, so a later `c.i.v` would read `c`'s
        // pre-copy leaf rather than `d`'s -- the same stale-part hole, one level
        // down, and a false refutation of the true contract `d.i.v == 1`.
        let nested: Vec<(Vec<u32>, Val)> = self
            .nested
            .iter()
            .filter(|((l, _), _)| *l == s)
            .map(|((_, chain), v)| (chain.clone(), *v))
            .collect();
        // Elements of a field-path array are parts of the local too: `c = d` has to carry
        // `d.a[0]` to `c.a[0]`, or a later read of the destination's element finds nothing (or,
        // worse, the destination's own pre-copy element).
        let path_elems: Vec<(Vec<u32>, u64, Val)> = self
            .elems_path
            .iter()
            .filter(|((l, _, _), _)| *l == s)
            .map(|((_, chain, k), v)| (chain.clone(), *k, *v))
            .collect();
        let any = !fields.is_empty()
            || !elems.is_empty()
            || !payloads.is_empty()
            || !nested.is_empty()
            || !path_elems.is_empty()
            || disc.is_some()
            || indexed.is_some();
        self.forget_parts(dst);
        for (chain, v) in nested {
            self.nested.insert((dst, chain), v);
        }
        for (chain, k, v) in path_elems {
            self.elems_path.insert((dst, chain, k), v);
        }
        for (k, v) in fields {
            self.fields.insert((dst, k), v);
        }
        for (k, v) in elems {
            self.elems.insert((dst, k), v);
        }
        for (k, v) in payloads {
            self.payloads.insert((dst, k), v);
        }
        if let Some(d) = disc {
            self.discriminants.insert(dst, d);
        }
        if let Some(ix) = indexed {
            self.indexed.insert(dst, ix);
        }
        any
    }

    fn get(&self, p: &Place) -> Val {
        let resolved = self.resolve(p);
        let p = &resolved;
        // A nested field path is a walk, not a field: `(((*_1).0).0)` must not be
        // answered by looking up the *outer* field `(1, 0)` twice, which would
        // return `o.i` for `o.i.v` -- a wrong value, not a missing one. So a chain
        // of two or more fields is answered *only* out of the nested store, and a
        // path no contract bound reads `Unknown`. The single-field walk below is
        // deliberately not consulted: it is keyed by one field index and would
        // return the intermediate aggregate for the leaf.
        if let Some(chain) = field_chain(&p.proj) {
            return self.nested.get(&(p.local, chain)).copied().unwrap_or(Val::Unknown);
        }
        let mut cur = match self.locals.get(&p.local) {
            Some(v) => *v,
            // A modelled `Option` local has no entry in `locals`: its value is
            // its tag, which lives in `discriminants`. Without this fallback a
            // read of the bare local `_2` -- which is exactly what
            // `discriminant(_2)` and `move _2` lower to -- would come back
            // unknown and the `switchInt` on the tag would go unmodelled.
            None => match self.discriminants.get(&p.local) {
                Some(v) => *v,
                // A local with no whole value but with *parts*: an aggregate a
                // modelled call wrote field-by-field (`overflowing_add` writes
                // `_0.0` and `_0.1` without ever assigning `_0`), or an enum built
                // from a variant. The projections below are what carry the value,
                // so falling through to them is right; returning `Unknown` here
                // would make every such component unreadable, which is exactly how
                // a `ret.1` contract for the `overflowing_*` family was reported
                // as an aggregate with no such component. A projection-less read
                // of such a local still has no single value, and the loop below
                // leaves `cur` as this same `Unknown` for it.
                None if !p.proj.is_empty() => Val::Unknown,
                None => return Val::Unknown,
            },
        };
        // A downcast read is a read of the variant's payload. rustc emits the
        // downcast only inside the `switchInt` arm that already matched the
        // variant, so the path condition forces the tag here and no extra gate
        // is needed. What is needed is that the payload *exists*: an enum this
        // frontend did not build has no entry, and answering `Unknown` there is
        // what keeps a stale or invented payload out of the result.
        let modelled = self.discriminants.contains_key(&p.local);
        let mut i = 0;
        while i < p.proj.len() {
            cur = match &p.proj[i] {
                // A struct field lives in `fields`; a *tuple* component lives in
                // `elems`, because `_3 = (a, b)` stores it under `Proj::Index` and
                // rustc prints the read back as `_3.0` (`Proj::Field`). The two
                // spellings of "component 0" have to meet in one store, or a tuple
                // local's component reads `Unknown`: `let t = (a, b); t.0` would
                // not be `a`. A local is a struct or a tuple and never both, so the
                // `elems` lookup can only ever hit for the tuple case, and a struct
                // whose field is genuinely unwritten finds nothing in either store
                // and stays `Unknown`.
                Proj::Field(f) => match self.fields.get(&(p.local, *f)) {
                    Some(v) => *v,
                    None => *self.elems.get(&(p.local, *f as u64)).unwrap_or(&Val::Unknown),
                },
                // An indexed element. `elems` is the array-literal map, keyed by
                // a concrete index; a slice's or array *argument*'s elements live
                // under `indexed` instead. The two must not be confused, so the
                // `indexed` lookup is tried first and only for a local that *is*
                // one.
                Proj::Index(k) => match self.indexed.get(&p.local) {
                    Some(s) if s.poisoned => Val::Unknown,
                    Some(s) => match s.elems.get(k) {
                        Some(v) => Val::Sym(*v, Sign::of_bool(s.elem_signed)),
                        // Not read yet. `get` takes `&self` and so cannot create
                        // the element; the operand path goes through
                        // `read_indexed`, which can, and does so before this
                        // is reached. Answering `Unknown` here is the fallback
                        // for a caller that did not.
                        None => Val::Unknown,
                    },
                    // An element of an array reached through a *field path*: `o.a[0]` is keyed
                    // by `(local, the field chain before the index, index)`. The path form is
                    // tried first; a whole-local array has an empty chain, which is the plain
                    // `o[0]` case the `elems` map below answers. Only an element this run
                    // explicitly wrote is served; a path no write reached is `Unknown`, never a
                    // seed or a literal, so `o.a[0]` cannot read a value the body never stored.
                    None => {
                        let chain = field_steps(&p.proj[..i]).unwrap_or_default();
                        if chain.is_empty() {
                            // A whole-local array (an array literal): the plain `elems` map
                            // keeps answering it, exactly as before.
                            *self.elems.get(&(p.local, *k)).unwrap_or(&Val::Unknown)
                        } else {
                            *self
                                .elems_path
                                .get(&(p.local, chain, *k))
                                .unwrap_or(&Val::Unknown)
                        }
                    }
                },
                // `(*_1)[_2]` — a subscript that is a local. The element is
                // looked up by the index's *value*: a constant index names one
                // element, and a symbolic index names none the run can pin, so it
                // reads `Unknown` rather than an arbitrary element. Reading an
                // arbitrary element would make `xs[i]` a different value per
                // read, which is a wrong proof waiting to happen.
                Proj::IndexVar(li) => {
                    let sym = match self.locals.get(li) {
                        Some(Val::Sym(v, _)) => Some(*v),
                        _ => None,
                    };
                    match sym.and_then(|v| smt::evaluate(v, |_| None)) {
                        Some(k) => match self.indexed.get(&p.local) {
                            Some(s) if s.poisoned => Val::Unknown,
                            Some(s) => {
                                let sign = Sign::of_bool(s.elem_signed);
                                s.elems.get(&k).map(|v| Val::Sym(*v, sign)).unwrap_or(Val::Unknown)
                            }
                            None => {
                                let chain = field_steps(&p.proj[..i]).unwrap_or_default();
                                if chain.is_empty() {
                                    *self.elems.get(&(p.local, k)).unwrap_or(&Val::Unknown)
                                } else {
                                    *self
                                        .elems_path
                                        .get(&(p.local, chain, k))
                                        .unwrap_or(&Val::Unknown)
                                }
                            }
                        },
                        // A symbolic subscript: `get` takes `&self`, so it cannot
                        // create the elements the chain needs. The operand path
                        // goes through `read_indexed`, which can, and does so
                        // first; this is the fallback for a caller that did not.
                        None => Val::Unknown,
                    }
                }
                Proj::Deref => {
                    // The frontend does not track aliasing, so a dereference is
                    // only meaningful when the pointee *is* the local: `_1` is the
                    // `&Config` argument and `*_1` is the `Config` it names, which
                    // the executor already holds under `_1` because `Ty::Ref` is
                    // modelled as its referent.
                    //
                    // `i == 0` is load-bearing. A deref that follows a projection
                    // -- `*(_1.0)`, a field that is itself a reference -- is a
                    // *different* pointee, and `deref_ok` says nothing about it
                    // (it is keyed on the local, and the local's referent is not
                    // the field's). Letting that through would read the field as
                    // though it were the argument's referent, which is a wrong
                    // value rather than a missing one.
                    if i != 0 || !self.deref_ok.contains_key(&p.local) {
                        return Val::Unknown;
                    }
                    i += 1;
                    continue;
                }
                Proj::Downcast(v) => {
                    if !modelled {
                        return Val::Unknown;
                    }
                    // The downcast *and* the payload field it addresses are one
                    // step: `((_2 as Some).0)`. Both projections are consumed
                    // here, so the loop must skip the `Field(0)` as well --
                    // letting it run would look the payload up in the tuple map
                    // and replace a good value with `Unknown`. Anything other
                    // than a lone payload field is a shape the model does not
                    // produce, so it reads as unknown rather than walking on.
                    if !matches!(p.proj.get(i + 1), Some(Proj::Field(0)) | None) {
                        return Val::Unknown;
                    }
                    i += 1;
                    self.payloads.get(&(p.local, *v)).map(|(val, _)| *val).unwrap_or(Val::Unknown)
                }
            };
            i += 1;
        }
        cur
    }

    fn set(&mut self, p: &Place, v: Val) {
        // A write through a reference (`(*_2).0 = v`) belongs to the place `_2`
        // addresses, not to `_2`; resolving here is what makes the write and the
        // read of the target meet in one store.
        let resolved = self.resolve(p);
        let p = &resolved;
        // A write to the *whole* referent through a reference -- `(*_1) = v`, how
        // `*v = 5` lowers for `v: &mut u8` -- is a whole-place write to `_1`,
        // because `Ty::Ref` is modelled as its referent (`_1` *is* the value
        // `*_1` names). Stripping the lone deref here lets it share the whole-place
        // arm below. Only a lone deref of a deref-ok local qualifies: `(*_1)[0] = v`
        // and `(*_1).0 = v` keep their projection and reach their own arms, and a
        // deref of a local with no recorded referent stays unresolved.
        //
        // This strip was missing, and its absence was a false proof: `*v = 5; *v`
        // on a `&mut u8` dropped the write, the read returned the seed, and
        // `requires: v == 0` / `ensures: ret == 0` was **proved** against a body
        // that returns 5.
        let stripped;
        let p = if p.proj.as_slice() == [Proj::Deref] && self.deref_ok.contains_key(&p.local) {
            stripped = Place { local: p.local, proj: Vec::new() };
            &stripped
        } else {
            p
        };
        if p.proj.is_empty() {
            // A whole-place assignment replaces the value *and* every part of it
            // the environment holds separately. The field, element, payload and
            // tag maps are keyed by local and are not touched by a plain
            // `locals` write, so leaving them would let a later read of `c.x`
            // return the value the argument *had* -- which is how `c = d; c.x`
            // proved `ret == c.x` against the stale `c.x`. A derived part of a
            // value that is no longer there is a wrong value, not a missing one,
            // so the parts are dropped here rather than read later.
            //
            // `Val::Agg` is the exception, and it is load-bearing: an aggregate
            // rvalue (`_0 = (a, b)`, or the `(result, overflowed)` tuple of a
            // `checked_*`) *writes its parts itself* inside `eval_rvalue` and
            // then hands back `Val::Agg` as the local's value. Clearing here
            // would delete the parts that were just written, which turns a
            // modelled tuple back into an unknown one.
            if !matches!(v, Val::Agg) {
                self.forget_parts(p.local);
            }
            self.whole_writes.insert(p.local);
            self.locals.insert(p.local, v);
            return;
        }
        match p.proj.as_slice() {
            [Proj::Field(i)] => {
                self.fields.insert((p.local, *i), v);
                // A write to the aggregate `o.i` makes every nested path through it
                // describe a value that is no longer there. `o.i.v` is seeded
                // separately, so leaving it would let a later read return the
                // pre-write leaf -- the same stale-part hole the whole-local write
                // closes, one level down.
                self.forget_nested_under(p.local, &[*i]);
            }
            // An element write to a slice or array argument has to land in the
            // *same* store the read consults. Writing it to `elems` -- the
            // array-literal map -- left the read looking at the seeded value, so
            // `a[0] = 0; a[i]` proved `ret == a[i]` against the pre-write `a[0]`:
            // a false contract, proved.
            [Proj::Index(i)] => self.write_elem(p.local, *i, v),
            // `_1[_2] = v` -- a symbolic subscript. Only a constant index has a
            // per-index slot; a symbolic one would have to update every element
            // the chain could select, which this store does not model, so it
            // poisons instead of guessing.
            [Proj::IndexVar(li)] | [Proj::Deref, Proj::IndexVar(li)] => {
                match self.locals.get(li) {
                    Some(Val::Sym(x, _)) => match smt::evaluate(*x, |_| None) {
                        Some(k) => self.write_elem(p.local, k, v),
                        None => self.poison_elems(p.local),
                    },
                    _ => self.poison_elems(p.local),
                }
            }
            // `(*_1)[0] = v` -- how a write to a `&mut [T]` or `&mut [T; N]`
            // argument lowers. The deref is transparent for an argument, so the
            // element belongs to the same store `read_indexed` consults.
            [Proj::Deref, Proj::Index(i)] => self.write_elem(p.local, *i, v),
            // `(*_1).0 = v` -- how a write to a field through a `&mut` argument
            // lowers. `resolve` has already collapsed `(*_1).0` to `_1.0` when the
            // argument is one, so this arm is reached only for a reference *local*
            // whose target is not recorded, and the field belongs to the same
            // store the read consults.
            //
            // This arm was missing, and its absence was a false proof, not a lost
            // proof: `c.lo = 5; c.lo` on a `&mut Config` dropped the write, the
            // read returned the *seed*, and `requires: c.lo == 0` / `ensures: ret
            // == 0` was **proved** against a body that returns 5.
            [Proj::Deref, Proj::Field(i)] => {
                self.fields.insert((p.local, *i), v);
                self.forget_nested_under(p.local, &[*i]);
            }
            // A nested write through a reference: `((*_1).0).0 = v` falls to the
            // catch-all below, which strips the leading deref before building the
            // chain. A deref followed by something that is *not* all fields (an
            // index, a downcast) must reach that same catch-all rather than being
            // swallowed here, or an indexed local would be left stale instead of
            // poisoned.
            [Proj::Downcast(variant), Proj::Field(0)] | [Proj::Downcast(variant)] => {
                self.payloads.insert((p.local, *variant), (v, 0));
            }
            // A nested field write: `((_1.0).0) = v`. Keyed by the whole chain, so
            // it lands in the same store the nested read consults. A chain that is
            // not all field projections (an index, a downcast) is left to the
            // catch-all, which poisons an indexed local rather than guessing.
            rest => {
                if let Some(chain) = field_chain(rest) {
                    self.forget_nested_under(p.local, &chain);
                    self.nested.insert((p.local, chain), v);
                    return;
                }
                // An element of an array reached through a field path: `(_1.0)[k] = v`. The
                // whole projection is the key, so `o.a[0]` and `o.b[0]` cannot collide. The
                // write replaces that element and leaves the siblings; the element's *type*
                // was not seeded, so a read of an element this run did not write stays
                // `Unknown` rather than inventing a value.
                if let [fields @ .., last] = rest {
                    let index = match last {
                        Proj::Index(k) => Some(*k),
                        // A symbolic subscript is only writable when the run can pin its
                        // value; otherwise the store cannot say which element changed, so the
                        // whole path is dropped rather than left stale.
                        Proj::IndexVar(li) => match self.locals.get(li) {
                            Some(Val::Sym(x, _)) => smt::evaluate(*x, |_| None),
                            _ => None,
                        },
                        _ => None,
                    };
                    if let Some(chain) = field_steps(fields) {
                        if !chain.is_empty() {
                            match index {
                                Some(k) => {
                                    self.write_elem_at(p.local, chain, k, v);
                                    return;
                                }
                                None => {
                                    self.elems_path.retain(|(l, c, _), _| {
                                        *l != p.local || c.as_slice() != chain.as_slice()
                                    });
                                    return;
                                }
                            }
                        }
                    }
                }
                // A shape the arms above do not cover. `*a = v` (a whole-store
                // write through a `&mut [T; N]`) would need a new store, so it is
                // dropped. For an indexed local that leaves the store describing a
                // value that is no longer there, so it is poisoned rather than left
                // stale -- and `poison_elems` records the write, so a `&mut` caller
                // sees the poison rather than its pre-call elements.
                if self.indexed.contains_key(&p.local) {
                    self.poison_elems(p.local);
                }
            }
        }
    }

    /// Drop every part of `local` the environment holds separately from the
    /// local's own value: fields, elements, payloads and the enum tag.
    ///
    /// Called when the local is overwritten as a whole, because the parts then
    /// describe a value that is no longer there. The *length* of an indexed local
    /// is kept: it is a property of the type, not of the value, so a reassigned
    /// array still has its `N`.
    /// Drop every nested path through `prefix` for `local`.
    ///
    /// Called when an *intermediate* aggregate is overwritten (`o.i = ...`), so the
    /// seeded leaves under it (`o.i.v`) no longer describe the value in the store.
    /// A stale part is a wrong value, not a missing one, so it is dropped rather
    /// than read later.
    fn forget_nested_under(&mut self, local: u32, prefix: &[u32]) {
        self.nested
            .retain(|(l, chain), _| *l != local || !chain.starts_with(prefix));
        // The elements of an array reached through this prefix describe a value that is no
        // longer there once the intermediate aggregate is overwritten, so they are dropped too.
        // A stale element is a wrong value, not a missing one.
        self.elems_path.retain(|(l, chain, _), _| *l != local || !chain.starts_with(prefix));
    }

    fn forget_parts(&mut self, local: u32) {
        self.fields.retain(|(l, _), _| *l != local);
        self.nested.retain(|(l, _), _| *l != local);
        self.elems.retain(|(l, _), _| *l != local);
        // Elements of field-path arrays under a whole-value write describe a value that is no
        // longer there; keeping them would be a stale read of the old array.
        self.elems_path.retain(|(l, _, _), _| *l != local);
        self.payloads.retain(|(l, _), _| *l != local);
        self.discriminants.remove(&local);
        self.tag_widths.remove(&local);
        if let Some(s) = self.indexed.get_mut(&local) {
            s.elems.clear();
            // The seeded elements are gone, so a later read must not find them.
            // Poisoning is the honest state: the store cannot say what the
            // elements are now, only that it does not know.
            s.poisoned = true;
        }
    }

    /// Record an element write in whichever store the read for `local` consults.
    ///
    /// A slice or array argument's elements live in `indexed`; an array *literal*'s
    /// live in `elems`. The read path keys on the same distinction, so the two
    /// must agree here or a write becomes invisible to the read.
    fn write_elem(&mut self, local: u32, index: u64, v: Val) {
        match self.indexed.get_mut(&local) {
            Some(s) => match v {
                Val::Sym(x, _) => {
                    s.elems.insert(index, x);
                }
                // An aggregate element, or an unmodelled one. The element is no
                // longer the seeded input, and this store cannot hold what it is
                // now; keeping the seed would be a stale read, so it poisons.
                _ => s.poisoned = true,
            },
            None => {
                self.elems.insert((local, index), v);
            }
        }
    }

    /// Mark every element of `local` unknown, keeping the length.
    fn poison_elems(&mut self, local: u32) {
        match self.indexed.get_mut(&local) {
            Some(s) => s.poisoned = true,
            // A literal array written through a symbolic subscript: the whole
            // literal is unmodelled now, so its elements are dropped rather than
            // left stale.
            None => self.elems.retain(|(l, _), _| *l != local),
        }
    }

    /// Mark every element of the array at `chain` under `local` unknown.
    ///
    /// A write through a returned reference whose index the run cannot pin may land
    /// on *any* element, so none of them can be trusted afterwards. Which store
    /// holds them depends on the shape: an array reached through a field path
    /// (`x.a[0]`, the field chain *before* the index) is in `elems_path`, a
    /// whole-local literal array is in `elems`, and a whole-local array *argument*
    /// is in `indexed`. All three are cleared under the path, and a whole-local
    /// array keeps its length.
    fn poison_array_under(&mut self, local: u32, chain: &[u32]) {
        if chain.is_empty() {
            self.poison_elems(local);
        } else {
            self.elems_path.retain(|(l, c, _), _| *l != local || !c.starts_with(chain));
        }
    }

    /// Record an element of an array reached through a field path, `o.a[k] = v`.
    ///
    /// The whole path is the key, so `o.a[0]` and `o.b[0]` cannot collide. Any
    /// previous value at that element is replaced; siblings are untouched.
    fn write_elem_at(&mut self, local: u32, chain: Vec<u32>, index: u64, v: Val) {
        self.elems_path.retain(|(l, c, k), _| *l != local || *c != chain || *k != index);
        self.elems_path.insert((local, chain, index), v);
    }

    /// Record the payload of a modelled `Option`, with its width.
    ///
    /// The width is what `discriminant` and the payload read are sized by. It is
    /// the operand width, because `checked_add` on a `u8` produces a `u8`
    /// payload: sizing it from the destination would size it from the
    /// `Option<u8>` local.
    fn set_payload(&mut self, local: u32, variant: u64, v: Val, width: u8) {
        self.payloads.insert((local, variant), (v, width));
    }

    /// The width of a modelled enum tag, when one was seeded for `local`.
    ///
    /// A seeded tag knows its own width (the discriminants'); a synthesised
    /// `Option` tag does not and falls back to the payload's width.
    fn tag_width(&self, local: u32) -> Option<u8> {
        self.tag_widths.get(&local).copied()
    }

    /// The width of a modelled `Option` local, from its payload.
    fn option_width(&self, local: u32) -> Option<u8> {
        self.payloads
            .iter()
            .find(|((l, _), _)| *l == local)
            .map(|(_, (_, w))| *w)
    }

    /// Record an enum tag for a local.
    fn set_discriminant(&mut self, local: u32, tag: Val) {
        // The width is taken from the tag's own value, so a seeded tag keeps the
        // discriminants' width its contract was checked at and a synthesised
        // `Option` tag keeps the operand's. Deriving it here rather than at each
        // read site is what keeps `discriminant` and the payload in one width.
        if let Val::Sym(v, _) = tag {
            self.tag_widths.insert(local, smt::bits(v));
        }
        self.discriminants.insert(local, tag);
    }
}

/// The field chain a projection run denotes, if every step is a field access.
///
/// `(((*_1).0).0)` has the projections `[Deref, Field(0), Field(0)]`; the deref
/// is transparent for an argument (its referent is the local itself), so the chain
/// is `[0, 0]`. A run that is not all fields -- an index, a downcast, a deref in
/// the middle -- returns `None`, because those name a different store and must not
/// be answered out of the nested one.
///
/// A *single* field is not a chain here: `[_1.0]` returns `None` so the
/// single-field store keeps answering it, and the two stores stay disjoint.
fn field_chain(proj: &[Proj]) -> Option<Vec<u32>> {
    let chain = field_steps(proj)?;
    if chain.len() < 2 {
        return None;
    }
    Some(chain)
}

/// A projection read as a chain of field indices, stripping one leading `Deref`.
///
/// `None` for any step that is not a field (an index, a downcast, a second deref): those
/// name a store the caller does not re-root. An empty chain is a whole place, which is
/// `Some(vec![])` -- the caller decides whether that is meaningful.
fn field_steps(proj: &[Proj]) -> Option<Vec<u32>> {
    let steps = match proj.first() {
        Some(Proj::Deref) => &proj[1..],
        _ => proj,
    };
    let mut chain = Vec::with_capacity(steps.len());
    for s in steps {
        match s {
            Proj::Field(i) => chain.push(*i),
            _ => return None,
        }
    }
    Some(chain)
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
    /// The loop cut that was active in the *caller* when this frame made the
    /// call, put aside for the same reason `saved_env` is.
    ///
    /// A loop cut belongs to the function whose loop it describes, so entering a
    /// callee must clear it -- the caller's loop invariant says nothing about the
    /// callee's locals. But the cut has to come back on return: the resumed
    /// caller is still inside its loop, and the next edge into its header must be
    /// checked against the invariant rather than unwound. Clearing `cut` for the
    /// callee and never restoring it left the caller unwinding a loop it had
    /// already cut, so a loop whose step is a same-dump call was reported as a
    /// cutoff once it exceeded `DEFAULT_UNWIND`, even though its invariant was
    /// sufficient. That is an incompleteness, not an unsoundness -- the report is
    /// `Incomplete`, never a false proof -- but it silently discards a valid
    /// proof, which is the failure this crate treats as a defect.
    saved_cut: Option<Cut>,
    /// `(caller storage, callee local)` for each argument the caller handed over
    /// through a reference (`&T`, `&mut T`, `&[T]`, `&mut [T]`). The caller side
    /// is the *place* the reference names -- `_2` for `set5(&mut x)` -- not the
    /// reference local, which is a temp.
    ///
    /// The frontend models `&T` as its referent, so these two locals denote the
    /// same storage and the callee's post-state is copied back to the caller's
    /// local on return. A by-value argument is deliberately *not* in this list:
    /// its writes must stay in the callee's frame, or `let b = f(a)` would
    /// mutate `a` and a caller contract about `a` would be checked against the
    /// wrong value.
    ///
    /// This used to hold only the *indexed* references, so a helper that wrote a
    /// field or a scalar through a `&mut` had its write die with the frame: the
    /// caller read its own seed, and `requires: c.lo == 0; ensures: ret == 0` on
    /// `set_lo(c); c.lo` was **proved** against a body that returns 5.
    by_ref: Vec<(Place, u32)>,
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

/// Symbolic inputs a contract names, handed to the executor so that the
/// contract and the body read the *same* variables.
///
/// One struct rather than three parallel slices: the three kinds are always
/// passed together, and bundling them keeps the executor's entry point from
/// growing an argument per projection shape as more are modelled.
#[derive(Default, Clone)]
pub struct Seeds {
    /// `(local, field index, variable, signed)` for each struct field a contract
    /// names. The sign travels with the seed so the executor builds a
    /// `Val::Sym` that knows it, rather than one it has to guess at.
    pub fields: Vec<(u32, u32, Var, bool)>,
    /// `(local, projection chain, variable, signed)` for each *nested* path a
    /// contract names, so the executor's nested store holds the same variable the
    /// contract's `o.i.v` was rewritten to.
    pub nested: Vec<(u32, Vec<u32>, Var, bool)>,
    /// `(local, length variable, element width, element signed)` for each slice
    /// or array argument.
    pub lens: Vec<(u32, Var, u8, bool)>,
    /// The fixed length for each array argument, so a symbolic subscript knows
    /// the domain to enumerate. A slice has no entry, and its `xs[i]` stays
    /// refused.
    pub array_lens: Vec<(u32, u64)>,
    /// The enumeration length for each *slice* whose contract subscripted it
    /// symbolically *and* established `len <= MAX_INDEX_CHAIN`. Without an entry
    /// the executor builds no chain, so a slice subscript stays refused; the entry
    /// exists only because the caller proved the length is bounded, which is what
    /// makes a finite chain an honest model of the whole slice.
    pub slice_steps: Vec<(u32, u64)>,
    /// `(local, index, variable, signed)` for each element a contract names.
    pub elems: Vec<(u32, u64, Var, bool)>,
    /// `(local, field chain, index, variable, signed)` for each element of an array reached
    /// through a field path (`o.a[0]`) that a contract names. Keyed by the whole path, so
    /// `o.a[0]` and `o.b[0]` cannot collide.
    pub path_elems: Vec<(u32, Vec<u32>, u64, Var, bool)>,
    /// `(local, tag variable, tag width, discriminants)` for each enum-typed
    /// argument a contract names a variant of.
    ///
    /// The tag is a symbolic input whose domain is the set of variant
    /// discriminants, because a value of the enum always has one of them — a
    /// property of the type, not an assumption about the caller. The run assumes
    /// that domain on the initial path, which is what makes the `otherwise` arm of
    /// an exhaustive `match` (which rustc lowers to `unreachable`) genuinely
    /// unreachable instead of a spurious panic.
    pub tags: Vec<(u32, Var, u8, Vec<u64>)>,
    /// `(local, variant, variable, width, signed)` for each variant payload a
    /// contract names, so `m.Data` in a contract and `((_1 as Data).0)` in the
    /// body name one variable rather than two that look alike.
    pub payload_seeds: Vec<(u32, u64, Var, u8, bool)>,
    /// `(variable index, value)` for each variable the precondition pins to a
    /// constant.
    ///
    /// The variable is seeded with the literal instead of a fresh symbolic input.
    /// Sound -- every model of the precondition has it equal to that -- and it is
    /// what lets a body whose only operand is pinned build its operations on a
    /// literal, where the constant folds collapse them. Keyed by the variable's own
    /// index, so a pin applies wherever that variable is seeded: an argument (whose
    /// index is its local), a struct field, a nested path, or an element. See
    /// [`crate::smt::pinned_vars`].
    pub pins: Vec<(u32, u64)>,
}

/// The contract of the function under verification, in *text* form, so a
/// recursive call can be checked and assumed at the call site.
///
/// A self-call is not inlined: inlining it is what made a recursive function
/// fail at the depth bound. Instead the call becomes the induction step of a
/// well-founded recursion -- the precondition is *proved* of the call's
/// arguments, the `decreases:` measure is *proved* to shrink, and the
/// postcondition is then *assumed* for the result. The measure is what makes the
/// assumption an induction hypothesis rather than a restatement of the goal, so
/// it is required: without one the call falls back to the old inlining.
///
/// The text is carried rather than a pre-built predicate because only the
/// executor knows what the arguments hold at the call site, and the same text has
/// to be evaluated there rather than at entry.
#[derive(Clone, Debug)]
pub struct Recursion {
    /// Raw `requires:` texts.
    pub requires: Vec<String>,
    /// Raw `ensures:` texts. At least one is needed: with no postcondition there
    /// is nothing to assume, so the call falls back to inlining.
    pub ensures: Vec<String>,
    /// The `decreases:` measure.
    pub decreases: String,
    /// The argument names whose types are signed, for the measure's relation.
    pub signed: BTreeSet<String>,
    /// The program's `const` table, so a measure or contract naming a constant
    /// resolves the way the body's use site does.
    pub consts: BTreeMap<String, Const>,
    /// Whether the return type is signed, for a postcondition comparison.
    pub ret_signed: bool,
}

/// The recursion context threaded through the walk: the contract text plus the
/// measure's value at *entry*, which the decrease test compares against.
struct RecCtx {
    rec: Recursion,
    /// The measure evaluated in the entry state, with its signedness.
    measure_entry: Option<(Var, bool)>,
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
    seeds: &Seeds,
    rec: Option<Recursion>,
) -> MirReport
where
    F: Fn(Option<Var>, &[(u32, Var)]) -> Result<Pred, String>,
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

    let mut env = Env::with_enums(&prog.enums, &prog.consts);
    // A pinned variable takes the literal its precondition fixes it to, so the
    // body's operations fold instead of building a circuit over an input that has
    // only one value. The pin is keyed by *variable index*, so it applies wherever
    // that variable is seeded -- an argument (whose index is its local) and an
    // aggregate part (a field, a nested path, an element) alike. See
    // [`crate::smt::pinned_vars`].
    let pin_of = |v: Var| -> Option<u64> {
        let idx = smt::index(v);
        seeds.pins.iter().find(|(i, _)| *i == idx).map(|(_, k)| *k)
    };
    // The literal for a pinned variable, masked to the variable's own width: the
    // value a precondition writes is signed (`-7`), and the pattern the seed needs
    // is two's complement at that width (`249` at eight bits).
    let lit_of = |v: Var, k: u64| -> Var {
        let w = smt::bits(v);
        let mask = if w >= 64 { u64::MAX } else { (1u64 << w) - 1 };
        smt::word(k & mask, w)
    };
    for &l in &f.arg_locals {
        let ty = f.ty_of(l).cloned().unwrap_or(Ty::Other("?".into()));
        let v = match ty.width() {
            Some(w) => {
                let sym = smt::var_named(l, w);
                match pin_of(sym) {
                    Some(k) if w == 1 => Val::Bool(smt::truth(k & 1 != 0)),
                    Some(k) => Val::Sym(lit_of(sym, k), Sign::of(&ty)),
                    None if w == 1 => Val::Bool(sym.eq_val(1)),
                    // The argument's own type declares its sign, so the value
                    // carries it rather than a later site having to look it up.
                    None => Val::Sym(sym, Sign::of(&ty)),
                }
            }
            None => Val::Unknown,
        };
        env.locals.insert(l, v);
        // A `&T` argument may be dereferenced: `Ty::Ref` is modelled as its
        // referent, so `*_1` names the same value `_1` does.
        if matches!(ty, Ty::Ref(_)) {
            env.deref_ok.insert(l, ());
        }
    }
    // Struct fields the contract names. The contract's `c.lo` is bound to this
    // variable, and the body's `((*_1).0)` reads it from here, so the two are the
    // same symbolic input rather than two that merely look alike.
    for &(local, field, v, signed) in &seeds.fields {
        let val = match pin_of(v) {
            Some(k) => Val::Sym(lit_of(v, k), Sign::of_bool(signed)),
            None => Val::Sym(v, Sign::of_bool(signed)),
        };
        env.fields.insert((local, field), val);
    }
    // Nested field paths the contract names, keyed by the whole projection chain
    // so the body's `(((*_1).0).0)` reads the same variable the contract's `o.i.v`
    // was rewritten to.
    for &(local, ref chain, v, signed) in &seeds.nested {
        let val = match pin_of(v) {
            Some(k) => Val::Sym(lit_of(v, k), Sign::of_bool(signed)),
            None => Val::Sym(v, Sign::of_bool(signed)),
        };
        env.nested.insert((local, chain.clone()), val);
    }
    // Slice lengths and elements the contract names. The contract's `xs.len()` and
    // `xs[0]` and the body's `PtrMetadata(_1)` and `(*_1)[0]` must be one value,
    // so the *same* variables are seeded here. An element the contract does not
    // name is not seeded; the first body read creates it (see `slice_elem`), and
    // a contract that names it later would then disagree — which is why
    // `bind_slice_refs` runs over every contract text before the run, so a name a
    // contract uses always has a binding here.
    for &(local, len, elem_w, elem_signed) in &seeds.lens {
        let fixed_len = seeds.array_lens.iter().find(|(l, _)| *l == local).map(|(_, n)| *n);
        // A slice's chain length comes from the *contract*, which established
        // `len <= MAX_INDEX_CHAIN` before the run; an array's is its type length.
        // The two are separate lists because they mean different things: the first
        // is proved, the second is a fact about the type.
        let slice_steps = seeds.slice_steps.iter().find(|(l, _)| *l == local).map(|(_, n)| *n);
        env.indexed.insert(
            local,
            Indexed {
                len,
                elem_w,
                elem_signed,
                elems: BTreeMap::new(),
                fixed_len,
                slice_steps,
                poisoned: false,
            },
        );
    }
    for &(local, index, v, _) in &seeds.elems {
        if let Some(s) = env.indexed.get_mut(&local) {
            let v = match pin_of(v) {
                Some(k) => lit_of(v, k),
                None => v,
            };
            s.elems.insert(index, v);
        }
    }
    // Elements of field-path arrays the contract names, keyed by the whole path. The body's
    // `(_1.0)[k]` write lands on the same key, so a contract's `o.a[0]` and the body's write are
    // one value. Pins apply here as elsewhere: a pinned element is a *literal*, not an input.
    for &(local, ref chain, index, v, _signed) in &seeds.path_elems {
        let val = match pin_of(v) {
            Some(k) => Val::Sym(lit_of(v, k), Sign::of_bool(_signed)),
            None => Val::Sym(v, Sign::of_bool(_signed)),
        };
        env.elems_path.insert((local, chain.clone(), index), val);
    }
    // Enum tags a contract names a variant of. The tag is seeded so the body's
    // `discriminant(_1)` reads the same variable the contract's `m` does, and the
    // payloads are seeded so a downcast read names the same one too.
    for &(local, tag, width, _) in &seeds.tags {
        env.set_discriminant(local, Val::Sym(smt::truncate(tag, width), Sign::Unsigned));
    }
    for &(local, variant, v, width, signed) in &seeds.payload_seeds {
        env.set_payload(local, variant, Val::Sym(v, Sign::of_bool(signed)), width);
    }
    // The tag's domain is the set of variant discriminants. Assuming it is sound
    // because it is a fact about the *type*: a value of the enum always has one of
    // its variants' tags, so no caller could falsify it. It is also necessary:
    // without it the `otherwise` arm of an exhaustive `match` looks reachable, and
    // since rustc lowers that arm to `unreachable`, every `match` would report a
    // panic.
    //
    // A disjunction of the discriminants, not a `tag < count` bound. The two agree
    // only when the numbering is `0..count`; with `A, B = 3, C` the real tags are
    // `0`, `3` and `4`, and `tag < 3` would exclude `4` -- excluding a value the
    // type admits, which is the unsound direction. The disjunction is exact for any
    // numbering.
    let mut pre = pre;
    for &(_, tag, width, ref discs) in &seeds.tags {
        if discs.is_empty() {
            continue;
        }
        // A discriminant too large for the tag's width cannot be represented, so
        // the domain cannot be assumed as written; refusing to assume is the safe
        // direction (the `otherwise` arm then looks reachable and the run reports
        // it, rather than a wrong domain being taken as fact).
        let max = *discs.iter().max().unwrap_or(&0);
        if width < 64 && max > (1u64 << width) - 1 {
            continue;
        }
        let mut bound: Option<Pred> = None;
        for d in discs {
            let p = smt::eq_const(tag, *d);
            bound = Some(match bound {
                None => p,
                Some(prev) => smt::or(prev, p),
            });
        }
        if let Some(bound) = bound {
            pre = Some(match pre {
                None => bound,
                Some(p) => smt::and(p, bound),
            });
        }
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

    // The recursion context: the measure evaluated in the *entry* state, which
    // every recursive call's decrease test compares against. Evaluated here,
    // once, because the entry state is the one the walk starts from and the walk
    // itself only ever sees later states. `names` is the entry binding of the
    // arguments, which is exactly the state the measure is about.
    let rec_ctx = rec.map(|rec| {
        let entry_names = spec::arg_vars(f);
        let measure_entry = spec::eval_measure(&rec.decreases, &entry_names, &rec.signed, &rec.consts)
            .ok();
        RecCtx { rec, measure_entry }
    });
    // A `decreases:` clause that cannot be read at entry is a refusal, not a
    // silently-absent measure: without it every recursive call would be reported
    // unknown, and saying so once here is clearer than at each call.
    if let Some(rc) = &rec_ctx {
        if rc.measure_entry.is_none() {
            report
                .unknown_paths
                .push("unreadable `decreases:` measure at entry".into());
        }
    }

    let mut work = vec![State {
        frame: Frame {
            func: root,
            ret_target: usize::MAX,
            ret_dest: None,
            saved_env: None,
            saved_cut: None,
            by_ref: Vec::new(),
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
        run_state(prog, st, &post, &mut report, &mut work, &seeds.pins, root, &rec_ctx);
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
        // A call writes its destination too, and that write is not a statement:
        // rustc spells `x = f(..)` as a `Call` terminator whose `dest` is `x`. Reading
        // only `Stmt::Assign` missed it, so a counter advanced by a call
        // (`i = i.wrapping_add(1)`) stayed out of the havoc set and kept the value it
        // had when the header was first entered. The induction step then proved the
        // invariant for that one value rather than for the loop, and a postcondition
        // that only holds on the first iteration came back `Verified`.
        if let Term::Call { dest, .. } = &block.term {
            writes.insert(dest.local, ());
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
        if let Some(Val::Sym(v, _)) = env.locals.get(&local) {
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
    crate::mir::spec::eval_invariant(text, &names, &signed_names(f), &env.consts)
        .map_err(|e| e.to_string())
}

/// The `(variable, literal)` bindings for the pins, masked to each variable's width.
///
/// A pin records a *bit pattern*, not a signed number: `-7` at eight bits is `249`. The
/// width comes from the variable's own declaration ([`smt::var_width`]), so the literal is
/// the same term the seeding uses. A pin whose variable is not declared in this context is
/// skipped: there is no width to mask to, and a wrong width would substitute a term of the
/// wrong size.
fn pin_bindings(pins: &[(u32, u64)]) -> Vec<(Var, Var)> {
    pins.iter()
        .filter_map(|&(idx, k)| {
            let w = smt::var_width(idx);
            if w == 0 {
                return None;
            }
            let mask = if w >= 64 { u64::MAX } else { (1u64 << w) - 1 };
            Some((smt::var_named(idx, w), smt::word(k & mask, w)))
        })
        .collect()
}

/// Apply the precondition's pins to a path and the goal built over it, at one obligation.
///
/// A pin is a *forced* value: the precondition entails `v == k`, so rewriting `v` to `k`
/// throughout `(P => Q)` gives `(P[v:=k] => Q[v:=k])`, which has the same truth value --
/// a model of `!P` restricts, and a model of `!P[v:=k]` extends by `v := k`. The rewrite is
/// therefore an equivalence: it can turn a refusal into a proof or a refutation, and it can
/// never manufacture a verdict.
///
/// It is applied to the *whole path* and not to the precondition alone, and that is the
/// load-bearing part. The executor's path is not just the precondition: a `match` on an enum
/// tag, an `assert`, a branch each conjoin their own constraint. Rewriting only the
/// precondition would drop the relation between the tag and the value the pin gives it --
/// `m == Mode::Run` pins the tag to `2`, and a path that then splits on `tag == 0` is
/// infeasible *because* the pin says `2`. Rewriting the path keeps every split and every
/// pin, and takes the deep term (`c == b * 2`) out of the assumption the diagram is built
/// over. See [`crate::smt::pinned_vars`].
fn pinned_pair(path: Pred, goal: Pred, pins: &[(u32, u64)]) -> (Pred, Pred) {
    if pins.is_empty() {
        return (path, goal);
    }
    let bindings = pin_bindings(pins);
    if bindings.is_empty() {
        return (path, goal);
    }
    (smt::substitute(path, &bindings), smt::substitute(goal, &bindings))
}

/// Decide `path => goal`, retrying with the pins rewritten in only if the engine refuses.
///
/// The unrewritten query is tried first and its answer is kept whenever it is decided. That
/// ordering is what preserves the *witness*: the rewrite removes the pinned variables, so a
/// counterexample found under it cannot name the input, and the counterexample is the more
/// useful answer. The fallback exists for the one case the rewrite is for -- an `Unknown`
/// the pins can lift -- and [`pinned_pair`] is an equivalence, so a decided answer from the
/// retry is the same answer the first attempt would have given had it been able to decide.
fn prove_obligation(path: Pred, goal: Pred, pins: &[(u32, u64)]) -> Verdict {
    let v = smt::prove_implies(path, goal);
    if !matches!(v, Verdict::Unknown) || pins.is_empty() {
        return v;
    }
    let (path, goal) = pinned_pair(path, goal, pins);
    let v2 = smt::prove_implies(path, goal);
    if matches!(v2, Verdict::Unknown) {
        v
    } else {
        v2
    }
}

/// [`smt::find_model`] with the same pins fallback as [`prove_obligation`].
fn find_obligation(path: Pred, pins: &[(u32, u64)]) -> Verdict {
    let v = smt::find_model(path);
    if !matches!(v, Verdict::Unknown) || pins.is_empty() {
        return v;
    }
    let (path, _) = pinned_pair(path, smt::truth(true), pins);
    let v2 = smt::find_model(path);
    if matches!(v2, Verdict::Unknown) {
        v
    } else {
        v2
    }
}

/// The base type name of a path segment, with generic arguments and an
/// `impl`-projection wrapper stripped: `Vec2` → `Vec2`, `G::<T>` → `G`,
/// `<S2 as T2>` → `S2`, `core::num::<impl u8>` → `u8`.
///
/// rustc prints a method's *definition* with the type it is implemented for
/// wrapped in `<impl …>` and a *call* with that type bare, so the two have to be
/// cut to the same shape before they can be compared.
fn base_type(s: &str) -> String {
    let s = s.trim();
    if let Some(rest) = s.split("<impl ").nth(1) {
        return rest.chars().take_while(|c| c.is_ascii_alphanumeric() || *c == '_').collect();
    }
    let s = match s.strip_prefix('<') {
        Some(rest) => rest.split(" as ").next().unwrap_or(rest),
        None => s,
    };
    let s = s.split("::<").next().unwrap_or(s);
    let s = s.split('<').next().unwrap_or(s);
    s.rsplit("::").next().unwrap_or(s).trim().to_string()
}

/// The type a method call is made on: `Vec2` in `Vec2::push`, `G` in
/// `G::<T>::walk`, `S2` in `<S2 as T2>::go`.
fn call_type(name: &str) -> Option<String> {
    Some(base_type(name.rsplit_once("::")?.0))
}

/// The `self` type of an *instance* method, read from its receiver's declared
/// type.
///
/// rustc prints a method's *definition* as `<impl at FILE:L:C: L:C>::m`, which
/// names no type, but an instance method's receiver is the first argument and its
/// `debug` binding is literally `self`, so that local's declared type names the
/// type the method is implemented for (`&Vec2` gives `Vec2`).
///
/// A *static* associated function has no `self`, so it has no `debug self`
/// binding and this returns `None`. The distinction matters: a static
/// `Foo::m(x: Vec2)`'s first parameter is an ordinary argument, and reading it as
/// a receiver would let a call to an *external* `Vec2::m` resolve to `Foo::m` --
/// answering a call from the wrong body, which is a false proof. A free function
/// has no `self` either and is also `None`, so callers distinguish the two by the
/// definition name (see [`is_impl_method`]).
fn method_self_type(f: &MirFn) -> Option<String> {
    let self_local = f
        .debug_bindings
        .iter()
        .find_map(|(n, l)| (n == "self").then_some(*l).flatten())?;
    let ty = f.locals.get(&self_local)?;
    let inner = match ty {
        Ty::Ref(inner) => inner.as_ref(),
        other => other,
    };
    match inner {
        Ty::Other(s) => Some(base_type(s)),
        _ => None,
    }
}

/// Whether the definition name is rustc's printed form for a method in an `impl`
/// block (`<impl at FILE:L:C: L:C>::m`), as opposed to a free function's bare name.
fn is_impl_method(f: &MirFn) -> bool {
    f.name.contains("<impl at")
}

/// Resolve a call name to the function in the dump it names.
///
/// An exact match is the free-function case: rustc prints a same-crate free
/// function's call and its definition by the same bare name. Otherwise the name
/// is a qualified call (`Type::m`) whose *definition* rustc prints as
/// `<impl at …>::m`, so only the tail is shared.
///
/// The tail alone is not enough. `Vec2::push` and `Vec::<u8>::push`, or a free
/// `wrapping_add` and `core::num::<impl u8>::wrapping_add`, share a tail while
/// naming different functions, and answering such a call from the wrong body is a
/// false proof. Two guards keep that from happening:
///
/// * A call name that still carries an `impl` projection (`…::<impl u8>::…`) is a
///   `core`/`std` callee. rustc prints a *local* method call with its concrete
///   type (`Vec2::push`, `<S as T>::m`), never with `<impl`, so such a name is
///   never a same-dump call and is refused outright.
/// * A surviving candidate must be the method for the same type: an instance
///   method's `self` type must equal the call's type, and a static associated
///   function (whose `self` type cannot be read) is accepted on the unique tail
///   only. A free function never matches a qualified call, because rustc prints a
///   same-crate free function's call bare -- the exact-match case above.
///
/// `None` means the call is not modelled, which the caller reports rather than
/// guesses at.
fn resolve_callee(prog: &MirProgram, name: &str) -> Option<usize> {
    if let Some(i) = prog.fns.iter().position(|g| g.name == name) {
        return Some(i);
    }
    if name.contains("<impl") {
        return None;
    }
    let tail = name.rsplit("::").next()?;
    let want_ty = call_type(name)?;
    let mut hits = prog.fns.iter().enumerate().filter(|(_, g)| {
        if g.name.rsplit("::").next() != Some(tail) {
            return false;
        }
        match method_self_type(g) {
            Some(self_ty) => self_ty == want_ty,
            None => is_impl_method(g),
        }
    });
    match (hits.next(), hits.next()) {
        (Some((i, _)), None) => Some(i),
        _ => None,
    }
}

/// Answer a self-recursive call by its contract instead of inlining it.
///
/// Returns `Some(())` when the call was handled (the caller must then continue at
/// its own `target`, or stop when the obligation failed), `None` when it was not a
/// recursive call or recursion is not licensed, so the caller falls through to the
/// inliner.
///
/// # Why this is sound
///
/// A self-call inlined once is the *first* unrolling, and `DEFAULT_INLINE_DEPTH`
/// stops the second. The contract route replaces the unrolling with an induction:
///
/// * the callee's precondition is *proved* of the call's arguments (`Pre`), so the
///   assumption only applies to calls the function itself admits;
/// * the `decreases:` measure is *proved* to be non-negative at entry and strictly
///   smaller at the call (`Dec`), which is the well-founded basis; and
/// * the postcondition is *assumed* of the result.
///
/// The measure is what makes this an induction rather than a circular argument: a
/// strictly decreasing sequence in a well-founded order is finite, so there is a
/// base case, and at the base case the body must establish the postcondition on
/// its own. Nothing here *assumes* the postcondition at the base case -- the
/// `return` obligations still have to be discharged by the body -- so a body that
/// does not establish it is still a failure.
///
/// Every check is an obligation, so a wrong measure or a precondition the
/// arguments do not meet is a *finding*, not a silent fallback.
#[allow(clippy::too_many_arguments)]
fn try_recursive_call(
    prog: &MirProgram,
    st: &mut State,
    root: usize,
    name: &str,
    args: &[Operand],
    dest: &Place,
    target: usize,
    rec: &Option<RecCtx>,
    report: &mut MirReport,
    work: &mut Vec<State>,
    pins: &[(u32, u64)],
) -> Option<()> {
    // Only a self-call, and only the function under verification: an inlined
    // callee's frame has a different `func`, and its own recursion is not this
    // function's induction.
    //
    // The name is resolved with the same rule the inliner uses (exact match, else
    // a unique tail match that also agrees on the method's `self` type), and the
    // result has to be the root itself. A name that resolves to nothing, or
    // ambiguously, is not this function calling itself.
    //
    // This must run *before* the intrinsic dispatch below, but it must not
    // swallow an intrinsic call. A function named `wrapping_add` that calls
    // `u8::wrapping_add` is calling the *intrinsic*, not itself; treating the
    // call as recursive would assume the function's own postcondition in place of
    // evaluating the intrinsic, which is a false proof. `resolve_callee` refuses
    // that name because the intrinsic's `self` type (`u8`) is not the local
    // function's, so the check falls through to the intrinsic model.
    if st.frame.func != root || resolve_callee(prog, name) != Some(root) {
        return None;
    }
    // The root frame has no caller, so a self-call is recursion by construction.
    // A frame with a caller is an inlined callee, and reaching the root's name
    // from there is not the root calling itself.
    if st.frame.caller.is_some() {
        return None;
    }
    let Some(rc) = rec else { return None };
    // No postcondition means nothing to assume, so the call has no contract route
    // and falls back to inlining (which will report the depth cutoff).
    if rc.rec.ensures.is_empty() {
        return None;
    }
    let f = &prog.fns[root];
    // The contract is evaluated over the call's arguments, so the field bindings
    // are the call site's and are rebuilt below. The `const` table is not: a
    // constant has the same value at the call as at entry, and the entry state
    // already carries it in `rc.rec.consts`. Handing the reader an empty table
    // here made a contract that names a constant -- `requires: n <= LIMIT` --
    // unreadable at the self-call, which turned a decidable proof into a refusal.
    let fields = FieldEnv::with_consts(rc.rec.consts.clone());

    // The argument bindings at the call site: name -> the value the caller holds.
    // A name that has no value there (an unmodelled operand) makes the whole call
    // unmodelled, which is the same refusal the inliner would give.
    let mut names: BTreeMap<String, Var> = BTreeMap::new();
    for (i, a) in args.iter().enumerate() {
        let Some(&l) = f.arg_locals.get(i) else { continue };
        match operand(&mut st.env, a) {
            Val::Sym(v, _) => {
                names.insert(f.name_of(l), v);
            }
            Val::Bool(p) => {
                names.insert(f.name_of(l), smt::ite(p, smt::word(1, 1), smt::word(0, 1)));
            }
            _ => {
                report
                    .unknown_paths
                    .push(format!("unmodelled argument to a recursive call to `{name}`"));
                return Some(());
            }
        }
    }

    // `Pre`: the callee's precondition, proved of the call's arguments. This is a
    // proof obligation, so an unreadable precondition is a refusal rather than a
    // silently skipped check -- assuming a postcondition without the matching
    // precondition would be assuming the conclusion.
    let mut pre_ok = true;
    let mut pre: Option<Pred> = None;
    for r in &rc.rec.requires {
        match spec::eval_requires(r, &names, &rc.rec.signed, &fields) {
            Ok(p) => pre = Some(match pre {
                None => p,
                Some(prev) => smt::and(prev, p),
            }),
            Err(e) => {
                report
                    .unknown_paths
                    .push(format!("unreadable `requires` at a recursive call: {e}"));
                pre_ok = false;
                break;
            }
        }
    }
    if !pre_ok {
        return Some(());
    }
    if let Some(p) = pre {
        report.obligations.push(Obligation {
            kind: ObligationKind::RecursivePrecondition,
            verdict: prove_obligation(st.path, p, pins),
        });
    }

    // `Dec`: the measure at the call is non-negative and strictly below its value
    // at entry. Both halves are needed. Non-negativity is what makes the order
    // well-founded (a signed measure that goes negative would otherwise
    // "decrease" forever); strictness is the progress.
    if let Some((m_entry, signed)) = rc.measure_entry {
        match spec::eval_measure(&rc.rec.decreases, &names, &rc.rec.signed, &rc.rec.consts) {
            Ok((m_call, call_signed)) => {
                if call_signed != signed || smt::bits(m_call) != smt::bits(m_entry) {
                    report.unknown_paths.push(
                        "the measure at a recursive call has a different type than at entry"
                            .into(),
                    );
                    return Some(());
                }
                let zero = smt::word(0, smt::bits(m_entry));
                let nonneg = if signed { smt::sge(m_entry, zero) } else { smt::truth(true) };
                let decreases = if signed {
                    smt::slt(m_call, m_entry)
                } else {
                    smt::ult(m_call, m_entry)
                };
                report.obligations.push(Obligation {
                    kind: ObligationKind::RecursiveDecreases,
                    verdict: prove_obligation(st.path, smt::and(nonneg, decreases), pins),
                });
            }
            Err(e) => {
                report.unknown_paths.push(format!("unreadable `decreases`: {e}"));
                return Some(());
            }
        }
    } else {
        report.unknown_paths.push(
            "a recursive call has no `decreases:` measure at entry to compare against".into(),
        );
        return Some(());
    }

    // Assume the postcondition for the result: a fresh variable for `ret`, the
    // conjuncts of every `ensures`, then write it to the call's destination. The
    // postcondition is *assumed*, never proved, here -- proving it is the `return`
    // obligations' job.
    let Some(w) = f.ret_ty.width() else {
        report
            .unknown_paths
            .push("a recursive call returns an aggregate, which is not modelled".into());
        return Some(());
    };
    let ret_v = smt::var(w);
    let ret_signed = rc.rec.ret_signed;
    let mut post_assumed: Option<Pred> = None;
    for e in &rc.rec.ensures {
        match spec::eval_ensures(
            e,
            &names,
            Some(ret_v),
            spec::RET_IS_UNKNOWN,
            &rc.rec.signed,
            ret_signed,
            &fields,
        ) {
            Ok(p) => post_assumed = Some(match post_assumed {
                None => p,
                Some(prev) => smt::and(prev, p),
            }),
            Err(e) => {
                report
                    .unknown_paths
                    .push(format!("unreadable `ensures` at a recursive call: {e}"));
                return Some(());
            }
        }
    }
    let assumed = post_assumed.unwrap_or_else(|| smt::truth(true));
    st.path = smt::and(st.path, assumed);
    let ret_val = if w == 1 {
        Val::Bool(ret_v.eq_val(1))
    } else {
        Val::Sym(ret_v, Sign::of_bool(ret_signed))
    };
    st.env.set(dest, ret_val);
    advance(prog, st.clone(), target, report, work, pins);
    Some(())
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
    pins: &[(u32, u64)],
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
        verdict: prove_obligation(st.path, inv, pins),
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
                    // A havoced local is a fresh *input* of the same type, so it
                    // keeps the type's sign.
                    Val::Sym(smt::var(w), Sign::of(ty))
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

/// Answer a modelled `core::num` call, if the callee is one.
///
/// `None` means the callee is not a modelled intrinsic, and the caller falls
/// through to the same-dump inliner. `Some(Err(..))` means it *is* one but this
/// call is outside what the model covers -- an unknown operand, a width past
/// [`intrinsics::DIV_MAX_WIDTH`] -- and the path is reported unknown. The
/// distinction matters: refusing to model a call and refusing to inline it are
/// different answers, and only the first is a coverage gap in `intrinsics`.
fn try_intrinsic(
    prog: &MirProgram,
    func: usize,
    name: &str,
    args: &[Operand],
    dest: &Place,
    env: &mut Env,
) -> Option<Result<(), String>> {
    let op = intrinsics::classify(name)?;
    let cur = &prog.fns[func];
    // The operand width, from the first argument's declared type. It is not the
    // destination's: `checked_add` on a `u8` writes an `Option<u8>`, and taking
    // the width from there would ask the engine for a 64-bit overflow test.
    let first = args.first()?;
    let w = operand_width(cur, first)?;
    // The operand's signedness comes *from the value*. An operand whose type
    // could not be read was already refused when the value was built (it is
    // `Val::Unknown`, not a `Sym`), so there is no sign to guess here: guessing
    // would give `sdiv`/`srem` the unsigned meaning, which is a wrong value for
    // every negative operand rather than a weaker proof.
    let (x, sign) = match operand(env, first) {
        // The sign comes out of the value with the word, so the two cannot be
        // read from different places and disagree.
        Val::Sym(v, sign) => (v, sign),
        // A `bool` operand has no bit-vector to hand the model, and an unknown
        // one has no value at all. Either way there is nothing to compute with.
        _ => return Some(Err(format!("unmodelled argument to `{name}`"))),
    };
    // The unary shapes take one operand and no operator. They are handled here
    // rather than through a `BinOp`, because there is no second operand to read.
    if op.is_unary() {
        // A bit count does not read the sign at all -- the bits of a negative
        // value are just bits -- so a dump that did not print one is still
        // modelled. A unary *operator* does read it, because `neg` and `abs`
        // mean different things on the two types, so a missing sign is refused
        // there rather than guessed.
        let signed = match op {
            intrinsics::Intrinsic::Unary(..) => sign.known()?,
            _ => false,
        };
        // A bit count returns a type wider than its operand (`u8` -> `u32`), so
        // the result term is built at the destination's width. Taking it from the
        // operand instead would leave an 8-bit term in a 32-bit local, and the
        // next read of that local would be ill-formed.
        let result_w = width_of(cur, dest).unwrap_or(w);
        let Some(outcome) = intrinsics::eval(op, x, x, w, signed, result_w) else {
            return Some(Err(format!("`{name}` past what the model covers at {w} bits")));
        };
        return Some(match outcome {
            Outcome::Value(v) => {
                // The result has the operand's type, so it has the operand's
                // sign. For a bit count that reading is only a label -- the value
                // is unsigned and non-negative -- but it is the type's sign, and
                // labelling it anything else would be a second opinion about a
                // type this code already knows.
                env.set(dest, Val::Sym(v, Sign::of_bool(signed)));
                Ok(())
            }
            Outcome::Option { tag, payload } => {
                // `checked_neg` and `checked_abs` return an `Option`.
                env.set_discriminant(dest.local, Val::Sym(tag, Sign::Unsigned));
                env.set_payload(
                    dest.local,
                    intrinsics::SOME_TAG,
                    Val::Sym(payload, Sign::of_bool(signed)),
                    w,
                );
                Ok(())
            }
            Outcome::Tuple { value, overflowed } => {
                // `overflowing_neg` and `overflowing_abs` return `(T, bool)`,
                // which is a plain aggregate: field 0 the value, field 1 the
                // flag. `Val::Agg` is returned so `set` does not clear the parts
                // that were just written.
                let field = |i| Place { local: dest.local, proj: vec![Proj::Field(i)] };
                env.set(&field(0), Val::Sym(value, Sign::of_bool(signed)));
                env.set(&field(1), Val::Bool(overflowed));
                Ok(())
            }
        });
    }
    // A sign the dump did not print is a refusal, not an unsigned reading:
    // `sdiv` on an `i8` read as unsigned returns a huge positive quotient for
    // every negative operand, which is a wrong value rather than a weaker proof.
    let signed = sign.known()?;
    // `pow` reads two operands of *different* types: the base has the method's
    // width and sign, the exponent is the `u32` it is declared as. So the exponent
    // is read on its own -- a `Val::Sym` and its width from the argument's type --
    // and the fold is handed the two separately. Reading it as a second operand at
    // `w` bits would read an `i8` exponent for a `u8` base, or a `u8` exponent for
    // a `u32` one, and fold the wrong number of bits.
    if let intrinsics::Intrinsic::Pow(_) = op {
        let Some(exp_arg) = args.get(1) else {
            return Some(Err(format!("unmodelled arity for `{name}`")));
        };
        let Some(exp_w) = operand_width(cur, exp_arg) else {
            return Some(Err(format!("unmodelled exponent type for `{name}`")));
        };
        // The exponent is unsigned by construction (`u32`); a signed reading of
        // its bits would make `exp == 0x8000_0000` a negative number.
        let exp = match operand(env, exp_arg) {
            Val::Sym(v, _) => v,
            _ => return Some(Err(format!("unmodelled argument to `{name}`"))),
        };
        if !intrinsics::pow_exponent_fits(exp_w) {
            return Some(Err(format!("`{name}` exponent past the model's 32 bits")));
        }
        let Some(outcome) = intrinsics::eval(op, x, exp, w, signed, w) else {
            return Some(Err(format!("`{name}` past what the model covers at {w} bits")));
        };
        let sign = Sign::of_bool(signed);
        return Some(match outcome {
            Outcome::Value(v) => {
                env.set(dest, Val::Sym(v, sign));
                Ok(())
            }
            Outcome::Option { tag, payload } => {
                env.set_discriminant(dest.local, Val::Sym(tag, Sign::Unsigned));
                env.set_payload(dest.local, intrinsics::SOME_TAG, Val::Sym(payload, sign), w);
                Ok(())
            }
            Outcome::Tuple { value, overflowed } => {
                let field = |i| Place { local: dest.local, proj: vec![Proj::Field(i)] };
                env.set(&field(0), Val::Sym(value, sign));
                env.set(&field(1), Val::Bool(overflowed));
                Ok(())
            }
        });
    }
    let y = match args.get(1) {
        Some(a) => match operand(env, a) {
            Val::Sym(v, _) => v,
            _ => return Some(Err(format!("unmodelled argument to `{name}`"))),
        },
        // Every two-operand name has both operands printed, so a missing second
        // argument means the dump had a shape the model does not cover.
        None => return Some(Err(format!("unmodelled arity for `{name}`"))),
    };
    let Some(outcome) = intrinsics::eval(op, x, y, w, signed, w) else {
        return Some(Err(format!("`{name}` past what the model covers at {w} bits")));
    };
    // The result of an arithmetic intrinsic has the operand's type, so it has
    // the operand's sign -- `wrapping_sub(0, 1)` on a `u8` is `255` and on an
    // `i8` is `-1`, the same bits read two ways.
    let sign = Sign::of_bool(signed);
    match outcome {
        Outcome::Value(v) => env.set(dest, Val::Sym(v, sign)),
        Outcome::Option { tag, payload } => {
            // The payload is recorded under the `Some` projection with the
            // operand width, and the tag alongside it. rustc reads the payload
            // only inside the arm where the tag is `1`, so recording it now is
            // sound; the width is what keeps the read from being mis-sized.
            env.set_discriminant(dest.local, Val::Sym(tag, Sign::Unsigned));
            env.set_payload(dest.local, intrinsics::SOME_TAG, Val::Sym(payload, sign), w);
        }
        Outcome::Tuple { value, overflowed } => {
            // `overflowing_*` returns `(result, overflowed)`, which is a plain
            // aggregate rather than an `Option`. Field 0 gets the wrapped value
            // and field 1 the flag, so a caller that writes `let (r, o) = …` or
            // asserts `!o` reads a real condition.
            let field = |i| Place { local: dest.local, proj: vec![Proj::Field(i)] };
            env.set(&field(0), Val::Sym(value, sign));
            env.set(&field(1), Val::Bool(overflowed));
        }
    }
    Some(Ok(()))
}

/// The declared bit width of an operand, when it has one.
fn operand_width(f: &MirFn, o: &Operand) -> Option<u8> {
    match o {
        Operand::Copy(p) | Operand::Move(p) => width_of(f, p),
        Operand::Const(Const::UInt(_, ty)) => ty.as_ref().and_then(|t| t.width()),
        Operand::Const(_) => None,
    }
}

#[allow(clippy::too_many_arguments)]
fn run_state<F>(
    prog: &MirProgram,
    mut st: State,
    post: &Option<F>,
    report: &mut MirReport,
    work: &mut Vec<State>,
    pins: &[(u32, u64)],
    root: usize,
    rec: &Option<RecCtx>,
)
where
    F: Fn(Option<Var>, &[(u32, Var)]) -> Result<Pred, String>,
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
                // A reference *copied* between locals (`let r = identity(&mut x)`
                // lowers to `_4 = move _3` where `_3` is the returned `&mut u8`)
                // addresses the same place `_3` did, and `resolve` is what turns
                // `*_4` into that place. Only `Rvalue::Ref` and a reference `Cast`
                // recorded the mapping, so the copy lost it: `*_4 = 5` was then a
                // write to a local no caller reads, the write was dropped, and
                // `requires: x == 0` / `ensures: ret == 0` was **proved** against a
                // body that returns 5 -- while the true contract `ret == 5` was
                // refuted. The mapping is carried only for a reference *type*, so a
                // numeric copy cannot invent one.
                // The *source* is the guard, not the destination: a copy of a
                // reference local is a reference copy, and `q.proj.is_empty()`
                // keeps a copy *through* a reference (`_3 = copy (*_1)`, where `_3`
                // is a `u8`) out -- carrying the address there would give a scalar
                // an address, and in a two-reference `swap` both scalar copies then
                // claimed the same storage, which broke the swap and proved a false
                // contract.
                if let Rvalue::Use(Operand::Copy(q) | Operand::Move(q)) = rv {
                    if q.proj.is_empty() && matches!(cur.ty_of(q.local), Some(Ty::Ref(_))) {
                        if let Some(o) = st.env.ref_origin.get(&q.local).cloned() {
                            st.env.addressed.insert(dest.local, o.clone());
                            st.env.ref_origin.insert(dest.local, o);
                        }
                    } else if q.proj.as_slice() == [Proj::Deref]
                        && matches!(cur.ty_of(dest.local), Some(Ty::Ref(_)))
                    {
                        // A reference read *through* another reference: `**rr = 5`
                        // lowers to `_4 = no_retag copy (*_3); (*_4) = 5`, where `_4`
                        // is a `&mut u8`. The copy is a *reference*, so it addresses
                        // what `_3` points to. Neither branch above fires -- the
                        // source is not a bare reference local, and its projection is
                        // a deref -- so `_4` got no address, `(*_4) = 5` was dropped,
                        // and `requires: x == 0` / `ensures: ret == 0` was **proved**
                        // against a body that returns 5, while the true `ret == 5` was
                        // refuted. The destination's *type* is what separates this from
                        // `_3 = copy (*_1)` with `_3: u8`, which copies a scalar and
                        // must carry no address (both are a deref; only the type
                        // differs).
                        //
                        // The place is `_3`'s referent, not `_3`: aiming at `_3` would
                        // make `(*_4) = 5` write to the reference local rather than to
                        // what it points at.
                        let p = st.env.pointee(q);
                        st.env.addressed.insert(dest.local, p.clone());
                        st.env.ref_origin.insert(dest.local, p);
                    }
                }
                st.env.set(dest, v);
                // A *nested* aggregate assignment moves the source's parts under the
                // destination's path. Two shapes need it: a struct literal into a nested field
                // (`o.i = Inner { v: 9 }` -> `(_1.0) = move _2`), and a nested-to-nested move
                // (`o.i = o.j` -> `_2 = move (_1.1); (_1.0) = move _2`, so a *nested source*
                // into a whole temp, then a whole source into a nested destination).
                //
                // `copy_parts` in `eval_rvalue` handles only whole-to-whole, and a nested
                // source is one it refuses, so this runs whenever *either* side is nested.
                // It is done *after* `set` because the field arm of `set` forgets the nested
                // paths beneath the destination -- correct, since they are stale -- and this
                // is what puts the source's parts back. Without it the temp's `v` never lands
                // under `_1.0`, and `(_1.0).0` reads `Unknown`.
                if let Rvalue::Use(Operand::Copy(q) | Operand::Move(q)) = rv {
                    if !q.proj.is_empty() || !dest.proj.is_empty() {
                        st.env.rebase_parts(q, dest);
                    }
                }
            }
        }
    }

    // Terminator. Every successor goes through `advance`, which is where a loop
    // edge into the invariant's header is checked instead of followed.
    match &block.term {
        Term::Goto(b) => advance(prog, st, *b, report, work, pins),
        Term::Return => {
            let ret = st.env.get(&Place::new(0));
            match st.frame.caller.take() {
                // The root returned: check the postcondition here.
                None => {
                    report.returned_paths += 1;
                    if let Some(post) = post {
                        // The components of a tuple return, so a postcondition can
                        // name `ret.0`. They are read through the *same* place read
                        // the body uses, rather than from one store directly.
                        //
                        // That is not a convenience: a tuple local's component is
                        // written under `Proj::Index` by a literal (`_0 = (a, b)`) and
                        // under `Proj::Field` by a modelled call (`overflowing_add`
                        // writes field 0 and field 1), while `Env::get` consults
                        // `fields` and falls back to `elems` so both spellings of
                        // "component `k`" meet. Collecting from `elems` alone missed
                        // every call-written component, and the symptom was a
                        // postcondition about `ret.1` reported unreadable -- an
                        // aggregate with no such component -- rather than checked.
                        // Going through `get` makes the two agree by construction.
                        //
                        // The candidate indices are the union of the two stores, and
                        // an unwritten component stays out of the list: binding a
                        // *fresh* variable for it would make a postcondition about
                        // `ret.1` pass vacuously, which is why the filter drops
                        // anything that is not a readable value.
                        //
                        // A `bool` component is widened to a one-bit word for the
                        // same reason a `bool` *return* is: a postcondition
                        // `ret.0 == true` compares against a word, and dropping the
                        // component would leave the name unbound, so the parser
                        // refuses the whole contract. `(bool, u8)` returns are
                        // common (every `checked_*` is `(T, bool)`), so refusing
                        // them silently loses the proof.
                        let mut components: BTreeSet<u32> = BTreeSet::new();
                        for (l, k) in st.env.elems.keys() {
                            if *l == 0 {
                                components.insert(*k as u32);
                            }
                        }
                        for (l, k) in st.env.fields.keys() {
                            if *l == 0 {
                                components.insert(*k);
                            }
                        }
                        let projs: Vec<(u32, Var)> = components
                            .into_iter()
                            .filter_map(|k| {
                                let p = Place { local: 0, proj: vec![Proj::Field(k)] };
                                match st.env.get(&p) {
                                    Val::Sym(x, _) => Some((k, x)),
                                    Val::Bool(p) => {
                                        Some((k, smt::ite(p, smt::word(1, 1), smt::word(0, 1))))
                                    }
                                    _ => None,
                                }
                            })
                            .collect();
                        // What the postcondition is evaluated against. A scalar
                        // return hands over its word; a bool is widened to a one-bit
                        // word (proving `path => rp` alone would check only that the
                        // bool is *true*, which is not the contract — `ensures: ret
                        // == false` would be ignored). An aggregate has no single
                        // word, so `ret` itself is passed as `None` and a contract
                        // that uses bare `ret` is refused by the parser; the
                        // components are still available as `ret.0`, `ret.1`.
                        let rv = match ret {
                            Val::Sym(rv, _) => Some(rv),
                            Val::Bool(rp) => Some(smt::ite(rp, smt::word(1, 1), smt::word(0, 1))),
                            _ => None,
                        };
                        match post(rv, &projs) {
                            Ok(p) => {
                                report.obligations.push(Obligation {
                                    kind: ObligationKind::Postcondition,
                                    verdict: prove_obligation(st.path, p, pins),
                                });
                            }
                            Err(e) => report
                                .unknown_paths
                                .push(format!("unreadable `ensures`: {e}")),
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
                    // The callee ran in its own `Env`, seeded from a copy of each
                    // indexed argument's store. What happens to that store now
                    // depends on how the argument was passed, and the two cases
                    // are opposites:
                    //
                    // * A by-value `[T; N]` is the callee's *own copy*. Its writes
                    //   die with the frame, so the caller's array is still the one
                    //   it passed and must not be overwritten from the callee.
                    //   Nothing is copied back.
                    // * A `&mut [T]`/`&mut [T; N]` is the caller's storage. The
                    //   frontend models `&T` as its referent (the single-owner
                    //   reading, not an aliasing model), so the callee's local and
                    //   the caller's local denote the same value: the callee's
                    //   post-state *is* the caller's post-state, and is copied
                    //   back. That is what makes a helper that writes through a
                    //   reference visible to the caller, and a callee that wrote
                    //   nothing leaves the caller's store as it was.
                    for (target, cal) in &caller.by_ref {
                        let cl = target.local;
                        // The target's projection *below* its leading deref. A
                        // reference argument arrives as `_5 = &mut _2; set5(_5)`,
                        // so `pointee` has already collapsed the temp and the target
                        // is a plain place on the caller's local -- `c` for `&mut c`,
                        // `c.0` for `&mut c.lo`. Stripping the deref (when a caller
                        // ever hands one over) leaves the chain every re-key below
                        // is prefixed with.
                        let rest: &[Proj] = match target.proj.first() {
                            Some(Proj::Deref) => &target.proj[1..],
                            _ => &target.proj,
                        };
                        // An indexed referent (`&mut [T]` / `&mut [T; N]`): the
                        // callee's element store *is* the caller's post-state.
                        //
                        // Only when the target is the *whole* local. For a
                        // sub-place target (`set5(&mut a[0])`) the callee's local
                        // is a scalar `&mut u8`, and the store the callee holds for
                        // it is the caller's array carried in for the read -- which
                        // the callee's whole-place write *poisoned*. Copying that
                        // poison back would make the caller's untouched `a[0]` read
                        // unknown, turning a decidable contract into an incomplete
                        // one.
                        if rest.is_empty() {
                            if let Some(s) = st.env.indexed.get(cal) {
                                env.indexed.insert(cl, s.clone());
                            }
                        }
                        // A whole-referent write (`*v = x`). The whole place was
                        // replaced, so the caller's derived parts are dropped
                        // before the callee's value is copied in -- otherwise a
                        // stale field the callee overwrote would survive. A
                        // sub-place target (`&mut _1.0`) is coarser: every part of
                        // `_1` is dropped, which loses precision but never keeps a
                        // stale value.
                        if st.env.whole_writes.contains(cal) {
                            if let Some(v) = st.env.locals.get(cal) {
                                // The callee's whole-place value lands *at the
                                // target*, which is the caller's local only when
                                // the target has no projection. For `&mut c.lo` the
                                // target is `c.0`, so the write belongs in the
                                // field store, not on `c` itself -- writing it to
                                // `c` would put a bit-vector where a struct lives.
                                // `set` keys the projection for us, and it drops
                                // the parts the write replaces.
                                env.set(&target.clone(), *v);
                                // A *whole-local* target additionally supersedes
                                // the whole local, which is what the parts drop
                                // above needs to see.
                                if target.proj.is_empty() {
                                    env.whole_writes.insert(cl);
                                }
                            } else {
                                env.forget_parts(cl);
                            }
                        }
                        // A write to a *part* of the referent (`(*v).0 = x`,
                        // `(*v).a.b = x`, `(*v)[0] = x`). Only the callee's
                        // entries exist for its argument local (a reference is
                        // seeded as `Unknown`, never as parts), so every entry
                        // here is a write and is safe to carry back. A part the
                        // callee did not touch keeps the caller's seed, which is
                        // the same storage the callee read.
                        //
                        // Every key is re-based on the *target's* projection, not
                        // copied onto the caller's local. For a whole-local target
                        // (`&mut c`) `rest` is empty and the keys are unchanged, so
                        // `c.lo` lands on `c`'s field as before. For a sub-place
                        // target (`&mut o.i`) the callee's `_1.v` is `o.i.v`, so the
                        // key has to become the chain `rest ++ [v]` -- copying it to
                        // `o`'s field `v` would put a leaf where no leaf lives, and
                        // *dropping* it (what a whole-local-only guard did) lost the
                        // write entirely: `set_inner(&mut o.i); o.i.v` read the
                        // caller's seed, so the true contract `ret == 5` was refuted
                        // and the false `ret == 0` was **proved**.
                        // `nested` is keyed by a chain of *field* indices, so the
                        // target's projection is usable as a prefix exactly when it
                        // is itself a field chain. A target that is not one (an
                        // element, `&mut o.a[0]`) is a scalar in the callee, so it
                        // has no parts to carry and the loops below see nothing --
                        // the `None` arm exists only so an unrepresentable key is
                        // never invented.
                        let rest_chain: Option<Vec<u32>> = {
                            let mut c = Vec::with_capacity(rest.len());
                            let ok = rest.iter().all(|s| match s {
                                Proj::Field(i) => {
                                    c.push(*i);
                                    true
                                }
                                _ => false,
                            });
                            if ok {
                                Some(c)
                            } else {
                                None
                            }
                        };
                        let mut dropped = false;
                        for ((l, f), v) in st.env.fields.iter() {
                            if *l != *cal {
                                continue;
                            }
                            match &rest_chain {
                                Some(rc) if rc.is_empty() => {
                                    env.fields.insert((cl, *f), *v);
                                }
                                Some(rc) => {
                                    let mut key = rc.clone();
                                    key.push(*f);
                                    env.nested.insert((cl, key), *v);
                                }
                                None => dropped = true,
                            }
                        }
                        for ((l, chain), v) in st.env.nested.iter() {
                            if *l != *cal {
                                continue;
                            }
                            match &rest_chain {
                                Some(rc) => {
                                    let mut key = rc.clone();
                                    key.extend_from_slice(chain);
                                    env.nested.insert((cl, key), *v);
                                }
                                None => dropped = true,
                            }
                        }
                        for ((l, k), v) in st.env.elems.iter() {
                            if *l != *cal {
                                continue;
                            }
                            if rest.is_empty() {
                                env.elems.insert((cl, *k), *v);
                            } else if let Some(rc) = &rest_chain {
                                // An array *argument* handed over as a whole field-path
                                // target (`&mut x.a`): the callee's `_1` is the array, so
                                // its element `k` is the caller's `<target>[k]`, which lives
                                // in `elems_path` under the target's field chain. Without
                                // this the element was dropped and the caller read its own
                                // seed (`set_first_of(&mut x.a); x.a[0]` was `Incomplete` in
                                // *both* directions). The chain is non-empty here -- the
                                // empty one is the whole-local arm above -- and the entry
                                // exists only because the argument is an array: a struct or
                                // tuple argument's parts live in `fields`/`nested`, never
                                // here, so this cannot re-base a scalar onto an array key.
                                env.elems_path.insert((cl, rc.clone(), *k), *v);
                            } else {
                                // An element under a sub-place target that is not a field
                                // chain (`&mut x.a[0]`) has no key in this store. Leaving the
                                // caller's element would be a stale value, so the caller's
                                // parts go instead -- precision lost, never a wrong value
                                // kept.
                                dropped = true;
                            }
                        }
                        // Elements of field-path arrays (`x.a[0]`) the callee wrote.
                        // These live in their own store, keyed by the whole chain, so
                        // the loop above never sees them: without this one a helper's
                        // `x.a[0] = 9` died with the frame and the caller read its own
                        // seed, so the false `ret == 5` was **proved** against a body
                        // returning 9. A whole-local target re-bases the callee's chain
                        // under the caller's local unchanged; a sub-place target whose
                        // chain is a field chain prefixes it (`&mut o.i` makes the
                        // callee's `_1.a[0]` the caller's `o.i.a[0]`), and one that is
                        // not (an element target, `&mut x.a[0]`) has no representable
                        // key, so the caller's parts go rather than a stale value being
                        // kept.
                        for ((l, chain, k), v) in st.env.elems_path.iter() {
                            if *l != *cal {
                                continue;
                            }
                            match &rest_chain {
                                Some(rc) => {
                                    let mut full = rc.clone();
                                    full.extend_from_slice(chain);
                                    env.elems_path.insert((cl, full, *k), *v);
                                }
                                None => dropped = true,
                            }
                        }
                        if dropped {
                            env.forget_parts(cl);
                        }
                    }
                    if let Some(dest) = &caller.ret_dest {
                        // A reference the callee *returned*: `identity(_3) -> _2`
                        // where the callee's `_0` addressed its argument. The
                        // callee's local indices mean nothing in the caller's
                        // frame, but `ref_origin` records which caller local the
                        // reference was built from, so the caller's destination can
                        // be pointed at that storage. Without this the returned
                        // reference had no address in the caller, `*r = 5` was
                        // dropped, and the false `ret == 0` was **proved**.
                        // The callee's returned reference names a place in the
                        // *callee's* terms. Translate its head through
                        // `arg_source`: a head that is a reference argument becomes
                        // the caller's place, and the returned projection is
                        // appended -- `&mut self.lo` returns `_1.0`, and `_1` is the
                        // caller's `c`, so the caller's destination is `c.lo`. A
                        // head that is *not* an argument is the callee's own
                        // storage, which dies at return; nothing is recorded and a
                        // write through the returned reference is dropped rather
                        // than aimed at a foreign place.
                        if let Some(o) = st.env.ref_origin.get(&0).cloned() {
                            if let Some(src) = st.env.arg_source.get(&o.local).cloned() {
                                // Two rewrites turn the callee's origin into a place in
                                // the caller, and both are needed for an *element*:
                                //
                                // `resolve` collapses a deref of a local whose address
                                // was recorded; then a leading deref is stripped
                                // outright, because the head here is a reference
                                // *argument* (`arg_source` holds only those) and `src`
                                // already names its referent. `&mut a[0]` on a
                                // whole-array argument is `(*_1)[_2]`, and `_1` is that
                                // argument, so without the strip the deref lands in the
                                // middle of the caller's place where no store is keyed
                                // -- the write is dropped and a false contract about the
                                // seed is *proved*.
                                //
                                // `pin_index_vars` then resolves the `IndexVar` the dump
                                // prints (`_2` for the literal `0`), which dies at the
                                // call boundary. Only the callee's own projection is
                                // pinned: the caller's `src.proj` names *caller* locals,
                                // so resolving it against this frame would read the
                                // wrong local and is carried through as it is.
                                let mut o = st.env.resolve(&o);
                                if matches!(o.proj.first(), Some(Proj::Deref)) {
                                    o.proj.remove(0);
                                }
                                let o = st.env.pin_index_vars(&o);
                                // An `IndexVar` that is *not* pinned -- a symbolic index
                                // the contract does not fix -- names a callee local that
                                // means nothing in the caller. Carried across, the caller
                                // reads it as *its own* local of that number, which is a
                                // different argument, and the write lands on whatever
                                // element that happens to hold: `*x.nth_mut(i) = 9` with a
                                // parameter before `i` aimed the write at `x.a[zero]` --
                                // the seed element -- so the false `ret == 5` was
                                // *proved*.
                                //
                                // Dropping the reference alone is not enough: the write
                                // may hit *any* element, so a later read of `x.a[0]` must
                                // not fall back to its seed (that turned the false proof
                                // around rather than removing it -- `ret == 5` became
                                // provable). The array's elements are poisoned instead, so
                                // every read is unknown: the write is lost, never
                                // mis-aimed, and no stale seed survives it.
                                if o.proj.iter().any(|s| matches!(s, Proj::IndexVar(_))) {
                                    // The array's field chain is the `Field` steps that
                                    // lead up to the index; the index step and anything
                                    // past it are not part of the path.
                                    let mut chain = field_steps(&src.proj).unwrap_or_default();
                                    for step in &o.proj {
                                        match step {
                                            Proj::Field(f) => chain.push(*f),
                                            _ => break,
                                        }
                                    }
                                    env.poison_array_under(src.local, &chain);
                                } else {
                                    let mut proj = src.proj.clone();
                                    proj.extend_from_slice(&o.proj);
                                    let place = Place { local: src.local, proj };
                                    env.addressed.insert(dest.local, place.clone());
                                    env.ref_origin.insert(dest.local, place);
                                }
                            }
                        }
                        env.set(dest, ret);
                        // A tuple return has components, and the callee stored
                        // them in its *own* return place (`_0.0`, `_0.1`). The
                        // caller's `min2(a, b).0` reads `_2.0`, so the components
                        // have to cross the boundary with the return value.
                        // Carrying only the aggregate loses them, and a contract
                        // about `min2(a, b).0` is then unreadable rather than
                        // checked. They are copied under the *destination's*
                        // local, which is the place the caller actually reads.
                        //
                        // Only the components the callee wrote are copied, so a
                        // path that left `_0.1` unwritten leaves the caller's
                        // `dest.1` unknown rather than inventing a value.
                        if matches!(ret, Val::Agg) {
                            for ((l, k), v) in st.env.elems.iter() {
                                if *l != 0 {
                                    continue;
                                }
                                let p = Place {
                                    local: dest.local,
                                    proj: vec![Proj::Index(*k)],
                                };
                                env.set(&p, *v);
                            }
                            // A *struct* return keeps its fields and nested paths in the
                            // field stores, not in `elems`: `_0 = _1` copies `_1`'s parts
                            // through `copy_parts`, which writes `fields`/`nested`. Copying
                            // only `elems` lost them, so `id_inner(o.i).v` -- a nested
                            // aggregate handed to a helper by value and read back -- read
                            // `Unknown` while the contract was true of the body. This runs
                            // after the `elems` loop because clearing the destination's old
                            // fields must not also clear the tuple components just written;
                            // the nested paths are set last so the intermediate field write
                            // (which forgets the paths beneath it) cannot drop a leaf.
                            //
                            // Only when the destination is a whole local, which is the shape
                            // a call's destination has. A returned whole value replaces every
                            // part, so the destination's old fields and nested paths are
                            // dropped first: keeping one the callee did not write would be a
                            // *wrong* value rather than a missing one.
                            if dest.proj.is_empty() {
                                env.fields.retain(|(l, _), _| *l != dest.local);
                                env.nested.retain(|(l, _), _| *l != dest.local);
                                env.elems_path.retain(|(l, _, _), _| *l != dest.local);
                                for ((l, f), v) in st.env.fields.iter() {
                                    if *l != 0 {
                                        continue;
                                    }
                                    let p = Place {
                                        local: dest.local,
                                        proj: vec![Proj::Field(*f)],
                                    };
                                    env.set(&p, *v);
                                }
                                for ((l, chain, k), v) in st.env.elems_path.iter() {
                                    if *l != 0 {
                                        continue;
                                    }
                                    env.elems_path.insert((dest.local, chain.clone(), *k), *v);
                                }
                                for ((l, chain), v) in st.env.nested.iter() {
                                    if *l != 0 {
                                        continue;
                                    }
                                    let p = Place {
                                        local: dest.local,
                                        proj: chain.iter().map(|i| Proj::Field(*i)).collect(),
                                    };
                                    env.set(&p, *v);
                                }
                            }
                        }
                    }
                    // Restore the caller's loop cut, which entering the callee
                    // cleared. Without this the resumed caller has no cut, so the
                    // next edge into its loop header is unwound rather than
                    // checked against the invariant -- and a loop whose step is a
                    // same-dump call is reported as a cutoff once it passes
                    // `DEFAULT_UNWIND`, even when the invariant was sufficient.
                    // The callee's `cut` is discarded: it named the callee's loop,
                    // if any, and the callee has returned.
                    let cut = caller.saved_cut.clone();
                    work.push(State {
                        block: caller.ret_target,
                        frame: *caller,
                        path: st.path,
                        env,
                        visits: st.visits,
                        depth: st.depth.saturating_sub(1),
                        cut,
                    });
                }
            }
        }
        Term::Unreachable => {
            report.obligations.push(Obligation {
                kind: ObligationKind::Unreachable,
                verdict: find_obligation(st.path, pins),
            });
        }
        Term::Assert { cond, negated, msg, target, .. } => {
            // `assert(c)` panics when `c` is false, so a panic is possible
            // exactly when `path ∧ ¬c` is satisfiable. rustc prints the
            // overflow and divide-by-zero checks as `assert(!bit)`, so `negated`
            // flips which polarity is the failing one.
            let c = operand(&mut st.env, cond);
            let holds = match c {
                Val::Bool(p) => p,
                // A bit-vector condition is true when it is non-zero. An assert
                // condition is a `bool` in Rust, so the sign here is irrelevant;
                // it is carried for uniformity, not used.
                Val::Sym(v, _) => smt::not(smt::eq_const(v, 0)),
                Val::Agg | Val::Unknown => {
                    report.unknown_paths.push(format!("unmodelled assert condition: {msg}"));
                    return;
                }
            };
            let satisfied = if *negated { smt::not(holds) } else { holds };
            let bad = smt::and(st.path, smt::not(satisfied));
            report.obligations.push(Obligation {
                kind: ObligationKind::Panic { message: msg.clone() },
                verdict: find_obligation(bad, pins),
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
            advance(prog, next, *target, report, work, pins);
        }
        Term::SwitchInt { discr, cases, otherwise } => {
            let d = operand(&mut st.env, discr);
            let arm = |k: u128, positive: bool| -> Option<Pred> {
                match d {
                    Val::Bool(p) => Some(if (k != 0) == positive { p } else { smt::not(p) }),
                    // A `switchInt` compares against a discriminant, which is an
                    // integer: equality does not depend on the sign.
                    Val::Sym(v, _) => {
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
                advance(prog, next, *target, report, work, pins);
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
            advance(prog, next, *otherwise, report, work, pins);
        }
        Term::Call { callee, args, dest, target } => {
            let Callee::Name(name) = callee else {
                report.unknown_paths.push("indirect call not modelled".into());
                return;
            };
            // A self-call is answered by the function's own contract when it
            // carries a `decreases:` measure, rather than inlined: inlining it
            // would only unroll once and hit the depth bound. See
            // [`try_recursive_call`]. It returns `Some` when it handled the call
            // (including the failure case), and `None` when the call is not
            // recursive, so the inliner below still sees every other call.
            if try_recursive_call(
                prog, &mut st, root, name, args, dest, *target, rec, report, work, pins,
            )
            .is_some()
            {
                return;
            }
            // The same-dump lookup runs *first*, and on the full name. A `core::num`
            // name is only an intrinsic when the dump has no body for it: the model in
            // `intrinsics` is a definition of `core`'s function, and a user function
            // that happens to be called `wrapping_add` is a different function.
            // Answering from `intrinsics` first let such a function shadow the
            // intrinsic, so a `wrapping_add` that returns `0` had its *actual* body
            // ignored and was modelled as `a + b` -- a false proof of `ret == 3` for
            // `a == 1, b == 2`.
            //
            // Matching the full name, not the suffix, is what keeps the other
            // direction honest too. rustc prints the intrinsic as the qualified path
            // `core::num::<impl u8>::wrapping_add`, which never equals a plain
            // same-dump name, so a user `wrapping_add` and `u8::wrapping_add` can
            // coexist: the first is inlined by the exact match, the second falls
            // through to the model.
            let exact = prog.fns.iter().position(|g| g.name == *name);
            if exact.is_none() {
                if let Some(done) =
                    try_intrinsic(prog, st.frame.func, name, args, dest, &mut st.env)
                {
                    let next = match done {
                        Ok(()) => State { block: *target, ..st },
                        Err(e) => {
                            report.unknown_paths.push(e);
                            return;
                        }
                    };
                    advance(prog, next, *target, report, work, pins);
                    return;
                }
            }
            if st.depth + 1 >= DEFAULT_INLINE_DEPTH {
                report.unknown_paths.push(format!("call depth limit reached at `{name}`"));
                return;
            }
            // Only same-dump calls can be inlined. Assuming a return value for
            // anything else would be assuming the conclusion, so it is unknown.
            //
            // An exact match is the free-function case: rustc prints a same-crate
            // free function's call and its definition by the same bare name.
            // Otherwise the call is a method (`Type::m`) whose definition rustc
            // prints as `<impl at …>::m`, so only the tail is shared -- but the
            // tail alone is not enough, because `Vec2::push` and `Vec::<u8>::push`
            // (or a free `wrapping_add` and `core::num::<impl u8>::wrapping_add`)
            // share one. Inlining the wrong body is a false proof, so the tail
            // match also requires the same method `self` type and a unique
            // candidate; see [`resolve_callee`].
            let inline_idx = resolve_callee(prog, name);
            let Some(idx) = inline_idx else {
                report.unknown_paths.push(format!("call to unmodelled function `{name}`"));
                return;
            };
            let callee_fn = &prog.fns[idx];
            // A callee taking `&mut &mut T` is refused. Its `**v = x` writes
            // through two levels: the outer reference's referent lives in the
            // *caller's* frame, and the callee reaches it through its own `(*_1)`,
            // whose local index means something else in each frame. One level of
            // that is modelled (the referent's parts are carried in and the
            // post-state copied back); two is not, and `relay(&mut r)` with
            // `relay(v: &mut &mut u8) { **v = 5 }` had its write dropped -- so
            // `requires: x == 0` / `ensures: ret == 0` was **proved** against a
            // body that returns 5. Refusing the call leaves the true contract
            // unproved instead of proving the false one, which is the honest
            // failure mode. `&mut T` is unaffected: its argument is not a
            // reference to a reference.
            if callee_fn
                .arg_locals
                .iter()
                .any(|l| matches!(callee_fn.ty_of(*l), Some(Ty::Ref(inner)) if matches!(**inner, Ty::Ref(_))))
            {
                report.unknown_paths.push(
                    "call to a function taking `&mut &mut T` is not modelled".into(),
                );
                return;
            }
            let Some(b0) = callee_fn.blocks.first() else {
                report.unknown_paths.push(format!("callee `{name}` has no body"));
                return;
            };
            let mut env = Env::with_enums(&prog.enums, &prog.consts);
            // Which caller locals were handed over through a reference, so the
            // return path knows whose store the callee's post-state belongs to.
            let mut by_ref: Vec<(Place, u32)> = Vec::new();
            for (i, a) in args.iter().enumerate() {
                let v = operand(&mut st.env, a);
                let Some(&l) = callee_fn.arg_locals.get(i) else { continue };
                env.locals.insert(l, v);
                // A reference argument may be dereferenced inside the callee
                // (`*_1 = 5`), and `Ty::Ref` is modelled as its referent, so `_1`
                // *is* the value `*_1` names. `verify_fn` marks the root's
                // reference arguments this way; the inliner builds the callee's
                // env itself, so it has to mark them too, or the callee's
                // `(*_1) = v` is treated as a deref with no recorded referent and
                // the write is dropped -- which is how a `&mut u8` helper's write
                // was lost and a false `ret == 0` contract was proved.
                if matches!(callee_fn.ty_of(l), Some(Ty::Ref(_))) {
                    env.deref_ok.insert(l, ());
                }
                let Place { local: cl, proj } = match a {
                    Operand::Copy(p) | Operand::Move(p) => p,
                    Operand::Const(_) => continue,
                };
                if !proj.is_empty() {
                    continue;
                }
                // The *storage* the argument denotes, which is the caller's local
                // itself for a by-value argument and the pointee for a reference.
                //
                // `pointee`, not `resolve`: `resolve` only follows an explicit
                // `*_p` projection, and `set5(&mut x)` hands the callee a *temp*
                // (`_5 = &mut _2; set5(_5)`) whose place has no projection at all.
                // `pointee` follows the recorded address of an empty-projection
                // local, which is what turns `_5` into the `_2` the caller reads.
                //
                // The whole argument's state -- its element store *and* its parts
                // -- is carried in, keyed on the callee's local. A reference shares
                // the caller's storage, so the callee's `a[0]`, `c.lo` and `o.i.v`
                // must read the caller's values; without them a helper that indexes
                // or reads a field has an unmodelled operand and the caller's
                // contract stays unproved, while a read-modify-write helper
                // (`c.lo = c.lo + d`) cannot be modelled at all.
                //
                // The state is *cloned*, never shared: the callee must not be able
                // to write the caller's copy directly, or a by-value argument would
                // behave like a reference. Only a reference argument's post-state
                // is copied back (see the return path).
                let is_ref = arg_is_ref(callee_fn, i);
                let source = if is_ref {
                    st.env.pointee(&Place { local: *cl, proj: Vec::new() })
                } else {
                    Place { local: *cl, proj: Vec::new() }
                };
                let sl = source.local;
                // The value *at the target*, and the target's parts. The value is
                // read through `get`, not out of `locals`, because a sub-place
                // target has no whole-local entry: `&mut c.lo` targets `c.0`, whose
                // value lives in `fields`. Reading `locals[source.local]` there
                // returned the *struct's* absent value, so the callee's `*v` was
                // `Unknown` and a helper that *reads* through its argument (`*v`,
                // `*v = *v + 1`, a two-reference `swap`) had an unmodelled operand --
                // while a helper that only *wrote* (`*v = 5`) worked, because the
                // write creates the value the copy-back then reads. `Ty::Ref` is
                // modelled as its referent, so the callee's local *is* the target's
                // value and this is a copy of what the caller holds, not an
                // assumption about it.
                //
                // The part stores are copied only for a *whole-local* target, and
                // they are keyed by `source.local` because that is the local that
                // owns them. For a sub-place target the parts belong to the target's
                // own type, which the value copy above already covers for a scalar;
                // copying the enclosing local's parts instead would hand the callee
                // a sibling field it does not own.
                if is_ref {
                    let v = st.env.get(&source);
                    env.locals.insert(l, v);
                }
                if source.proj.is_empty() {
                    if let Some(store) = st.env.indexed.get(&sl).cloned() {
                        env.indexed.insert(l, store);
                    }
                    for ((l0, f), v) in st.env.fields.iter() {
                        if *l0 == sl {
                            env.fields.insert((l, *f), *v);
                        }
                    }
                    for ((l0, chain), v) in st.env.nested.iter() {
                        if *l0 == sl {
                            env.nested.insert((l, chain.clone()), *v);
                        }
                    }
                    for ((l0, k), v) in st.env.elems.iter() {
                        if *l0 == sl {
                            env.elems.insert((l, *k), *v);
                        }
                    }
                    // Elements of field-path arrays (`o.a[0]`) are carried in for the
                    // same reason the plain elements are: the callee's `(_1.0)[k]` is
                    // the caller's `o.a[k]`, so a helper that *reads* one has to see
                    // the caller's seed. Without this the callee read `Unknown`, and a
                    // helper that wrote the element had its write die with the frame --
                    // the caller read its own seed, so `requires: x.a[0] == 5;
                    // ensures: ret == 5` on `set_first(x); x.a[0]` was **proved**
                    // against a body that returns 9.
                    for ((l0, chain, k), v) in st.env.elems_path.iter() {
                        if *l0 == sl {
                            env.elems_path.insert((l, chain.clone(), *k), *v);
                        }
                    }
                } else if is_ref {
                    // A sub-place target whose own type is an aggregate: `&mut
                    // o.i`. The callee's `i.v` is the caller's `o.i.v`, so the
                    // target's parts are carried in *re-based* -- the target's
                    // chain is dropped from the front of each key and the callee's
                    // local takes its place. This is the exact inverse of the
                    // re-based copy-back, and it is what lets a helper *read* a
                    // nested aggregate it was handed (`read_inner(&o.i)`), which is
                    // otherwise an unmodelled operand.
                    let mut rc = Vec::with_capacity(source.proj.len());
                    let ok = source.proj.iter().all(|p| match p {
                        Proj::Field(i) => {
                            rc.push(*i);
                            true
                        }
                        _ => false,
                    });
                    if ok {
                        // A remainder of one step is a *field* in this store's
                        // spelling (`fields` is keyed by a single index, `nested` by
                        // a chain of two or more), so the two lengths have to be
                        // routed apart or the callee's `_1.0` -- a lone field read --
                        // would consult `fields` and miss.
                        for ((l0, chain), v) in st.env.nested.iter() {
                            if *l0 != sl || !chain.starts_with(&rc) {
                                continue;
                            }
                            let rem = &chain[rc.len()..];
                            match rem {
                                [f] => {
                                    env.fields.insert((l, *f), *v);
                                }
                                [] => {}
                                _ => {
                                    env.nested.insert((l, rem.to_vec()), *v);
                                }
                            }
                        }
                        // Elements of field-path arrays under a sub-place target, the
                        // same re-basing as the nested parts above: `&mut o.i` makes the
                        // caller's `o.i.a[0]` the callee's `_1.a[0]`, so the chain has
                        // the target's prefix dropped. Without this a helper that only
                        // *reads* the element through its argument (`read_inner(&o.i)` ->
                        // `i.a[0]`) saw `Unknown` and its contract was unreadable -- an
                        // incompleteness where the true contract should decide.
                        for ((l0, chain, k), v) in st.env.elems_path.iter() {
                            if *l0 != sl || !chain.starts_with(&rc) {
                                continue;
                            }
                            let rem = &chain[rc.len()..];
                            if rem.is_empty() {
                                // The target *is* the array (`peek_of(&x.a)`): in the
                                // callee's terms its argument is a whole local, so the
                                // callee's `_1[k]` read consults the *plain* element store,
                                // not the field-path one. Without this the callee read
                                // `Unknown` and a read-only helper's contract was
                                // unreadable -- an incompleteness where the true contract
                                // should decide. This is the exact inverse of the write-back
                                // arm that re-bases a whole-array target's element.
                                env.elems.insert((l, *k), *v);
                            } else {
                                env.elems_path.insert((l, rem.to_vec(), *k), *v);
                            }
                        }
                    }
                }
                if is_ref {
                    by_ref.push((source.clone(), l));
                }
                // The origin local of a reference argument, in the *caller's*
                // frame, so a reference the callee returns can be resolved once it
                // is back in the caller. A `&mut x` argument is passed through a
                // temp (`_5 = &mut _2; set5(_5)`), so the origin is `_5`'s origin --
                // `_2` -- not `_5` itself.
                if matches!(callee_fn.ty_of(l), Some(Ty::Ref(_))) {
                    // The argument denotes `source` in the caller's frame, and
                    // inside the callee it is the local `l` itself. Recording both
                    // is what lets a reference the callee returns be translated
                    // back: the callee's `_0` names `l` (or a projection of it),
                    // and `arg_source` turns that into the caller's place.
                    env.arg_source.insert(l, source.clone());
                    env.ref_origin.insert(l, Place { local: l, proj: Vec::new() });
                }
            }
            let caller = Frame {
                func: st.frame.func,
                ret_target: *target,
                ret_dest: Some(dest.clone()),
                // The caller's locals are put aside here and restored on return.
                // `env` below is the callee's, freshly built from the arguments.
                saved_env: Some(st.env.clone()),
                // The caller's loop cut is put aside for the same reason: it
                // describes the caller's loop, and the caller is still inside it
                // when this call returns.
                saved_cut: st.cut.clone(),
                by_ref: by_ref.clone(),
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
                    saved_cut: None,
                    by_ref: Vec::new(),
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
fn operand(env: &mut Env, o: &Operand) -> Val {
    match o {
        Operand::Copy(p) | Operand::Move(p) => {
            // A dereference of an addressed local names the place it addresses,
            // so `_2 = &_1; *_2` reads `_1` -- including through a subscript,
            // which is why the rewrite comes before `read_indexed`.
            let p = &env.resolve(p);
            // A slice element is created on first read, so it goes through the
            // mutable path before the ordinary one.
            if let Some(v) = env.read_indexed(p) {
                return v;
            }
            env.get(p)
        }
        Operand::Const(c) => match c {
            Const::UInt(v, ty) => match ty.as_ref().and_then(|t| t.width()) {
                Some(1) => Val::Bool(smt::truth(*v == 1)),
                // A constant's type suffix is the only place its signedness
                // appears -- `const 0_i8` versus `const 0_u8` -- so the sign is
                // read here, once, and travels with the value.
                Some(w) => {
                    // No suffix means the dump printed no type, so there is no
                    // sign to read. It is `Unknown`, not `Unsigned`: defaulting to
                    // unsigned here is exactly the false proof this type exists to
                    // prevent, and the callers refuse an `Unknown` sign.
                    let sign = ty.as_ref().map(Sign::of).unwrap_or(Sign::Unknown);
                    Val::Sym(smt::word(*v as u64, w), sign)
                }
                None => Val::Unknown,
            },
            Const::Bool(b) => Val::Bool(smt::truth(*b)),
            // An enum variant *construction*: `Mode::Idle`. The dump prints it as
            // a path constant, and it is the one place a tag is a *known* value
            // rather than an input -- a locally built enum then has a constant
            // discriminant, which is what lets `let m = Mode::Idle; match m`
            // decide instead of leaving the switch unmodelled. The variant's index
            // is read from the program's enum layouts, the same table a downcast
            // resolves against, so the construction and the match agree by
            // construction.
            // A variant construction whose destination `eval_rvalue` could not
            // resolve (it has no enum layout) stays unknown; the well-typed path
            // is in `eval_rvalue::Use`, where the destination's width is known.
            // A named `const` item: `_0 = const K`, where the item's own body is
            // printed separately as `const K: u8 = const 5_u8;`. The value is
            // inlined from the table rather than left unknown, so the use site
            // folds. rustc const-evaluates the item, so its body is already a
            // literal with a type suffix -- which is where the width and sign
            // come from, exactly as for an inline literal.
            //
            // A path constant that is *not* a known `const` -- an enum variant
            // construction (`Mode::Idle`), or a constant whose body is an
            // expression rather than a literal -- stays unknown; the enum case is
            // resolved by the caller in `eval_rvalue`, which knows the
            // destination's width.
            Const::Other(name) => match env.consts.get(name) {
                Some(Const::UInt(v, ty)) => match ty.as_ref().and_then(|t| t.width()) {
                    Some(1) => Val::Bool(smt::truth(*v == 1)),
                    Some(w) => {
                        let sign = ty.as_ref().map(Sign::of).unwrap_or(Sign::Unknown);
                        Val::Sym(smt::word(*v as u64, w), sign)
                    }
                    None => Val::Unknown,
                },
                Some(Const::Bool(b)) => Val::Bool(smt::truth(*b)),
                _ => Val::Unknown,
            },
            Const::Unit => Val::Unknown,
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
                    // The literal has no suffix, so it takes the place's type --
                    // and therefore the place's signedness. A place whose type
                    // the dump did not print leaves the sign unknown, which the
                    // consumers refuse rather than read as unsigned.
                    let sign = type_of_place(f, dest).map(|t| Sign::of(&t))
                        .unwrap_or(Sign::Unknown);
                    return Val::Sym(smt::word(*v as u64, w), sign);
                }
            }
            let v = operand(env, o);
            // An enum variant *construction*: `_1 = Mode::Idle`. It is a
            // constant with no width of its own -- the enum's tag width is the
            // discriminants', which only the destination's enum layout knows --
            // so it is resolved here, against the destination, rather than in
            // `operand`. Getting the width right is what lets the tag be
            // `discriminant`-ed and compared against the arm constants.
            if let Operand::Const(Const::Other(name)) = o {
                if let Some(i) = crate::mir::parse::variant_index(name, &env.enums) {
                    // The discriminants' width wins over `dest_w`: the dump
                    // declares an enum local as `isize`, so `dest_w` is 64 and
                    // would put a locally built tag in a different width from a
                    // seeded one. The discriminants' width is the tag's real
                    // domain.
                    let w = enum_tag_width(f, dest, &env.enums)
                        .or(dest_w)
                        .unwrap_or(64);
                    env.set_discriminant(dest.local, Val::Sym(smt::word(i, w), Sign::Unsigned));
                    return Val::Agg;
                }
            }
            // A whole-struct copy (`c = d`) carries the value's *parts* across, so
            // `c.lo` afterwards reads `d.lo`. `Val::Agg` is returned when parts
            // moved, which is what tells `set` not to clear the parts just copied
            // -- the same convention an aggregate literal uses.
            if dest.proj.is_empty() {
                if let Operand::Copy(q) | Operand::Move(q) = o {
                    if env.copy_parts(q, dest.local) {
                        return Val::Agg;
                    }
                }
            }
            v
        }
        Rvalue::Binary(op, a, b) => {
            // The signedness of the *left* operand decides what `Shr` means and
            // what `<`/`<=`/`>`/`>=` mean; the amount's type is irrelevant and
            // rustc keeps it a distinct `u32`. That sign is now *in* the value
            // (`Val::Sym(word, sign)`), so there is no separate lookup that a
            // later caller could forget: an operand whose type cannot be resolved
            // is `Val::Unknown` here, and `eval_binary` refuses it rather than
            // reading it as unsigned.
            let (x, y) = (operand(env, a), operand(env, b));
            eval_binary(*op, x, y, dest_w)
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
            let res = eval_binary(*op, x, y, Some(w));
            env.set(&Place { local: dest.local, proj: vec![Proj::Field(0)] }, res);
            match overflow_pred(*op, x, y, w) {
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
                // `!x` is a bitwise complement, so the result has the operand's
                // type and keeps its sign. The mask must therefore be the
                // *operand's* width, which the value carries; `dest_w` is only a
                // cross-check. Deriving the mask from `dest_w` is right exactly
                // when the two agree, so a disagreement -- the dump and the value
                // disagreeing about the type -- is refused rather than masked at
                // a width the value does not have.
                (UnOp::Not, Val::Sym(s, sign)) => {
                    let w = smt::bits(s);
                    if dest_w.is_some_and(|dw| dw != w) {
                        return Val::Unknown;
                    }
                    Val::Sym(smt::bxor(s, smt::all_ones(w)), sign)
                }
                // `-x` is `0 - x`, which is the right bit pattern for every input
                // including `MIN` (it wraps back to `MIN`, which is what rustc's
                // own `assert(x != MIN)` guards and then computes anyway). The
                // result has the operand's type, so it keeps the operand's sign.
                (UnOp::Neg, Val::Sym(s, sign)) => match dest_w {
                    Some(w) => Val::Sym(smt::sub(smt::word(0, w), s), sign),
                    None => Val::Unknown,
                },
                _ => Val::Unknown,
            }
        }
        Rvalue::Cast(o, ty) => {
            // A cast between reference types (`&[u8; 4]` to `&[u8]`) does not
            // change *what* is addressed, only how it is described. The address
            // mapping is therefore carried across, which is what makes
            // `let r = &a; r.len()` on an array read the array's own length: the
            // `PtrMetadata` after the cast names the slice local, and only the
            // carried mapping gets it back to the array. A cast whose target is
            // not a reference is a numeric cast and carries nothing.
            if matches!(ty, Ty::Ref(_)) {
                if let Operand::Copy(q) | Operand::Move(q) = o {
                    let target = env.resolve(q);
                    if let Some(p) = env.addressed.get(&target.local).cloned() {
                        env.addressed.insert(dest.local, p);
                    }
                }
            }
            let v = operand(env, o);
            // The cast's *result* has the target type, so its sign is the
            // target's. The source's sign comes out of the value, which is what
            // decides whether a widening sign-extends or zero-fills.
            let out_sign = Sign::of(ty);
            match (v, ty.width()) {
                // Widening a *signed* value sign-extends: `-1i8 as i16` is `-1`,
                // not `255`. `truncate` zero-fills, so using it for every cast
                // modelled `-1i8 as i16` as `255` and proved
                // `requires: a == -1; ensures: ret == 255` -- a reachable false
                // proof. `sign_extend` truncates first when the target is no
                // wider, so a narrowing cast is unaffected. An *unsigned* source
                // zero-fills, which is what `truncate` does.
                (Val::Sym(s, src), Some(w)) => {
                    // A source sign the dump did not print is a refusal: zero
                    // -filling a signed value is the `-1i8 as i16` false proof,
                    // and sign-extending an unsigned one turns `255u8 as u16`
                    // into `65535`. Neither reading is safe to guess.
                    let bits = match src.known() {
                        Some(true) => smt::sign_extend(s, w),
                        Some(false) => smt::truncate(s, w),
                        None => return Val::Unknown,
                    };
                    Val::Sym(bits, out_sign)
                }
                (Val::Bool(p), Some(1)) => Val::Bool(p),
                (Val::Bool(p), Some(w)) => {
                    Val::Sym(smt::ite(p, smt::word(1, w), smt::word(0, w)), out_sign)
                }
                _ => Val::Unknown,
            }
        }
        Rvalue::Variant(name, ops) => {
            // An enum variant construction with a payload. The tag is the
            // variant's discriminant -- resolved against the program's enum
            // layouts, the same table a `match`'s downcast reads -- and the
            // operands are written as the variant's fields, so the downcast read
            // finds what the construction wrote.
            let Some(variant) = crate::mir::parse::variant_index(name, &env.enums) else {
                return Val::Unknown;
            };
            let w = enum_tag_width(f, dest, &env.enums).or(dest_w).unwrap_or(64);
            env.set_discriminant(dest.local, Val::Sym(smt::word(variant, w), Sign::Unsigned));
            for (i, o) in ops.iter().enumerate() {
                let v = operand(env, o);
                let pw = operand_width(f, o).unwrap_or(0);
                env.set_payload(dest.local, variant, v, pw);
                env.set(&Place { local: dest.local, proj: vec![Proj::Field(i as u32)] }, v);
            }
            Val::Agg
        }
        Rvalue::Aggregate(ops) => {
            for (i, o) in ops.iter().enumerate() {
                let v = operand(env, o);
                env.set(&Place { local: dest.local, proj: vec![Proj::Index(i as u64)] }, v);
            }
            Val::Agg
        }
        Rvalue::Struct(ops) => {
            // A struct literal writes *fields*, not elements. The two are
            // different stores on purpose: a contract names a struct field
            // (`c.lo`) and never a tuple component by name, and a field read
            // (`_1.0`) consults `fields` first. Storing these under `Index` would
            // leave the read looking in a store the literal never wrote, which is
            // how `let c = Config { lo: 7, .. }; c.lo` stayed unknown.
            //
            // The printed order is declaration order, which is the order the
            // `Field(N)` projections index, so position `i` here is field `i`.
            for (i, o) in ops.iter().enumerate() {
                let v = operand(env, o);
                let dst = Place { local: dest.local, proj: vec![Proj::Field(i as u32)] };
                env.set(&dst, v);
                // An *aggregate operand* keeps its value in its parts, so `Outer { i: x, .. }`
                // stores the field's value but not `x`'s own `v`. A later read of the returned
                // `mk_outer(o.i).i.v` walks the nested chain and finds nothing. The parts are
                // re-rooted onto the field *after* the `set` above, because a field write
                // forgets the paths beneath it; the operand's own parts are untouched, so this
                // is a copy of what it holds rather than an assumption about it. The gate is the
                // operand's *type*, not its value: a by-value struct argument's parts live in
                // `fields`, so it reads `Unknown` as a whole and would be missed by a value
                // test.
                if let Operand::Copy(q) | Operand::Move(q) = o {
                    if matches!(v, Val::Agg) || matches!(type_of_place(f, q), Some(Ty::Other(_))) {
                        env.rebase_parts(q, &dst);
                    }
                }
            }
            Val::Agg
        }
        Rvalue::Ref(p) => {
            // `&place` addresses `place`. The local itself is not a modelled
            // value -- a pointer has no bit-vector meaning here -- so it reads
            // `Unknown`; what the reference *is* for this frontend is the mapping
            // `resolve` consults, and that is recorded here, at the one place a
            // reference is created.
            //
            // The place is stored as written, so `&_1.0` keeps its projection and
            // `(*_2)` later reads `_1.0` rather than the whole of `_1`.
            env.addressed.insert(dest.local, p.clone());
            // The *origin* of the reference, as the place it was built from -- in
            // this frame's terms. `_3 = &mut _1` records `_1`, and `_0 = &mut
            // (*_1).0` records `_1.0`. It is what lets a reference the callee
            // returns be re-based onto the caller's storage: without the projection
            // `*c.lo_mut() = 5` lost the write (the returned reference named
            // nothing), and the false `ret == 0` was **proved** while the true
            // `ret == 5` was refuted.
            env.ref_origin.insert(dest.local, p.clone());
            Val::Unknown
        }
        // `Len(p)` -- the length of a slice or array. `PtrMetadata` is how 1.99
        // and later lower the same query for a `&[T]`; older compilers (1.85, the
        // MSRV) lower it as `Len((*_1))` instead. The two mean the same number, so
        // they are modelled by the same code: refusing `Len` on a slice leaves the
        // bounds check above `a[i]` unmodelled on 1.85 and turns an otherwise
        // decidable corpus entry into an incomplete one.
        Rvalue::Len(p) => length_of(env, f, p),
        Rvalue::Unknown(_) => Val::Unknown,
        // `PtrMetadata(_1)` -- for a `&[T]` this is the slice's length. Modelled
        // only when the local is a slice the frontend bound a length for; any
        // other pointer has metadata this model cannot express, and answering
        // `Unknown` there is what keeps an invented length out of a proof.
        Rvalue::PtrMetadata(p) => length_of(env, f, p),
        Rvalue::Discriminant(p) => match env.discriminants.get(&p.local) {
            // The tag's width is the payload's, not the dump's `isize`. The
            // `switchInt` compares it against the small variant constants, so
            // the width only has to be wide enough to hold them; taking it from
            // the payload keeps `discriminant` and the payload in one width.
            Some(Val::Sym(tag, _)) => {
                // A seeded enum tag carries its own width; a synthesised
                // `Option` tag takes the payload's. Reading a seeded tag at the
                // dump's `isize` width would truncate nothing but would also
                // widen a 2-bit tag to 64, and `eq_const` then compares a
                // 64-bit word against the `u8`-typed place's expectations --
                // keeping the tag's own width is what the contract's `m ==
                // Mode::Run` was checked at.
                let w = env.tag_width(p.local).or_else(|| env.option_width(p.local)).unwrap_or(64);
                // A discriminant is an unsigned integer.
                Val::Sym(smt::truncate(*tag, w), Sign::Unsigned)
            }
            Some(v) => *v,
            // No modelled call wrote a tag here. An enum this frontend did not
            // build has an unknown tag, not tag zero -- guessing `None` would
            // send every path down the wrong arm.
            None => Val::Unknown,
        },
    }
}

/// The tag width for a place whose type is an enum: the discriminants', matching what
/// `spec::FieldEnv::bind_enum` binds a contract's tag to.
///
/// The dump declares an enum local as `isize`, but the tag's *domain* is the set
/// of variant discriminants, so their width is the one that can hold every tag
/// and no more. Using it here keeps a locally built enum's tag in the same width
/// as a seeded one, which is what makes `discriminant` read both back
/// consistently.
fn enum_tag_width(f: &MirFn, p: &Place, enums: &BTreeMap<String, EnumLayout>) -> Option<u8> {
    let Ty::Other(name) = type_of_place(f, p)? else { return None };
    let def = enums.get(&name)?;
    if def.variants.is_empty() {
        return None;
    }
    Some(def.tag_width())
}

/// The declared width of a place, following one level of tuple/array projection.
fn width_of(f: &MirFn, p: &Place) -> Option<u8> {
    let mut ty = f.ty_of(p.local)?.clone();
    for pr in &p.proj {
        ty = match (pr, &ty) {
            (Proj::Field(i), Ty::Tuple(ts)) => ts.get(*i as usize)?.clone(),
            (Proj::Index(_), Ty::Array(inner, _)) => (**inner).clone(),
            // `*r` for a `&T` has type `T`. The dump prints the deref as
            // `(*_1)` with no type, so the width has to come from the referent
            // the local was declared with. This is the same transparency the
            // executor applies when it reads the value.
            (Proj::Deref, Ty::Ref(inner)) => (**inner).clone(),
            // A downcast yields the payload, whose type the dump does not print
            // here. Reading it as the base type would mis-size the value: the
            // `u8` inside `Option<u8>` is not the `Option<u8>` local. The caller
            // supplies the width from the operator instead, so this declines.
            (Proj::Downcast(_), _) => return None,
            _ => return None,
        };
    }
    match &ty {
        Ty::Ref(inner) => inner.width(),
        t => t.width(),
    }
}

/// Whether the `i`-th argument is an indexed value passed through a reference
/// (`&[T]` or `&mut [T; N]`) rather than by value (`[T; N]`).
///
/// The distinction decides what a call does to the caller's store: a reference
/// shares it (the callee's post-state is the caller's), a by-value array is the
/// callee's own copy (the caller's is unchanged). Reading it off the callee's
/// declared parameter type is what keeps the two apart, because the *caller's*
/// operand type is the same for both.
/// True when argument `i` is passed by reference, so the callee's post-state for
/// that local is the caller's storage and must be copied back on return.
fn arg_is_ref(f: &MirFn, i: usize) -> bool {
    let Some(&l) = f.arg_locals.get(i) else { return false };
    matches!(f.ty_of(l), Some(Ty::Ref(_)))
}

/// The declared type of a place, resolving the projections the dump spells out.
///
/// A projection changes the type, and therefore the signedness: a `u8` element of
/// an `[u8; 4]` is unsigned, and a field of a tuple is whatever that field's type
/// is. Reading signedness off the base local would read the *wrong* type for
/// exactly the operands this exists to classify.
///
/// A struct-field projection is not resolvable here -- the dump prints
/// `_1: Config` and says nothing about `Config`'s layout -- so it returns `None`,
/// which the caller treats as "refuse" rather than "unsigned". In practice rustc
/// copies a field into a temp before using it as a binary operand, so this is the
/// defensive case; refusing is still the right answer if the shape ever changes.
/// The length of the slice or array a place denotes, or `Unknown`.
///
/// Both `PtrMetadata(p)` (a `&[T]`, from 1.99 on) and `Len(p)` (the same query
/// printed by older compilers, and an array's length) read through this. The place
/// is followed to its pointee first, so `_2 = _3 as &[u8]` after `_3 = &_1` names
/// `_1` here -- the place whose length is actually wanted.
fn length_of(env: &Env, f: &MirFn, p: &Place) -> Val {
    let p = env.pointee(p);
    match env.indexed.get(&p.local) {
        // A slice argument, whose length is a symbolic input.
        // A length is a `usize`, so it is unsigned.
        Some(s) => Val::Sym(s.len, Sign::Unsigned),
        // An *array* has its length in its type, not in `indexed`, so an unsized
        // `&[T; N]` would otherwise read unknown. The length is the type's
        // constant -- not a guess, and not a fresh variable: `[T; N]` coerces to a
        // slice of exactly `N`, so the two are the same number and a contract that
        // writes `a.len() == 4` on an `a: [u8; 4]` has something to agree with.
        None => match type_of_place(f, &p) {
            Some(Ty::Array(_, n)) => Val::Sym(smt::word(n, USIZE_WIDTH), Sign::Unsigned),
            _ => Val::Unknown,
        },
    }
}

fn type_of_place(f: &MirFn, p: &Place) -> Option<Ty> {
    let mut ty = f.ty_of(p.local)?.clone();
    for pr in &p.proj {
        ty = match (pr, &ty) {
            (Proj::Field(i), Ty::Tuple(ts)) => ts.get(*i as usize)?.clone(),
            (Proj::Index(_), Ty::Array(inner, _)) => (**inner).clone(),
            (Proj::Deref, Ty::Ref(inner)) => (**inner).clone(),
            (Proj::Downcast(_), _) => return None,
            _ => return None,
        };
    }
    Some(ty)
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
///
/// The operand's signedness is *in* the operand -- `Val::Sym(word, sign)` -- not
/// a parameter, which is the point of the type. It used to be a bare `bool` the
/// caller looked up separately, and a caller that looked it up wrong (or not at
/// all) turned `0 < a` on an `i8` into an unsigned comparison, under which
/// `i8::MIN` is the largest value. A wrong signedness is not a missed proof but a
/// wrong branch, so the sign has to travel with the bits it describes.
fn eval_binary(op: BinOp, a: Val, b: Val, width: Option<u8>) -> Val {
    // rustc gives both operands of a binary op the same type, so one sign serves
    // both. It is taken from the left, matching how the operand type is chosen.
    //
    // `Some(signed)` only when the sign was actually read. `None` is not
    // "unsigned": the signedness-sensitive operators below refuse it rather than
    // pick a meaning. The operators that do not read the sign (`+`, `&`, `==`)
    // proceed, because for them the sign is genuinely irrelevant.
    let signed = match a {
        Val::Sym(_, sign) => sign.known(),
        // A comparison of two `bool`s (`p == q`) has no integer sign to use, and
        // the arms below handle it before any sign is read. Anything else here
        // has no bit-vector at all and returns `Unknown` below.
        _ => Some(false),
    };
    match op {
        BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
            let (x, y) = match (a, b) {
                (Val::Sym(x, _), Val::Sym(y, _)) => (x, y),
                (Val::Bool(x), Val::Bool(y)) => {
                    return Val::Bool(match op {
                        BinOp::Eq => smt::iff(x, y),
                        BinOp::Ne => smt::xor(x, y),
                        _ => return Val::Unknown,
                    })
                }
                _ => return Val::Unknown,
            };
            // `==`/`!=` do not read the sign -- two bit patterns are equal or
            // not regardless of how they are read -- so they are answered before
            // the sign is required. The relational four do read it, and refuse
            // when it was not printed: `<` on an `i8` is not `<` on a `u8`, and
            // the unsigned form calls `-1` the largest value. A wrong choice is
            // not a missed proof but a wrong branch, which is a wrong answer.
            if matches!(op, BinOp::Eq | BinOp::Ne) {
                return Val::Bool(match op {
                    BinOp::Eq => smt::eq(x, y),
                    _ => smt::not(smt::eq(x, y)),
                });
            }
            let Some(signed) = signed else { return Val::Unknown };
            Val::Bool(match op {
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
                (Val::Sym(x, _), Val::Sym(y, _)) => (x, y),
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
            // Every arm below is an integer operation whose result has the
            // operand's type, so the result carries the operand's sign. The sign
            // is `Unknown` exactly when the dump did not print it; the arms that
            // do not read it still compute, and the two that do (`Div`/`Rem` and
            // the shifts) refuse below rather than guess.
            let sign = match signed {
                Some(true) => Sign::Signed,
                Some(false) => Sign::Unsigned,
                None => Sign::Unknown,
            };
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
                    // A signed operand needs the *signed* divider, and an
                    // unprinted sign is a refusal: the unsigned divider returns a
                    // huge positive quotient for `-7 / 2`, a wrong value rather
                    // than a weaker proof.
                    // A constant power-of-two divisor is a shift, not a division, and
                    // the difference is not a micro-optimisation: the signed divider's
                    // sign fixup is a BDD wall at 64 bits (9.3s for `sdiv(x, 2)` against
                    // 47ms for `udiv(x, 2)`), so `a / 2` on an `i64` was reported
                    // `incomplete`. The constant path is the shift identity and needs no
                    // fixup. `|c| == 1` is deliberately not taken -- `x / -1` overflows at
                    // `MIN` and the general path handles that explicitly -- and it would
                    // be a no-op shift anyway.
                    let Some(w) = width else { return Val::Unknown };
                    if signed == Some(true) {
                        if let Some((q, r)) = smt::const_of(y)
                            .map(|v| as_signed(v, w))
                            .and_then(|c| smt::sdivmod_pow2(x, c, w))
                        {
                            return Val::Sym(
                                match op {
                                    BinOp::Div => q,
                                    _ => r,
                                },
                                sign,
                            );
                        }
                    }
                    // The unsigned twin: a logical shift and a mask, with no sign to
                    // fix up. The general unsigned divider is not the signed one's wall,
                    // but it is still a `2 * w`-deep term, and a *symbolic* dividend
                    // through it is refused for the diagram's size -- `n / 4` on a `u64`
                    // with `n <= 1000` was `incomplete` in ~0.9 s. `d == 1` is left to the
                    // general path so the guard matches the signed branch.
                    if signed == Some(false) {
                        if let Some((q, r)) = smt::const_of(y)
                            .and_then(|d| smt::udivmod_pow2(x, d, w))
                        {
                            return Val::Sym(
                                match op {
                                    BinOp::Div => q,
                                    _ => r,
                                },
                                sign,
                            );
                        }
                    }
                    match (signed, op) {
                        (Some(true), BinOp::Div) => smt::sdiv(x, y),
                        (Some(true), BinOp::Rem) => smt::srem(x, y),
                        (Some(false), BinOp::Div) => smt::udiv(x, y),
                        (Some(false), BinOp::Rem) => smt::urem(x, y),
                        // The arm is reached only for `Div`/`Rem` (the outer
                        // `match op` selects it), so `None` is the only other
                        // case and it is a refusal.
                        (None, _) => return Val::Unknown,
                        _ => return Val::Unknown,
                    }
                }
                // A *variable* shift amount is a barrel shifter (see
                // `smt::shift_var`). rustc guards it with `assert(n < w)`
                // immediately before, so the amount is in range on every path that
                // reaches here. A constant amount keeps the cheap `Op::Shl` path,
                // which is also what makes `x << 3` prove without any guard at all.
                BinOp::Shl | BinOp::Shr => {
                    let Some(w) = width else { return Val::Unknown };
                    // `Shr` is arithmetic on a signed operand and logical on an
                    // unsigned one; an unprinted sign is a refusal, because the
                    // two differ for every negative value.
                    let Some(signed) = signed else { return Val::Unknown };
                    // `evaluate` with no assignment is `Some(k)` for any term that
                    // folds to a constant -- `x >> 1 + 1` reaches here as an add of
                    // two constants -- and `None` for a symbolic amount. Using the
                    // raw-literal `const_of` here classified a folded constant as
                    // symbolic, so the body built a barrel shifter for an amount
                    // rustc knows at compile time and the engine could not decide
                    // the query. A symbolic amount still takes `shift_var` below.
                    match smt::evaluate(y, |_| None) {
                        // rustc's guard says `k < w`; a constant outside that range
                        // is a compile error, so this is defensive only.
                        Some(k) if k < w as u64 => {
                            let v = match shift_kind(op, signed) {
                                smt::Shift::Left => smt::shl(x, k as u32),
                                smt::Shift::LogicalRight => smt::lshr(x, k as u32),
                                smt::Shift::ArithmeticRight => smt::ashr(x, k as u32),
                            };
                            return Val::Sym(v, sign);
                        }
                        Some(_) => return Val::Unknown,
                        None => {
                            return Val::Sym(smt::shift_var(shift_kind(op, signed), x, y), sign);
                        }
                    }
                }
                _ => return Val::Unknown,
            }, sign)
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
/// The signed range of a `w`-bit two's complement value, in `i128` so that the
/// `w == 64` case fits without a special case.
fn signed_range(w: u8) -> (i128, i128) {
    let half = 1i128 << (w - 1);
    (-half, half - 1)
}

/// Reinterpret a `w`-bit two's complement bit pattern as a signed value.
fn as_signed(raw: u64, w: u8) -> i128 {
    if w >= 64 {
        (raw as i64) as i128
    } else {
        let r = raw as i128;
        if r >= (1i128 << (w - 1)) {
            r - (1i128 << w)
        } else {
            r
        }
    }
}

/// `a / b` rounded toward negative infinity, with `b > 0`.
///
/// Rust's `/` truncates toward zero, and the two differ exactly on the negative
/// side, which is the side this whole computation lives on.
fn floor_div(a: i128, b: i128) -> i128 {
    let q = a / b;
    if a % b != 0 && (a < 0) != (b < 0) {
        q - 1
    } else {
        q
    }
}

/// `a / b` rounded toward positive infinity, with `b > 0`.
fn ceil_div(a: i128, b: i128) -> i128 {
    let q = a / b;
    if a % b != 0 && (a < 0) == (b < 0) {
        q + 1
    } else {
        q
    }
}

/// Whether a *signed* `v * c` wraps at width `w`, for a constant `c`.
///
/// `x * c` is monotone in `x` on each side of zero, so the exact product leaves the
/// `w`-bit signed range on a *prefix* `x < lo` or a *suffix* `x > hi`. Both bounds are
/// a division of the range end by `c` rounded one way or the other, computed exactly
/// in `i128`.
///
/// That is the whole point of the construction: **nothing here needs the product**,
/// only the two bounds, so it works at `w == 64` where the general path has no wider
/// width to compute the product in and refuses. The general path's comment says the
/// gap is deliberate because a weaker predicate there would be worse than a refusal;
/// this is not weaker, it is exact -- `x * c` is inside the range exactly when `x` is
/// between the bounds -- which is why it is worth having rather than a compromise.
///
/// `c == 0` is the one constant the formula cannot take: the bounds are a division by
/// `c`, and it is the only one that would divide by zero. `c == 1` is a cheap early
/// return and the formula agrees with it anyway.
///
/// `c == -1` is deliberately *not* in the set, which is the one place this construction
/// is easy to get wrong by hand. `-1 * MIN` is `2^(w-1)`, and the largest signed value is
/// `2^(w-1) - 1` -- so multiplying by minus one *does* overflow, at exactly `MIN`. (It is
/// easy to say instead that `MIN * -1` "wraps back to `MIN`", which is true of the
/// *wrapped* result and is precisely the overflow.) An earlier version of this function
/// special-cased `-1` as never wrapping, which was wrong and is caught by
/// `a_signed_constant_multiply_overflow_is_exact` at `2-bit -2 * -1`.
fn signed_mul_wraps_at(v: Var, c: i128, w: u8) -> Pred {
    if c == 0 || c == 1 {
        return smt::truth(false);
    }
    let (mn, mx) = signed_range(w);
    // For `c > 0` the product leaves low when `x * c < mn` and high when `x * c > mx`,
    // so the bounds are `mn / c` rounded up and `mx / c` rounded down.
    //
    // For `c < 0` the product is decreasing, and the two ends swap: `x` below
    // `floor(mn / |c|) + 1` gives a product *above* `mx`, and `x` above `2^(w-1) / |c|`
    // gives one *below* `mn`. Getting the swap right is the whole difficulty of the
    // negative case, and it is checked against brute force in the test below.
    let (lo, hi) = if c > 0 {
        (ceil_div(mn, c), mx / c)
    } else {
        let d = -c;
        (floor_div(mn, d) + 1, (1i128 << (w - 1)) / d)
    };
    let mask = if w >= 64 { u64::MAX } else { (1u64 << w) - 1 };
    let mut wraps = smt::truth(false);
    // A bound outside the range describes no `x` at all, so the guard is dropped
    // rather than built: `slt(x, MIN)` would be a constant `false` term, and a
    // constant term in a predicate is noise the diagram does not need.
    if lo > mn {
        wraps = smt::or(wraps, smt::slt(v, smt::word((lo as u64) & mask, w)));
    }
    if hi < mx {
        wraps = smt::or(wraps, smt::sgt(v, smt::word((hi as u64) & mask, w)));
    }
    wraps
}

fn overflow_pred(op: BinOp, a: Val, b: Val, w: u8) -> Option<Pred> {
    // The sign is the operand's, read from the operand, for the same reason
    // `eval_binary` does: a wrong sign here is a wrong overflow predicate, and an
    // overflow predicate that is too weak is an overflow the tool calls safe.
    let (x, y, signed) = match (a, b) {
        (Val::Sym(x, sx), Val::Sym(y, _)) => (x, y, sx.known()?),
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
        // The two signs need different tests, and only the signed one widens.
        // Unsigned `x * y` wraps exactly when `y != 0 && x > MAX / y`, which is a
        // division and needs no wide product at all -- see the arm below. The
        // *signed* predicate is about the sign-extended product, and there is no
        // division form that is exact for every combination of the three signs, so
        // it is computed by widening: `smt::truncate` zero-extends when the target
        // width is larger, so the operands are widened to `2w`, multiplied exactly
        // there, and compared with the sign-extension of the wrapped result. Either
        // way the test is exact rather than a sufficient condition, which matters
        // because a too-weak predicate here would make the `assert` look
        // dischargeable and report an overflowing function as panic-free.
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
            // Both operands constant: the product is a literal, so the overflow
            // is a literal too. This arm is reachable only once an argument can
            // be pinned to a constant by its precondition (`a == 3` with the body
            // `a * 2`), which makes the *other* operand constant as well; rustc
            // folds a genuinely constant body before the frontend sees it. Without
            // this arm the pair fell through to the general path below, which has
            // no sound predicate at `w == 64` and returned `None`, so a query whose
            // every input was known came back `incomplete`.
            let both = match (smt::evaluate(x, |_| None), smt::evaluate(y, |_| None)) {
                (Some(xr), Some(yr)) => Some((xr, yr)),
                _ => None,
            };
            if let Some((xr, yr)) = both {
                let wraps = if signed {
                    let p = as_signed(xr, w) * as_signed(yr, w);
                    let (mn, mx) = signed_range(w);
                    p < mn || p > mx
                } else {
                    let p = (xr as u128) * (yr as u128);
                    let max = if w >= 64 { u64::MAX as u128 } else { (1u128 << w) - 1 };
                    p > max
                };
                return Some(smt::truth(wraps));
            }
            // A *constant* operand makes the test exact and cheap: `x * c` wraps,
            // for unsigned operands, exactly when `x > MAX / c`, and `MAX / c` is a
            // compile-time constant, so the whole predicate is one comparison --
            // no divider and no `2w`-bit multiplier. `i * 4` -- an index scaled by
            // an element size -- is the common shape.
            //
            // Unsigned only. The signed case has one case per combination of the
            // three signs, and a predicate that is too weak there is a false proof
            // rather than a refusal, so it takes `signed_mul_wraps_at` rather than
            // this comparison.
            let const_side = match (smt::evaluate(x, |_| None), smt::evaluate(y, |_| None)) {
                // `(v, k)`: the non-constant operand and the constant one.
                (Some(_), None) => Some((y, x)),
                (None, Some(_)) => Some((x, y)),
                _ => None,
            };
            if let Some((v, k)) = const_side {
                let raw = smt::evaluate(k, |_| None).expect("the constant side, just matched");
                if !signed {
                    let max = if w >= 64 { u64::MAX } else { (1u64 << w) - 1 };
                    // `c <= 1` is both cases where `MAX / c + 1` would not fit in
                    // `w` bits: `c == 0` never wraps, and `c == 1` cannot exceed
                    // `MAX`. The predicate is the sound one for every other `c`.
                    return Some(if raw <= 1 {
                        smt::truth(false)
                    } else {
                        smt::uge_const(v, max / raw + 1)
                    });
                }
                // Signed, and the same idea with a range that has two ends. This is
                // the case the general path below cannot reach at `w == 64`, and the
                // reason a scaled index in signed code stayed `incomplete`.
                return Some(signed_mul_wraps_at(v, as_signed(raw, w), w));
            }
            // Non-constant operands, unsigned. `x * y` wraps exactly when
            // `y != 0 && x > MAX / y`, and the division is *exact* rather than
            // sufficient: for `y != 0`, `x * y > MAX` iff `x > floor(MAX / y)`, and
            // `y == 0` can never wrap. No `2w`-bit product is built, so this costs
            // the divider the engine already has rather than the multiplier that is
            // the BDD scaling wall -- and it works at `w == 64`, where there is no
            // width left to widen to and the widened test below cannot exist at all.
            //
            // The shape is deliberately the one the guard in the saturation idiom is
            // written in (`if b != 0 && a > MAX / b`), in the same operand order, so
            // the two terms are structurally identical. That is what lets the boolean
            // fold in `smt::bin_bool` collapse `guard && !guard` to `false` without
            // ever blasting the divider: the difference between a verdict and
            // `Unknown` for a `u16` saturating multiply, whose guard is exactly this
            // predicate.
            if !signed {
                let max = if w >= 64 { u64::MAX } else { (1u64 << w) - 1 };
                let nonzero = smt::not(smt::eq(y, smt::word(0, w)));
                let over = smt::ult(smt::udiv(smt::word(max, w), y), x);
                return Some(smt::and(nonzero, over));
            }
            let wide = w.saturating_mul(2).min(64);
            if wide <= w {
                // Signed at the widest supported width: the sign-extended product
                // needs `2w` bits and there is nowhere to put them, so no sound
                // predicate is available.
                return None;
            }
            // Signed, non-constant. The widened product is a BDD-hostile shape -- a
            // `2w`-bit multiplier is the scaling wall this crate documents -- so past
            // 16 bits the query is not worth posing. A verifier that declines is
            // better than one that hangs, and a *weaker* predicate here would be worse
            // than either, because it would make an overflowing function look
            // panic-free. (An unsigned operand no longer takes this path: the exact
            // division test above replaces the widening there.)
            if wide > 16 {
                return None;
            }
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

    /// The signedness a `Val` is *built* with comes from the operand's own type.
    ///
    /// This is the invariant the whole refactor exists for. The sign used to be a
    /// `bool` threaded alongside the value, and the two false proofs both came
    /// from a site that dropped it: `const 0_i8` read as unsigned made `0 < a` an
    /// unsigned test (so `i8::MIN` read as positive), and a signed source cast
    /// without its sign zero-filled `-1i8 as i16` to `255`. Here the sign is a
    /// field of `Val::Sym`, and this test pins that the *only* place a `Val` is
    /// made from an `Operand` -- `operand` -- reads it from the operand's type:
    /// a constant's suffix, a place's declared type, and a projection's element
    /// type rather than its container's.
    #[test]
    fn a_vals_sign_comes_from_the_operands_type() {
        let mut env = Env::new();
        // A constant's suffix is its type: `const 0_i8` is signed, `const 0_u8`
        // is not.
        let sign_of = |env: &mut Env, o: &Operand| match operand(env, o) {
            Val::Sym(_, s) => s,
            other => panic!("expected a bit-vector, got {other:?}"),
        };
        assert_eq!(
            sign_of(&mut env, &Operand::Const(Const::UInt(0, Some(Ty::I8)))),
            Sign::Signed
        );
        assert_eq!(
            sign_of(&mut env, &Operand::Const(Const::UInt(0, Some(Ty::U8)))),
            Sign::Unsigned
        );
        // A suffix-less constant carries no width *and* no sign, so it is
        // `Val::Unknown` outright -- there is nothing to read a signedness from,
        // which is what keeps the false-proof default from coming back.
        assert!(matches!(
            operand(&mut env, &Operand::Const(Const::UInt(0, None))),
            Val::Unknown
        ));
        // A place read returns the value that was *stored* for the local, so the
        // sign is the one the seeding site gave it. This is the path an argument
        // or an array element takes, and it is where a missing sign would have
        // been invisible before: `env.locals` held a bare `Var`.
        env.locals.insert(0, Val::Sym(smt::var(8), Sign::Unsigned));
        env.locals.insert(1, Val::Sym(smt::var(8), Sign::Signed));
        assert_eq!(sign_of(&mut env, &Operand::Copy(Place::new(0))), Sign::Unsigned);
        assert_eq!(sign_of(&mut env, &Operand::Copy(Place::new(1))), Sign::Signed);
    }

    /// A relational test on a value whose sign the dump did not print is
    /// *refused*, not read as unsigned.
    ///
    /// This is the regression guard for the `0 < a` false proof. `Lt` on two
    /// `Sign::Unknown` operands must be `Val::Unknown`, which the caller reports
    /// as an unmodelled path, rather than `smt::ult`, which would call
    /// `i8::MIN` the largest value and prove the wrong branch.
    #[test]
    fn a_comparison_on_an_unprinted_sign_is_refused() {
        let unknown = Val::Sym(smt::var(8), Sign::Unknown);
        let v = eval_binary(BinOp::Lt, unknown, unknown, Some(8));
        assert!(matches!(v, Val::Unknown), "expected a refusal, got {v:?}");
        // The equality forms do not read the sign, so they still answer.
        assert!(matches!(eval_binary(BinOp::Eq, unknown, unknown, Some(8)), Val::Bool(_)));
        // Division and shifts read it too, and refuse the same way.
        assert!(matches!(
            eval_binary(BinOp::Div, unknown, unknown, Some(8)),
            Val::Unknown
        ));
        assert!(matches!(
            eval_binary(BinOp::Shr, unknown, unknown, Some(8)),
            Val::Unknown
        ));
        // An *unsigned* pair is answered, so the refusal is specific to the
        // missing sign rather than to the operator.
        let unsigned = Val::Sym(smt::var(8), Sign::Unsigned);
        assert!(matches!(
            eval_binary(BinOp::Lt, unsigned, unsigned, Some(8)),
            Val::Bool(_)
        ));
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

    /// The same loop, but the counter is advanced by a *call* rather than by an
    /// `Add` statement.
    ///
    /// This is the shape `rustc` emits for `i = i.wrapping_add(1)`: the write to
    /// `i` is the `Call` terminator's destination, not a `Stmt::Assign`. The
    /// havoc set is built from the loop body's writes, and reading only
    /// `Stmt::Assign` missed the call destination -- so `i` kept the value it had
    /// on the first entry, the induction step was checked against that one value,
    /// and the same false postcondition as above came back `Verified`.
    ///
    /// The fixture keeps the counter on `_2` (not `_0`) so the call destination is
    /// the only write to it inside the loop, which is what isolates the hole: with
    /// `Add` instead of the call, `an_invariant_too_weak_for_the_postcondition_is_not_a_proof`
    /// already covers the statement form.
    const COUNT_VIA_CALL_MIR: &str = r#"
fn count_via_call(_1: u8) -> u8 {
    debug n => _1;
    let mut _0: u8;
    let mut _2: u8;
    let mut _3: bool;
    let mut _4: u8;
    scope 1 {
        debug i => _2;
    }

    bb0: {
        _2 = const 0_u8;
        goto -> bb1;
    }

    bb1: {
        _4 = copy _2;
        _3 = Lt(move _4, copy _1);
        switchInt(move _3) -> [0: bb3, otherwise: bb2];
    }

    bb2: {
        _2 = core::num::<impl u8>::wrapping_add(move _2, const 1_u8) -> [return: bb4, unwind continue];
    }

    bb4: {
        goto -> bb1;
    }

    bb3: {
        _0 = copy _2;
        return;
    }
}
"#;

    /// A counter written only by a call must still be havoced at the loop header.
    #[test]
    fn a_call_written_counter_is_havoced_like_an_assigned_one() {
        let out = verify_with(
            COUNT_VIA_CALL_MIR,
            "count_via_call",
            "/// requires: n <= 4\n/// invariant: i <= n\n/// ensures: ret == 0\n",
        );
        assert!(
            !matches!(out, crate::mir::verify::FnOutcome::Verified { .. }),
            "a call-written counter must not escape the havoc, got {out:?}"
        );
    }

    /// And the sound direction: the same loop with the invariant that actually
    /// decides it must still verify, so the fix to the havoc set did not simply
    /// make every call-carrying loop unknown.
    #[test]
    fn a_call_written_counter_is_still_decidable() {
        let out = verify_with(
            COUNT_VIA_CALL_MIR,
            "count_via_call",
            "/// requires: n <= 4\n/// invariant: i <= n\n/// ensures: ret == n\n",
        );
        assert!(
            matches!(out, crate::mir::verify::FnOutcome::Verified { .. }),
            "the call-written loop should still be decided by its invariant, got {out:?}"
        );
    }

    /// A user function that happens to be named `wrapping_add` must be *inlined*,
    /// not modelled as the `core` intrinsic.
    ///
    /// `intrinsics::classify` matches the method name after the last `::`, so a
    /// plain `wrapping_add` classified as the intrinsic. Dispatching on the
    /// intrinsic *before* the same-dump lookup then ignored the user's body
    /// entirely: this `wrapping_add` returns `0` whatever it is given, but the
    /// caller's `ret == 3` for `a == 1, b == 2` came back `Verified` -- a proof of
    /// a false statement, which is the one failure this crate exists to prevent.
    const SHADOWED_INTRINSIC_MIR: &str = r#"
fn wrapping_add(_1: u8, _2: u8) -> u8 {
    let mut _0: u8;
    bb0: {
        _0 = const 0_u8;
        return;
    }
}

fn caller(_1: u8, _2: u8) -> u8 {
    debug a => _1;
    debug b => _2;
    let mut _0: u8;
    bb0: {
        _0 = wrapping_add(copy _1, copy _2) -> [return: bb1, unwind continue];
    }
    bb1: {
        return;
    }
}
"#;

    #[test]
    fn a_user_function_named_like_an_intrinsic_is_inlined_not_modelled() {
        let out = verify_with(
            SHADOWED_INTRINSIC_MIR,
            "caller",
            "/// requires: a == 1 && b == 2\n/// ensures: ret == 3\n",
        );
        assert!(
            !matches!(out, crate::mir::verify::FnOutcome::Verified { .. }),
            "a user `wrapping_add` returning 0 must not be modelled as `a + b`, got {out:?}"
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

    /// The same-dump helper the loop below calls, so the *inliner* is selected
    /// rather than the `core` intrinsic. Its body is `a + b`, the wrapped sum for
    /// a `u8`, but the point is only that the call is inlined.
    const HELPER_CALL_MIR: &str = r#"
fn wrapping_add(_1: u8, _2: u8) -> u8 {
    debug a => _1;
    debug b => _2;
    let mut _0: u8;
    bb0: {
        _0 = Add(copy _1, copy _2);
        return;
    }
}

fn count_via_helper(_1: u8) -> u8 {
    debug n => _1;
    let mut _0: u8;
    let mut _2: u8;
    let mut _3: bool;
    let mut _4: u8;
    scope 1 {
        debug i => _2;
    }

    bb0: {
        _2 = const 0_u8;
        goto -> bb1;
    }

    bb1: {
        _4 = copy _2;
        _3 = Lt(move _4, copy _1);
        switchInt(move _3) -> [0: bb3, otherwise: bb2];
    }

    bb2: {
        _2 = wrapping_add(move _2, const 1_u8) -> [return: bb4, unwind continue];
    }

    bb4: {
        goto -> bb1;
    }

    bb3: {
        _0 = copy _2;
        return;
    }
}
"#;

    /// A loop whose step is a same-dump call must keep its invariant across the
    /// inlined call, so it is decided by the invariant rather than unwound.
    ///
    /// Entering a callee clears `cut` -- the caller's loop invariant says nothing
    /// about the callee's locals -- but the return path used to copy the callee's
    /// (empty) cut into the resumed caller instead of restoring the caller's. The
    /// resumed caller was then inside a loop it had no cut for, so the next edge
    /// into its header was unwound. `n <= 10` needs more iterations than
    /// [`DEFAULT_UNWIND`], so the loop was reported as a cutoff even though its
    /// invariant decides it exactly.
    ///
    /// This is the shape the exact-name lookup now sends a user-defined
    /// `wrapping_add` through, which is why a loop that previously modelled the
    /// call as an intrinsic (and so kept its cut) began to lose it.
    #[test]
    fn an_invariant_survives_an_inlined_call_on_the_loop_edge() {
        let out = verify_with(
            HELPER_CALL_MIR,
            "count_via_helper",
            "/// requires: n <= 10\n/// invariant: i <= n\n/// ensures: ret == n\n",
        );
        assert!(
            matches!(out, crate::mir::verify::FnOutcome::Verified { .. }),
            "the loop should be decided by its invariant across the inlined call, got {out:?}"
        );
    }

    /// And the fix must not *weaken* the check: the same call-carrying loop with
    /// an invariant too weak for the postcondition must still be refuted, so
    /// restoring the cut did not restore a proof that was never there.
    #[test]
    fn an_inlined_call_does_not_rescue_a_weak_invariant() {
        let out = verify_with(
            HELPER_CALL_MIR,
            "count_via_helper",
            "/// requires: n <= 10\n/// invariant: i <= n\n/// ensures: ret == 0\n",
        );
        assert!(
            !matches!(out, crate::mir::verify::FnOutcome::Verified { .. }),
            "a weak invariant must not be rescued by the restored cut, got {out:?}"
        );
    }

    /// The *signed* constant multiply's predicate is exact, two-sided, at every width.
    ///
    /// This is the predicate that closes the `i64` gap, so it is the one that most needs
    /// the two-sided check: a predicate that is too *weak* here does not merely refuse a
    /// proof, it lets an overflowing `assert` discharge and reports an overflowing
    /// function as panic-free. A predicate that is too *strong* refuses safe code, which
    /// is the failure the old `wide > 16` bound was avoiding by refusing everything.
    ///
    /// So the whole domain is enumerated at widths where that is possible, against Rust's
    /// own `checked_mul` -- the oracle is the standard library's idea of overflow, not
    /// this file's. The negative constants are the interesting half: `x * c` is monotone
    /// but *decreasing* for `c < 0`, so the low and high bounds swap ends, and that swap
    /// is where a hand-derived bound goes wrong.
    #[test]
    fn a_signed_constant_multiply_overflow_is_exact() {
        // `true` when the engine's predicate says the multiply wraps. The oracle is
        // `i128`, which holds the exact product of any two values this test uses.
        let wraps = |w: u8, c: i128, v: i128| -> bool {
            smt::with_fresh(|| {
                // The constant has to be built as a `w`-bit bit pattern: `smt::word`
                // rejects a value that does not fit, and a negative constant does not fit
                // as written. Two's complement is the same pattern the frontend produces.
                let mask = if w >= 64 { u64::MAX } else { (1u64 << w) - 1 };
                let x = smt::var(w);
                let y = smt::word((c as u64) & mask, w);
                let p = overflow_pred(
                    BinOp::Mul,
                    Val::Sym(x, Sign::Signed),
                    Val::Sym(y, Sign::Signed),
                    w,
                )
                .expect("a constant multiply must produce a predicate");
                // The predicate is over the fresh variable, so asking whether it holds at
                // this point means substituting the point and evaluating. `v` is negative
                // for some cases, so it goes in as its own `w`-bit pattern too.
                smt::evaluate_pred(p, |_| Some((v as u64) & mask)).expect("predicate is over `x`")
            })
        };

        // Exhaustive where the domain is small enough to enumerate. Both signs of `c`
        // and every value of `x`, so the monotone-decreasing half is covered too.
        for w in [2u8, 3, 4, 5] {
            let half = 1i128 << (w - 1);
            let (mn, mx) = (-half, half - 1);
            for c in mn..=mx {
                for v in mn..=mx {
                    let want = v.checked_mul(c).is_none_or(|p| p < mn || p > mx);
                    assert_eq!(
                        wraps(w, c, v),
                        want,
                        "{w}-bit {v} * {c}: predicate said {} but wrapping is {want}",
                        wraps(w, c, v)
                    );
                }
            }
        }

        // `i64`, the width this predicate exists for and the one that cannot be
        // enumerated. The constants are chosen at the ends of the range and at powers of
        // two, where the bounds land on the edge of the domain; `x` is swept across each
        // constant's own boundary from `i64::MIN` to `i64::MAX`, which is the whole span
        // that matters for that constant.
        for c in [
            2i128,
            3,
            -2,
            -3,
            1 << 31,
            -(1 << 31),
            1 << 62,
            -(1 << 62),
            (1 << 62) - 1,
            i64::MAX as i128,
            i64::MIN as i128,
        ] {
            let (mn, mx) = (i64::MIN as i128, i64::MAX as i128);
            // The *safe* interval `[lo, hi]` -- the `x` whose product with `c` stays in
            // range -- derived here from the true interval, not from the implementation.
            // `x * c` is monotone but decreasing for `c < 0`, so the two ends of the
            // range swap: the low bound comes from `mx` and the high from `mn`. Deriving
            // both from `mn` (as an earlier version did) put the probes on the *negative*
            // side for every negative `c` and never straddled the positive transition at
            // `2^63 / |c|`, which is the boundary the negative arm is most likely to get
            // wrong. The probes below now bracket `lo` and `hi` on both signs.
            let (lo, hi) = if c > 0 {
                (ceil_div(mn, c), floor_div(mx, c))
            } else {
                (ceil_div(mx, c), floor_div(mn, c))
            };
            let probes = [
                mn,
                mn + 1,
                lo - 1,
                lo,
                lo + 1,
                -1,
                0,
                1,
                hi - 1,
                hi,
                hi + 1,
                mx - 1,
                mx,
            ];
            for v in probes {
                let want = v.checked_mul(c).is_none_or(|p| p < mn || p > mx);
                assert_eq!(
                    wraps(64, c, v),
                    want,
                    "64-bit {v} * {c}: predicate said {} but wrapping is {want}",
                    wraps(64, c, v)
                );
            }
        }
    }

    /// The unsigned arm is untouched by the signed one: both signs are asked the same
    /// question and must give different answers where signedness matters.
    ///
    /// `-1` at `i8` is `255u8`, and `255 * 255` wraps *unsigned* (the product is past
    /// `255`) while `-1 * -1` does not wrap *signed*. A predicate that read the bit
    /// pattern without the sign would give one answer to both, so the two are asked
    /// together and required to differ.
    #[test]
    fn the_signed_and_unsigned_arms_are_not_confused() {
        let wraps = |signed: bool, w: u8, c: u64, v: u64| -> bool {
            smt::with_fresh(|| {
                let x = smt::var(w);
                let y = smt::word(c, w);
                let sign = if signed { Sign::Signed } else { Sign::Unsigned };
                let p = overflow_pred(BinOp::Mul, Val::Sym(x, sign), Val::Sym(y, sign), w)
                    .expect("a constant multiply must produce a predicate");
                smt::evaluate_pred(p, |_| Some(v)).expect("predicate is over `x`")
            })
        };
        // `-1 * -1` is `1` in `i8`: no signed overflow. `255 * 255` is `65025`: unsigned
        // overflow at 8 bits.
        assert!(
            !wraps(true, 8, 0xFF, 0xFF),
            "-1 * -1 must not wrap as signed"
        );
        assert!(
            wraps(false, 8, 0xFF, 0xFF),
            "255 * 255 must wrap as unsigned"
        );
        // `127 * -1` is `-127`, representable, while the *same bits* read unsigned are
        // `127 * 255`, far past `255`. A predicate that ignored the sign would answer one
        // of these wrong.
        assert!(!wraps(true, 8, 0xFF, 0x7F), "127 * -1 must not wrap as signed");
        assert!(wraps(false, 8, 0xFF, 0x7F), "127 * 255 must wrap as unsigned");
        // The regression for the minus-one bound: `-1 * MIN` is `2^(w-1)`, one past the
        // largest signed value, so it *does* overflow -- while the same product read as
        // unsigned magnitudes is `128 * 255`, which also overflows but for its own
        // reason. The first version of the predicate called the signed one safe.
        assert!(
            wraps(true, 8, 0xFF, 0x80),
            "MIN * -1 must wrap as signed: 2^(w-1) is not representable"
        );
    }

    /// A multiply with *both* operands constant is decided, and exactly.
    ///
    /// Both operands are literals only when the precondition pins the argument to a
    /// constant (`a == 3` with the body `a * 2`), because rustc folds a genuinely
    /// constant body itself. That shape used to fall through to the general signed
    /// path, which has no sound predicate at `w == 64` and returned `None` -- so the
    /// `assert(!overflow)` that follows was unmodelled and the whole query came back
    /// `incomplete` even though every input was known. The oracle is `i128`, and the
    /// negative constants are the interesting half because the product's sign follows
    /// the *signs*, not the magnitudes.
    #[test]
    fn a_constant_times_a_constant_multiply_is_decided() {
        // `overflow_pred` with both operands literal, at the width `w`.
        let wraps = |signed: bool, w: u8, a: i128, b: i128| -> bool {
            smt::with_fresh(|| {
                let mask = if w >= 64 { u64::MAX } else { (1u64 << w) - 1 };
                let sign = if signed { Sign::Signed } else { Sign::Unsigned };
                let x = smt::word((a as u64) & mask, w);
                let y = smt::word((b as u64) & mask, w);
                let p = overflow_pred(BinOp::Mul, Val::Sym(x, sign), Val::Sym(y, sign), w)
                    .expect("two constant operands must still produce a predicate");
                smt::evaluate_pred(p, |_| None).expect("a constant predicate must be evaluable")
            })
        };

        // Exhaustive at the small widths, both signs: every pair of values, against the
        // true product. This is what pins the arms rather than a hand-picked few.
        for w in [2u8, 3, 4, 5] {
            let half = 1i128 << (w - 1);
            let (mn, mx) = (-half, half - 1);
            let umax = (1i128 << w) - 1;
            for a in mn..=mx {
                for b in mn..=mx {
                    let want = a.checked_mul(b).is_none_or(|p| p < mn || p > mx);
                    assert_eq!(
                        wraps(true, w, a, b),
                        want,
                        "{w}-bit signed {a} * {b}: said {} but wrapping is {want}",
                        wraps(true, w, a, b)
                    );
                }
            }
            for a in 0..=umax {
                for b in 0..=umax {
                    let want = (a as u128) * (b as u128) > umax as u128;
                    assert_eq!(
                        wraps(false, w, a, b),
                        want,
                        "{w}-bit unsigned {a} * {b}: said {} but wrapping is {want}",
                        wraps(false, w, a, b)
                    );
                }
            }
        }

        // `i64`, where the bug bit. The pairs straddle the representable boundary:
        // `MIN * -1` is one past `MAX` and must wrap; `MIN * 1` and `-1 * -1` do not.
        for (a, b) in [
            (1i128, 1i128),
            (i64::MAX as i128, 1),
            (i64::MAX as i128, 2),
            (i64::MIN as i128, 1),
            (i64::MIN as i128, -1),
            (-1, -1),
            (-1, 1),
            (1 << 31, 1 << 31),
            (1 << 31, -(1 << 31)),
            (i64::MIN as i128, i64::MIN as i128),
            (0, i64::MIN as i128),
        ] {
            let (mn, mx) = (i64::MIN as i128, i64::MAX as i128);
            let want = a.checked_mul(b).is_none_or(|p| p < mn || p > mx);
            assert_eq!(
                wraps(true, 64, a, b),
                want,
                "64-bit signed {a} * {b}: said {} but wrapping is {want}",
                wraps(true, 64, a, b)
            );
        }
    }

    /// `overflow_pred` is *exact* for a constant multiply, checked exhaustively at
    /// a width small enough to enumerate and at the real boundary of a wide one.
    ///
    /// The predicate is one comparison against `MAX / c`, and the reason it is
    /// worth a test of its own is the failure mode: a predicate that is merely
    /// *sufficient* would still refuse the safe cases, and a predicate that is too
    /// *weak* would let rustc's `assert(!overflow)` discharge on a program that
    /// overflows, reporting a false panic-free result. So the check is two-sided --
    /// it must fire on every wrapping input and on no other.
    ///
    /// At `u8` the whole domain is 256 values, so "no other" is checked rather than
    /// sampled. `u32` cannot be enumerated, so the two values straddling the
    /// boundary `ceil(2^32 / c) - 1` are used, which is where a fencepost error
    /// lives.
    #[test]
    fn a_constant_multiply_overflow_is_exact() {
        // `true` when the engine's predicate says the multiply wraps.
        let wraps = |w: u8, c: u64, v: u64| -> bool {
            smt::with_fresh(|| {
                // `x` must be *symbolic*: with both operands constant the
                // constant-operand path is not taken at all, and the test would
                // exercise the widening path it is meant to be independent of.
                let x = smt::var(w);
                let y = smt::word(c, w);
                let p = overflow_pred(
                    BinOp::Mul,
                    Val::Sym(x, Sign::Unsigned),
                    Val::Sym(y, Sign::Unsigned),
                    w,
                )
                .expect("a constant multiply must produce a predicate");
                // The predicate is over fresh variables, so asking whether it holds
                // for this one point means substituting the point and evaluating.
                smt::evaluate_pred(p, |_| Some(v)).expect("the predicate is over `x`")
            })
        };

        // Exhaustive at `u8`: every value against every constant that can wrap.
        for w in [4u8, 8] {
            let max = (1u64 << w) - 1;
            for c in 0..=max {
                for v in 0..=max {
                    let want = v.checked_mul(c).is_none_or(|p| p > max);
                    assert_eq!(
                        wraps(w, c, v),
                        want,
                        "{w}-bit {v} * {c}: predicate said {} but wrapping is {want}",
                        wraps(w, c, v)
                    );
                }
            }
        }

        // The boundary of a wide width, where a fencepost error would sit.
        for c in [2u64, 3, 5, 7, 8, 1000] {
            let boundary = (1u64 << 32).div_ceil(c); // ceil(2^32 / c)
            for v in [boundary - 1, boundary] {
                let want = (v as u128) * (c as u128) > (u32::MAX as u128);
                assert_eq!(wraps(32, c, v), want, "32-bit {v} * {c}");
            }
        }

        // Multiplying by zero and by one never wraps, at any width -- the two cases
        // that are decided by a constant `false` rather than by a comparison, and so
        // the two that would panic if `MAX / c` were computed for them.
        for w in [1u8, 8, 16, 32, 64] {
            let max = if w >= 64 { u64::MAX } else { (1u64 << w) - 1 };
            for c in [0u64, 1] {
                for v in [0u64, 1, max] {
                    assert!(!wraps(w, c, v), "{w}-bit {v} * {c} must not wrap");
                }
            }
        }
    }

    /// The name-shape rules a call name is resolved by, on the shapes rustc
    /// actually prints.
    ///
    /// These are pure string rules, so they are pinned here rather than only
    /// through a `rustc` run: the resolver is what stands between a call and the
    /// body it is answered from, and answering it from the wrong body is a false
    /// proof, not a lost one. The shapes below are the ones measured from a real
    /// `--emit=mir` dump.
    #[test]
    fn call_names_resolve_to_the_right_body() {
        // `base_type` strips the wrapper rustc prints on a definition and the
        // generics it prints on a call, and takes the last path segment.
        assert_eq!(base_type("Vec2"), "Vec2");
        assert_eq!(base_type("G::<T>"), "G");
        assert_eq!(base_type("<S2 as T2>"), "S2");
        assert_eq!(base_type("core::num::<impl u8>"), "u8");
        assert_eq!(base_type("&Vec2"), "&Vec2");

        // `call_type` is the type a method is called on.
        assert_eq!(call_type("Vec2::push").as_deref(), Some("Vec2"));
        assert_eq!(call_type("G::<T>::walk").as_deref(), Some("G"));
        assert_eq!(call_type("<S as T>::m").as_deref(), Some("S"));
        assert_eq!(call_type("free_fn"), None, "a bare name has no type segment");

        // An intrinsic call keeps its `<impl` projection, which marks it external.
        assert_eq!(call_type("core::num::<impl u8>::wrapping_add").as_deref(), Some("u8"));
    }
}

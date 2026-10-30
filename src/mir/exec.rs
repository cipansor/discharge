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
    /// Values addressed by an index, with a length: slice arguments (`&[T]`) and
    /// array arguments (`[T; N]`), keyed by the local the argument lives in.
    ///
    /// A slice has no length in its type, so its length is a fresh symbolic input
    /// -- it is whatever the caller passed. An array's length is the constant in
    /// its type. Either way the length is a *word* here, and the elements are
    /// distinct inputs per index, so `xs[0]` and `xs[1]` are two values and
    /// `xs[0] == xs[1]` is not provable; see `Indexed::elems`.
    indexed: BTreeMap<u32, Indexed>,
    /// Locals whose indexed store has been written since this `Env` was built.
    ///
    /// A call hands a callee a *copy* of an indexed argument's state. For a
    /// by-value `[T; N]` the callee's writes are its own and die with its frame,
    /// so the caller's store is untouched. For a `&mut [T]`/`&mut [T; N]` the
    /// callee writes the caller's storage, which this frontend does not model,
    /// so the caller's elements must become unknown when it returns -- a stale
    /// element there is a wrong value, not a missing one. This set is how the
    /// return path learns that a callee wrote.
    indexed_writes: BTreeSet<u32>,
    /// The program's enum layouts, so a variant *construction* constant
    /// (`Mode::Idle`) resolves to its discriminant.
    ///
    /// Carried by value rather than borrowed: the map is small, and a borrow
    /// would put a lifetime on `Env` for every call site of `operand` -- a table
    /// read once per constant is not worth that.
    enums: BTreeMap<String, EnumLayout>,
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
            fields: BTreeMap::new(),
            payloads: BTreeMap::new(),
            discriminants: BTreeMap::new(),
            deref_ok: BTreeMap::new(),
            addressed: BTreeMap::new(),
            indexed: BTreeMap::new(),
            indexed_writes: BTreeSet::new(),
            enums: BTreeMap::new(),
            tag_widths: BTreeMap::new(),
        }
    }

    /// Same as [`Env::new`], with the program's enum layouts attached.
    fn with_enums(enums: &BTreeMap<String, EnumLayout>) -> Env {
        Env { enums: enums.clone(), ..Env::new() }
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
        let any = !fields.is_empty()
            || !elems.is_empty()
            || !payloads.is_empty()
            || disc.is_some()
            || indexed.is_some();
        self.forget_parts(dst);
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
                    None => *self.elems.get(&(p.local, *k)).unwrap_or(&Val::Unknown),
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
                            None => *self.elems.get(&(p.local, k)).unwrap_or(&Val::Unknown),
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
            self.locals.insert(p.local, v);
            return;
        }
        match p.proj.as_slice() {
            [Proj::Field(i)] => {
                self.fields.insert((p.local, *i), v);
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
            [Proj::Downcast(variant), Proj::Field(0)] | [Proj::Downcast(variant)] => {
                self.payloads.insert((p.local, *variant), (v, 0));
            }
            // A shape the arms above do not cover. A nested projection would
            // need a place tree, and `*a = v` (a whole-store write through a
            // `&mut [T; N]`) would need a new store, so both are dropped. For an
            // indexed local that leaves the store describing a value that is no
            // longer there, so it is poisoned rather than left stale -- and
            // `poison_elems` records the write, so a `&mut` caller sees the
            // poison rather than its pre-call elements.
            _ => {
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
    fn forget_parts(&mut self, local: u32) {
        self.fields.retain(|(l, _), _| *l != local);
        self.elems.retain(|(l, _), _| *l != local);
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
        self.indexed_writes.insert(local);
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
        self.indexed_writes.insert(local);
        match self.indexed.get_mut(&local) {
            Some(s) => s.poisoned = true,
            // A literal array written through a symbolic subscript: the whole
            // literal is unmodelled now, so its elements are dropped rather than
            // left stale.
            None => self.elems.retain(|(l, _), _| *l != local),
        }
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
    /// `(caller local, callee local)` for each indexed argument the caller
    /// handed over through a reference (`&[T]` / `&mut [T]`).
    ///
    /// The frontend models `&T` as its referent, so these two locals denote the
    /// same storage and the callee's post-state is copied back to the caller's
    /// local on return. A by-value argument is deliberately *not* in this list:
    /// its writes must stay in the callee's frame, or `let b = f(a)` would
    /// mutate `a` and a caller contract about `a` would be checked against the
    /// wrong value.
    by_ref_indexed: Vec<(u32, u32)>,
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

    let mut env = Env::with_enums(&prog.enums);
    for &l in &f.arg_locals {
        let ty = f.ty_of(l).cloned().unwrap_or(Ty::Other("?".into()));
        let v = match ty.width() {
            Some(1) => Val::Bool(smt::var_named(l, 1).eq_val(1)),
            // The argument's own type declares its sign, so the value carries it
            // rather than a later site having to look it up.
            Some(w) => Val::Sym(smt::var_named(l, w), Sign::of(&ty)),
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
        env.fields.insert((local, field), Val::Sym(v, Sign::of_bool(signed)));
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
            s.elems.insert(index, v);
        }
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

    let mut work = vec![State {
        frame: Frame {
            func: root,
            ret_target: usize::MAX,
            ret_dest: None,
            saved_env: None,
            saved_cut: None,
            by_ref_indexed: Vec::new(),
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

fn run_state<F>(prog: &MirProgram, mut st: State, post: &Option<F>, report: &mut MirReport, work: &mut Vec<State>)
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
                    for (cl, cal) in &caller.by_ref_indexed {
                        if let Some(s) = st.env.indexed.get(cal) {
                            env.indexed.insert(*cl, s.clone());
                        }
                    }
                    if let Some(dest) = &caller.ret_dest {
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
                verdict: smt::find_model(st.path),
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
                    advance(prog, next, *target, report, work);
                    return;
                }
            }
            if st.depth + 1 >= DEFAULT_INLINE_DEPTH {
                report.unknown_paths.push(format!("call depth limit reached at `{name}`"));
                return;
            }
            // Only same-dump calls can be inlined. Assuming a return value for
            // anything else would be assuming the conclusion, so it is unknown. The
            // suffix match is the fallback for a name rustc prints with a path prefix
            // (`module::f`); an exact match above already took the unambiguous case.
            let inline_idx = exact.or_else(|| {
                prog.fns
                    .iter()
                    .position(|g| g.name.rsplit("::").next() == Some(name.as_str()))
            });
            let Some(idx) = inline_idx else {
                report.unknown_paths.push(format!("call to unmodelled function `{name}`"));
                return;
            };
            let callee_fn = &prog.fns[idx];
            let Some(b0) = callee_fn.blocks.first() else {
                report.unknown_paths.push(format!("callee `{name}` has no body"));
                return;
            };
            let mut env = Env::with_enums(&prog.enums);
            // Which caller locals were handed over through a reference, so the
            // return path knows whose store the callee's post-state belongs to.
            let mut by_ref_indexed: Vec<(u32, u32)> = Vec::new();
            for (i, a) in args.iter().enumerate() {
                let v = operand(&mut st.env, a);
                let Some(&l) = callee_fn.arg_locals.get(i) else { continue };
                env.locals.insert(l, v);
                // Carry the indexed argument's state into the callee. Without
                // this the callee's `a[0]` and `a.len()` have no store to read, so
                // a helper that indexes its parameter cannot be modelled at all
                // and a caller's contract about the result stays unproved.
                //
                // The store is *cloned*, never shared: the callee must not be able
                // to write the caller's copy directly, or a by-value argument would
                // behave like a reference. Only a reference argument's post-state
                // is copied back (see the return path).
                let Place { local: cl, proj } = match a {
                    Operand::Copy(p) | Operand::Move(p) => p,
                    Operand::Const(_) => continue,
                };
                if !proj.is_empty() {
                    continue;
                }
                let Some(store) = st.env.indexed.get(cl).cloned() else { continue };
                env.indexed.insert(l, store);
                if arg_is_indexed_ref(callee_fn, i) {
                    by_ref_indexed.push((*cl, l));
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
                by_ref_indexed: by_ref_indexed.clone(),
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
                    by_ref_indexed: Vec::new(),
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
            Const::Other(_) => Val::Unknown,
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
                env.set(&Place { local: dest.local, proj: vec![Proj::Field(i as u32)] }, v);
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
            Val::Unknown
        }
        Rvalue::Len(_) | Rvalue::Unknown(_) => Val::Unknown,
        // `PtrMetadata(_1)` — for a `&[T]` this is the slice's length. Modelled
        // only when the local is a slice the frontend bound a length for; any
        // other pointer has metadata this model cannot express, and answering
        // `Unknown` there is what keeps an invented length out of a proof.
        Rvalue::PtrMetadata(p) => {
            // The place is followed to its pointee first, so `_2 = _3 as &[u8]`
            // after `_3 = &_1` names `_1` here -- the place whose length is
            // actually wanted.
            let p = env.pointee(p);
            match env.indexed.get(&p.local) {
                // A slice argument, whose length is a symbolic input.
                // A length is a `usize`, so it is unsigned.
                Some(s) => Val::Sym(s.len, Sign::Unsigned),
                // An *array* has its length in its type, not in `indexed`, so an
                // unsized `&[T; N]` would otherwise read unknown. The length is
                // the type's constant -- not a guess, and not a fresh variable:
                // `[T; N]` coerces to a slice of exactly `N`, so the two are the
                // same number and a contract that writes `a.len() == 4` on an
                // `a: [u8; 4]` has something to agree with.
                None => match type_of_place(f, &p) {
                    Some(Ty::Array(_, n)) => Val::Sym(smt::word(n, USIZE_WIDTH), Sign::Unsigned),
                    _ => Val::Unknown,
                },
            }
        }
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
fn arg_is_indexed_ref(f: &MirFn, i: usize) -> bool {
    let Some(&l) = f.arg_locals.get(i) else { return false };
    matches!(f.ty_of(l), Some(Ty::Ref(inner)) if matches!(**inner, Ty::Slice(_) | Ty::Array(..)))
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
}

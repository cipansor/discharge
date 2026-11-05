//! An SMT decision procedure that lives *inside* the compiled artifact.
//!
//! This is the piece that lets Rust code carry its own proof engine, the way a
//! SPARK/Ada project carries `gnatprove`: formulas are built as bit-vector
//! terms, then bit-blasted into a Reduced Ordered Binary Decision Diagram
//! (ROBDD). A BDD is a canonical form, so two formulas are equivalent exactly
//! when their diagrams are the *same node*. That single property gives us, with
//! no external solver and no `std`:
//!
//! * [`prove`]         -> the formula holds for every input (diagram is `true`)
//! * [`find_model`]    -> a concrete input satisfying the formula, or `Unsat`
//! * [`prove_implies`] -> `pre => post` holds for every input
//!
//! Everything is heap-free: nodes live in a fixed-capacity arena, so a
//! safety-critical build gets no allocator, no OOM-abort surprise, and a
//! compile-time-bounded worst-case memory ([`ARENA_BYTES`]).
//!
//! # Honesty about scale
//!
//! BDDs are canonical but not a silver bullet. Boolean *equality* of two 32-bit
//! multipliers can blow up (the classic BDD wall). We keep a deterministic node
//! budget and return [`Verdict::Unknown`] rather than lie or loop forever. For
//! the identities that actually appear in safety code (masks, bounds,
//! saturating ops, shifts, fixed-point scaling) the diagrams stay tiny; see the
//! tests and `examples/`.

use core::fmt;
#[cfg(feature = "std")]
use core::cell::RefCell;

/// Node budget for the arena. This is the only tuning knob.
pub const CAP: usize = 1 << 14;

/// Slots in each bit-blaster's memo, rounded to a power of two.
///
/// The blasters walk a term as a tree, but a term built by a fold (`pow`, the divider) is
/// a *DAG*: a shared subterm is re-walked once per path to it, and for a 32-step fold that
/// is 2^32 walks of the same few hundred nodes. The arena never fills, so the existing
/// overflow guard never fires, and the query simply never returns. A memo on the blasted
/// value of each term collapses those paths: the same query drops from more than 10^8
/// visits to a few hundred. 128 slots is enough for the fold terms a single query touches;
/// it is deliberately small because the table lives in the arena (see `Ctx`), which is
/// allocated once and must stay well inside a thread's stack.
const BLAST_MEMO_N: usize = 128;

/// Step budget for one bit-blasting pass, the companion to [`BLAST_MEMO_N`].
///
/// A memo makes the fold walks cheap, but a memo is a cache, not a guarantee: a term shape
/// that evicts its own entries could still recompute. This bounds the *work* directly. When
/// it trips, the pass stops and the query degrades exactly as an arena overflow does -- the
/// BDD pass hands off to the SAT engine, the SAT pass reports `Unknown` -- so the answer
/// stays sound and the call always returns. The value is far above every query in the test
/// corpus (the largest measured pass is a few thousand steps) and far below the 10^8-step
/// blow-up it exists to stop.
pub(crate) const MAX_BLAST_STEPS: u32 = 1 << 22;

/// Step budget for the BDD *apply* during one query, the third of the engine's bounds.
///
/// `MAX_BLAST_STEPS` counts visits to the term DAG, which is where a fold (`pow`, the
/// divider) blows up when it is walked as a tree. But the DAG walk is not the only place
/// that can run away: the BDD `apply2` recurses over the *diagram*, and a boolean function
/// whose BDD is exponentially larger than its formula -- a wide division by a
/// non-power-of-two constant is the shape here -- makes that recursion, not the DAG walk,
/// the unbounded work. Measured on `udiv(x, 15)`: the DAG walk is ~330 steps while `apply2`
/// passes 4 000 000, and with no budget of its own the query never returns.
///
/// The bound is chosen from measurement, not taste. Over both corpus files the largest
/// legitimate query takes **57 191** apply steps (a u64 comparison); the pathological one
/// exceeds 4 000 000. 1 << 19 = 524 288 sits an order of magnitude above every decided
/// query and an order of magnitude below the blow-up, so it never changes a verdict in the
/// corpus while turning a hang into an answer. Because it is *charged per apply* it also
/// bounds the latency: the pathological query returned in about six seconds instead of
/// never (4 194 304 steps, the old pass's implied ceiling, took ~50s).
pub(crate) const MAX_APPLY_STEPS: u32 = 1 << 19;

/// Depth budget for the recursive term walk, the fourth of the engine's bounds.
///
/// The other three budgets count *steps*, and steps are not what a stack overflow is made
/// of. A term walk that is 262 levels deep takes only a few hundred steps, so it passes
/// every step budget and then aborts the process on the recursion -- which is worse than a
/// slow answer, because the crate's whole contract is that an undecidable query is
/// *reported*, never a crash. The shape that reaches this depth is a fold-built term: a
/// wide division by a non-power-of-two constant builds a chain of adders and muxes whose
/// length is proportional to the width, and the walk has no memo for the *stack*, only for
/// the visits.
///
/// The bound is chosen from measurement. Over both corpus files the deepest legitimate walk
/// is **138** levels; `udiv(x, 3)` at 64 bits reaches **262** and is the query that
/// overflowed a 2 MiB stack in release (a `blast` frame is ~2.3 KiB, so the walk wanted
/// ~600 KiB and then some). 128 would refuse a query the corpus already decides, so the
/// bound sits at **192**: above every decided query with margin, below the observed blow-up.
/// A trip sets `overflow`, so the query routes to the SAT fallback and from there to
/// `Unknown` -- sound, and it *returns*.
pub(crate) const MAX_WALK_DEPTH: u32 = 192;

/// How many leaves of an `And`/`Or` spine the structural cancellation in
/// [`Ctx::cancel_through_spine`] inspects.
///
/// A path condition is a left-nested chain, so the conjunct that cancels a later term
/// can sit deeper than the root; walking the spine is what reaches it. The cap keeps the
/// check O(1) per connective -- it is on the construction path of every `and`/`or`, so it
/// has to be cheap -- and truncating it only *misses* cancellations, never invents one.
pub(crate) const MAX_CONJ: usize = 16;

/// Worst-case arena memory in bytes, so an integrator can budget statically.
pub const ARENA_BYTES: usize =
    CAP * (core::mem::size_of::<Node>() + 2 * core::mem::size_of::<u32>());

/// Maximum number of symbolic variables per thread.
pub const MAX_VARS: usize = 256;

/// Term id 0 is reserved, never a real term.
///
/// [`Var::SENTINEL`] is `Var(Term(TERM_SENTINEL))`, and it has to be distinguishable from
/// every real term, because the fixed-size buffers in [`crate::wp`] use it as their
/// "no variable here" filler and rely on it never colliding with a live handle. It did
/// collide: the allocator handed out ids from 0, so `Term(0)` was the *first* real term,
/// and `Var::SENTINEL == var(8)` held -- the exact opposite of the comment on
/// `wp::writes` that promised "slot 0 is never a real variable". The collision was latent
/// because every reader is `[..n]`-counted, but an invariant a reviewer would lean on was
/// simply false. Reserving id 0 makes it true, and the reserved slot is one term out of
/// [`CAP`].
pub const TERM_SENTINEL: u32 = 0;

/// Bits of a term id that name a slot in the arena.
///
/// [`CAP`] is `1 << 14`, so 14 bits address every slot. The remaining bits of the id
/// carry the generation that created it.
const TERM_SLOT_BITS: u32 = 14;

/// Mask selecting the slot half of a packed term id.
const TERM_SLOT_MASK: u32 = (1 << TERM_SLOT_BITS) - 1;

/// Bits of a term id that carry the creating generation.
const TERM_GEN_BITS: u32 = u32::BITS - TERM_SLOT_BITS;

/// Mask selecting the generation half of a packed term id.
const TERM_GEN_MASK: u32 = u32::MAX << TERM_SLOT_BITS;

/// The largest generation a packed id can name.
///
/// A term id carries its generation so that a *recycled slot* cannot validate a stale
/// handle. The count of generations an arena has lived through is far smaller than
/// [`CAP`], so 18 bits is not a real limit: it would take that many `with_fresh` calls
/// on one thread while still holding a handle from the first, which the no-nesting
/// contract already forbids. It is documented rather than asserted because a wrapping
/// generation would only mean "a very old handle may match again", and the alternative
/// (a `usize` id) would double the size of every handle in the crate.
const TERM_GEN_MAX: u32 = (1 << TERM_GEN_BITS) - 1;

/// Maximum number of assignments reported in a counterexample.
pub const MAX_CEX: usize = 16;

// ---------------------------------------------------------------------------
// Verdicts
// ---------------------------------------------------------------------------

/// A concrete assignment (model or counterexample), as bit-vector values.
///
/// `MAX_CEX` entries are inlined rather than heap-allocated, which keeps the
/// type `Copy` and allocation-free. That makes this the largest variant of
/// [`Verdict`]; boxing it would require an allocator, which this crate does not
/// use, so the size is accepted deliberately.
///
/// Because the buffer is fixed, a model with more than `MAX_CEX` variables cannot be
/// reported in full. It used to be truncated silently, and `value_of` then returned
/// `None` for a *dropped* variable exactly as it does for one that was never mentioned —
/// so a caller could not tell an incomplete witness from a complete one. A model is the
/// evidence for a refutation; a truncated one is evidence with a hole in it, and the hole
/// has to be visible. [`Cex::is_complete`] reports it, and `total` records how many
/// variables the model actually touched.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Cex {
    assignments: [(u32, u8, u64); MAX_CEX],
    n: u8,
    /// How many variables the model touched, which may exceed `n` when the buffer was
    /// too small to hold them all. `n < total` means the witness is truncated.
    total: u32,
}

impl Cex {
    /// Value assigned to variable `var`, if that variable appears in the model.
    ///
    /// `None` means either that the variable was not mentioned or that the model was
    /// truncated before reaching it. Check [`Cex::is_complete`] to tell those apart; a
    /// `None` from an incomplete model is not evidence that the variable is unconstrained.
    pub fn value_of(&self, var: u32) -> Option<u64> {
        for i in 0..self.n as usize {
            let (v, _w, val) = self.assignments[i];
            if v == var {
                return Some(val);
            }
        }
        None
    }

    /// Number of variables reported.
    pub fn len(&self) -> usize {
        self.n as usize
    }

    /// True when no variable was mentioned.
    pub fn is_empty(&self) -> bool {
        self.n == 0
    }

    /// True when every variable the model touched is present.
    ///
    /// A complete model is a witness: replaying its assignments satisfies the query. An
    /// incomplete one is a *partial* witness — the assignments it does carry are correct,
    /// but the model also relied on variables that were dropped, so replaying it alone
    /// need not reproduce the verdict.
    pub fn is_complete(&self) -> bool {
        self.n as u32 == self.total
    }

    /// How many variables the model touched, reported or not.
    pub fn total(&self) -> u32 {
        self.total
    }
}

impl fmt::Display for Cex {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for i in 0..self.n as usize {
            let (v, w, val) = self.assignments[i];
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "v{}:u{} = {}", v, w, val)?;
        }
        if !self.is_complete() {
            // Say so in the rendering, not only in the API: a truncated witness printed
            // as if complete is the failure mode this flag exists to prevent.
            write!(f, " … {}/{} shown (TRUNCATED)", self.n, self.total)?;
        }
        Ok(())
    }
}

/// Result of a decision-procedure query.
///
/// The `Counterexample` variant inlines its assignments so that `Verdict` stays
/// `Copy` and allocation-free. That makes it the largest variant, which the
/// `large_enum_variant` lint flags; boxing it would require an allocator, which
/// this crate deliberately does not use.
#[allow(clippy::large_enum_variant)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Verdict {
    /// Holds for every input.
    Valid,
    /// Holds for no input (unsatisfiable).
    Unsat,
    /// A concrete input falsifies the property (for a validity query).
    Counterexample(Cex),
    /// The node budget was exhausted before a conclusion was reached. We refuse
    /// to guess: "unknown" is a first-class, safe answer.
    Unknown,
}

impl Verdict {
    /// True only when the property was *proved*. `Unknown` is not a proof.
    pub const fn is_proved(&self) -> bool {
        matches!(self, Verdict::Valid)
    }

    /// True when the query completed with a definite answer.
    pub const fn is_decided(&self) -> bool {
        !matches!(self, Verdict::Unknown)
    }
}

impl fmt::Display for Verdict {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Verdict::Valid => write!(f, "valid (proved for all inputs)"),
            Verdict::Unsat => write!(f, "unsat (no input satisfies it)"),
            Verdict::Counterexample(c) => write!(f, "refuted: {}", c),
            // `Unknown` has more than one cause: the node budget, an ill-formed query
            // (a width clash, an out-of-range constant, or a duplicated binding target),
            // an out-of-range variable index, or a stale handle. Naming only the budget
            // made an ill-formed query read as "try a smaller formula". The cause is not
            // carried in the verdict (it would widen a `Copy` enum used in hot loops), so
            // the message stays general and honest.
            Verdict::Unknown => write!(
                f,
                "unknown (no conclusion: budget exhausted, ill-formed query, or stale handle)"
            ),
        }
    }
}

// ---------------------------------------------------------------------------
// Terms
// ---------------------------------------------------------------------------

/// A packed term id: the low [`TERM_SLOT_BITS`] bits name a slot in the arena, the rest
/// carry the generation that created it.
///
/// The generation is *inside the handle* rather than in a side table indexed by slot.
/// Stamping a side table (`term_gen[slot] = generation`) cannot detect a recycled slot,
/// because the reset that recycles the slot rewrites the stamp the stale handle would
/// have been checked against: a predicate saved from one arena, looked up in the next,
/// found a *current* stamp on whatever term now occupied its slot and was reported
/// `Valid` when it was false. Packing the generation into the id makes the comparison
/// against the handle's own bits, which no later allocation can rewrite.
///
/// Child references in a [`Node`] hold a packed id verbatim in `a`/`b`/`c`, so
/// `Term(n.a)` reconstructs the same handle and the traversal code needs no change.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Term(pub(crate) u32);

impl Term {
    /// The arena slot this id names.
    fn slot(self) -> usize {
        (self.0 & TERM_SLOT_MASK) as usize
    }

    /// The generation bits of this id.
    fn gen_bits(self) -> u32 {
        self.0 & TERM_GEN_MASK
    }

    /// Pack a slot and a generation into an id.
    fn pack(slot: u32, generation: u32) -> Term {
        Term((slot & TERM_SLOT_MASK) | (generation << TERM_SLOT_BITS))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Op {
    Var,
    Const,
    Not,
    And,
    Or,
    Xor,
    Shl,
    LShr,
    Shr,
    Add,
    Sub,
    Mul,
    Eq,
    Ult,
    Ule,
    Ite,
    /// Zero-extend or truncate: the width changes, the low bits are kept.
    ///
    /// `a` is the operand, `b` the source width. Bit `i` of the result is bit `i`
    /// of the operand when `i < b`, and zero otherwise. This is the one width-
    /// changing operation in the language, and it exists because a loop counter
    /// often has to be wider than the value it indexes: with four addresses a
    /// 2-bit counter cannot reach 4, so the counter is 3 bits and gets truncated
    /// at the point of use.
    Trunc,
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct Node {
    pub(crate) op: Op,
    pub(crate) a: u32,
    pub(crate) b: u32,
    pub(crate) c: u32,
    pub(crate) width: u8,
    /// High 32 bits of a constant payload.
    pub(crate) hi: u32,
}

const FALSE: u32 = 0;
const TRUE: u32 = 1;

/// BDD variable id for (word variable `idx`, bit `b`).
const fn bdd_var(idx: u32, b: u32) -> u32 {
    idx * 64 + b
}

/// Ordering level of a BDD variable. Interleaving bit-planes by significance
/// keeps ripple-carry adders and comparators linear in BDD size.
const fn level_of(v: u32) -> u32 {
    (v & 63) * (MAX_VARS as u32) + (v >> 6)
}

// ---------------------------------------------------------------------------
// Manager
// ---------------------------------------------------------------------------

pub(crate) struct Ctx {
    terms: [Node; CAP],
    n_terms: usize,
    term_key: [u64; CAP],
    term_val: [u32; CAP],
    term_mask: u32,

    var: [u32; CAP],
    lo: [u32; CAP],
    hi: [u32; CAP],
    n_nodes: usize,

    uniq_key: [u64; CAP],
    uniq_val: [u32; CAP],
    uniq_mask: u32,

    and_key: [u64; CAP],
    and_val: [u32; CAP],
    or_key: [u64; CAP],
    or_val: [u32; CAP],
    xor_key: [u64; CAP],
    xor_val: [u32; CAP],
    not_key: [u64; CAP],
    not_val: [u32; CAP],

    var_width: [u8; MAX_VARS],
    n_vars: usize,
    overflow: bool,
    /// Memo for the BDD blaster: the blasted bits of a term, keyed by term id.
    ///
    /// Validity is scoped by the arena [`Ctx::generation`]: the key stores the term id
    /// *including* its generation bits, and a reset recycles slots under a new generation,
    /// so a stale entry can never be read as a current term's value. Cleared with the arena.
    blast_memo_key: [u32; BLAST_MEMO_N],
    blast_memo_bits: [[u32; 64]; BLAST_MEMO_N],
    /// Steps taken by the BDD blaster in the current query, against [`MAX_BLAST_STEPS`].
    blast_steps: u32,
    /// Steps taken by the BDD *apply* in the current query, against [`MAX_APPLY_STEPS`].
    ///
    /// A separate counter from `blast_steps`: the two bound different work (the term-DAG
    /// walk and the diagram recursion), and a query can blow up in either while staying
    /// small in the other. Both reset per query and both trip `overflow`.
    apply_steps: u32,
    /// Steps taken by the SAT blaster in the current query, against [`MAX_BLAST_STEPS`].
    sat_blast_steps: u32,
    /// Current recursion depth of the term walk, against [`MAX_WALK_DEPTH`].
    ///
    /// A field rather than a parameter so the recursive walkers do not have to thread it,
    /// and reset per query alongside the step counters.
    walk_depth: u32,
    /// Set when a variable index past `MAX_VARS` was requested.
    ///
    /// `overflow` alone is not enough to decide whether to fall back to the SAT engine.
    /// Every place that sets `overflow` is either a BDD arena that filled -- a scale
    /// problem the SAT engine can solve -- or this one, a modelling mistake (asking for
    /// variable #257). In the latter case `var_term` returns the term sentinel, and blasting
    /// the sentinel is *stale*, so a fallback would report `Unsat` for a query that is
    /// really malformed. This flag lets the fallback refuse instead.
    var_overflow: bool,
    ready: bool,

    // ---- substitution support (weakest-precondition generation) ----
    // `subst_val[i]` is the replacement term for variable `i`, or `NO_SUBST`.
    subst_val: [u32; MAX_VARS],
    // Memo for `subst`, stamped with the current epoch so it never needs
    // clearing when a new substitution begins.
    subst_memo: [u32; CAP],
    subst_epoch: [u32; CAP],
    epoch: u32,

    /// Bumped by every [`Ctx::reset`]. Term ids are recycled by a reset, so a handle from
    /// one arena can name a different term in the next. `epoch` cannot serve here: it is
    /// about the substitution memo, and it is also bumped by `clear_subst` within a single
    /// arena. This counter changes only when the arena is wiped.
    ///
    /// It is stored *inside each handle* (see [`Term`]) rather than in a per-slot table,
    /// because a per-slot table is rewritten by the very reset that recycles the slot and
    /// so cannot detect a stale handle. Always kept non-zero so the sentinel's generation
    /// bits never match a live arena.
    generation: u32,
    /// Set when a stale handle is touched. Sticky until the next reset, and treated exactly
    /// like `overflow`: the query refuses to answer rather than answer about the wrong term.
    stale: bool,
    /// Set when the query is ill-formed: a binary operation over operands of different
    /// widths, a constant that does not fit its width, or two bindings for the same
    /// substitution target. Sticky until the next reset, and treated like `overflow` and
    /// `stale`: the query returns `Unknown` rather than a verdict about a term that was
    /// never written. Each of those is a *refusal*; the alternative in every case is to
    /// pick one of several meanings silently, which is the failure this crate exists to
    /// prevent.
    ill_formed: bool,

    /// Makes `Ctx` `!Send` and `!Sync`, so the claim in the `no_std` `with_ctx` SAFETY
    /// comment is enforced by the type system rather than merely asserted. Every field
    /// above is a plain array or integer, so without this marker `Ctx` is auto-`Send` and
    /// auto-`Sync` -- and a type that is `Sync` can be shared across threads, which is
    /// exactly the sharing the single global `static mut CTX` cannot survive. The marker
    /// is a `*mut` because it is the one pointer type with no `Send`/`Sync` impl; it is
    /// never dereferenced, and it costs nothing at runtime.
    _not_shared: core::marker::PhantomData<*mut ()>,
}

/// Sentinel: variable `i` has no replacement.
const NO_SUBST: u32 = u32::MAX;

/// A compile-time gate that [`Ctx`] is `!Send` and `!Sync`.
///
/// The bare-metal [`with_ctx`] hands out `&'static mut Ctx` from a single global
/// `static mut CTX`, which is sound only while nothing else can reach that
/// context -- no second thread, and no re-entrant call. The `_not_shared` marker
/// is what makes that true, and until now only a comment said so: delete the
/// marker and `Ctx` is auto-`Send` and auto-`Sync` (every remaining field is a
/// plain array or integer), the crate still builds, and the safety argument is
/// quietly false. This turns "the marker is load-bearing" into something the
/// compiler checks on every build.
///
/// The mechanism is inference ambiguity, not a reading of the impls. The trait is
/// implemented for *every* type at `AmbiguousIfImpl<()>`, and again at
/// `AmbiguousIfImpl<InvalidSend>` for every `Send` type. If `Ctx` is `!Send` only
/// the first applies, so the `_` below infers to `()` and this compiles. If `Ctx`
/// *were* `Send`, both would apply and `_` would have no unique value -- an
/// inference error, which is the gate firing. `Sync` is checked the same way, so
/// the fact that this file compiles *is* the proof.
const _: fn() = || {
    trait AmbiguousIfImpl<A> {
        fn some_item() {}
    }
    impl<T: ?Sized> AmbiguousIfImpl<()> for T {}

    #[allow(dead_code)]
    enum InvalidSend {}
    impl<T: ?Sized + Send> AmbiguousIfImpl<InvalidSend> for T {}

    #[allow(dead_code)]
    enum InvalidSync {}
    impl<T: ?Sized + Sync> AmbiguousIfImpl<InvalidSync> for T {}

    let _ = <Ctx as AmbiguousIfImpl<_>>::some_item;
};

impl Ctx {
    const fn new() -> Self {
        Ctx {
            terms: [Node { op: Op::Const, a: 0, b: 0, c: 0, width: 0, hi: 0 }; CAP],
            // Starts at 1: id 0 is reserved for [`TERM_SENTINEL`]. See its docs.
            n_terms: TERM_SENTINEL as usize + 1,
            term_key: [u64::MAX; CAP],
            term_val: [0; CAP],
            term_mask: 0,
            var: [0; CAP],
            lo: [0; CAP],
            hi: [0; CAP],
            n_nodes: 2,
            uniq_key: [u64::MAX; CAP],
            uniq_val: [0; CAP],
            uniq_mask: 0,
            and_key: [u64::MAX; CAP],
            and_val: [0; CAP],
            or_key: [u64::MAX; CAP],
            or_val: [0; CAP],
            xor_key: [u64::MAX; CAP],
            xor_val: [0; CAP],
            not_key: [u64::MAX; CAP],
            not_val: [0; CAP],
            var_width: [0; MAX_VARS],
            n_vars: 0,
            overflow: false,
            blast_memo_key: [0; BLAST_MEMO_N],
            blast_memo_bits: [[FALSE; 64]; BLAST_MEMO_N],
            blast_steps: 0,
            apply_steps: 0,
            sat_blast_steps: 0,
            walk_depth: 0,
            var_overflow: false,
            ready: false,
            subst_val: [NO_SUBST; MAX_VARS],
            subst_memo: [0; CAP],
            subst_epoch: [0; CAP],
            epoch: 1,
            generation: 1,
            stale: false,
            ill_formed: false,
            _not_shared: core::marker::PhantomData,
        }
    }

    /// Clear the arena in place. Deliberately avoids `*self = Ctx::new()`, which
    /// would materialise a large temporary on the stack (bad on small firmware
    /// stacks) just to throw it away.
    fn reset(&mut self) {
        // Id 0 stays reserved for [`TERM_SENTINEL`]; real terms start at 1.
        self.n_terms = TERM_SENTINEL as usize + 1;
        self.n_nodes = 2;
        self.n_vars = 0;
        self.overflow = false;
        // The memo is keyed by term id *including* its generation, and the generation is
        // bumped below, so the old keys can never match a term in the new arena. Nothing to
        // clear -- only the counters, which are per query, not per arena.
        self.blast_steps = 0;
        self.apply_steps = 0;
        self.sat_blast_steps = 0;
        self.walk_depth = 0;
        self.var_overflow = false;
        self.ready = false;
        for i in 0..CAP {
            self.term_key[i] = u64::MAX;
            self.term_val[i] = 0;
            self.uniq_key[i] = u64::MAX;
            self.uniq_val[i] = 0;
            self.and_key[i] = u64::MAX;
            self.and_val[i] = 0;
            self.or_key[i] = u64::MAX;
            self.or_val[i] = 0;
            self.xor_key[i] = u64::MAX;
            self.xor_val[i] = 0;
            self.not_key[i] = u64::MAX;
            self.not_val[i] = 0;
        }
        for i in 0..MAX_VARS {
            self.var_width[i] = 0;
            self.subst_val[i] = NO_SUBST;
        }
        // A fresh epoch invalidates every memo entry without touching the array.
        // It must be bumped, not reset: see `bump_epoch`.
        self.bump_epoch();
        // Term ids are packed from a slot and the generation, and the slot numbering
        // restarts here, so every handle from the previous arena carries a generation the
        // new arena will not hand out. Bumping is what makes a stale handle reject itself
        // -- the check compares the handle's own bits, which nothing here rewrites.
        self.generation = self.generation.wrapping_add(1);
        if self.generation == 0 || self.generation > TERM_GEN_MAX {
            // Keep the generation inside the bits a handle can hold, and never let it be
            // zero: zero is the sentinel's generation, and a live term must never look
            // like the sentinel. Wrapping to 1 after the maximum is the only case where an
            // extremely old handle could match again, and holding one across 2^18 resets
            // is already outside the no-nesting contract.
            self.generation = 1;
        }
        self.stale = false;
        self.ill_formed = false;
        self.ensure_ready();
    }

    /// The generation as it appears in a handle's bits.
    fn gen_masked(&self) -> u32 {
        self.generation << TERM_SLOT_BITS
    }

    /// Lazily compute the open-addressing masks. Must run before any arena use;
    /// `with_ctx` calls it, so callers never have to think about it.
    fn ensure_ready(&mut self) {
        if self.ready {
            return;
        }
        let mut sz = 1usize;
        while sz < CAP {
            sz <<= 1;
        }
        let mask = (sz as u32) - 1;
        self.uniq_mask = mask;
        self.term_mask = mask;
        // The two terminal nodes must carry `var == u32::MAX`, because that is
        // how `top_var`/`cofactors` recognise "no variable here". Getting this
        // wrong silently produces a non-canonical (and exponentially larger)
        // diagram rather than an error, so it is set unconditionally.
        self.var[FALSE as usize] = u32::MAX;
        self.lo[FALSE as usize] = FALSE;
        self.hi[FALSE as usize] = FALSE;
        self.var[TRUE as usize] = u32::MAX;
        self.lo[TRUE as usize] = TRUE;
        self.hi[TRUE as usize] = TRUE;
        self.n_nodes = 2;
        self.ready = true;
    }

    // ------------------------- term arena -------------------------

    fn hash_node(n: &Node) -> u64 {
        let mut h = 0xcbf29ce484222325u64;
        let mut mix = |x: u64| {
            h ^= x;
            h = h.wrapping_mul(0x100000001b3);
        };
        mix(n.op as u64);
        mix(n.a as u64);
        mix(n.b as u64);
        mix(n.c as u64);
        mix(n.width as u64);
        mix(n.hi as u64);
        h | 1
    }

    fn mk_term(&mut self, n: Node) -> Term {
        let key = Self::hash_node(&n);
        let mut i = (key as u32) & self.term_mask;
        // See `mk_node`: a table with no empty slot left must be detected by the
        // probe count, because the capacity test sits inside the empty-slot
        // branch and would otherwise never be reached.
        let mut probes = 0usize;
        loop {
            let k = self.term_key[i as usize];
            if k == u64::MAX {
                if self.n_terms >= CAP {
                    self.overflow = true;
                    return Term(0);
                }
                let id = self.n_terms as u32;
                self.n_terms += 1;
                self.terms[id as usize] = n;
                self.term_key[i as usize] = key;
                self.term_val[i as usize] = id;
                return Term::pack(id, self.generation);
            }
            if k == key {
                let e = self.terms[self.term_val[i as usize] as usize];
                if e.op == n.op
                    && e.a == n.a
                    && e.b == n.b
                    && e.c == n.c
                    && e.width == n.width
                    && e.hi == n.hi
                {
                    return Term::pack(self.term_val[i as usize], self.generation);
                }
            }
            probes += 1;
            if probes > self.term_mask as usize {
                self.overflow = true;
                return Term(0);
            }
            i = (i + 1) & self.term_mask;
        }
    }

    /// Note a stale handle. Every accessor funnels through here, so one check covers
    /// `Var`, `Pred`, and anything else that carries a term id — the caller does not have
    /// to remember to look.
    pub(crate) fn is_current_term(&mut self, t: Term) -> bool {
        if t.gen_bits() != self.gen_masked() {
            self.stale = true;
            false
        } else {
            true
        }
    }

    fn note_if_stale(&mut self, t: Term) {
        if t.gen_bits() != self.gen_masked() {
            self.stale = true;
        }
    }

    fn node_of(&mut self, t: Term) -> Node {
        self.note_if_stale(t);
        self.terms[t.slot()]
    }

    /// The variable index a binding target names, refusing anything that is not a variable.
    ///
    /// A binding is `(from, to)`, and `from` has to be a *variable*. It was previously read
    /// as `node_of(from).a` without a check, and `a` means different things per operation:
    /// for a `Var` it is the index, but for a `Const` it is the *value*. So binding the
    /// constant `word(7, 8)` -- whose `a` is 7 -- silently substituted variable index 7, and
    /// `x := 7` written with a constant target proved `v7 == 0`. For a `Trunc` or an `Ite`,
    /// `a` is a *term id*, which as an index is either out of range (silently dropped by
    /// `set_subst`) or an unrelated variable. All of those are silent mis-substitutions
    /// rather than refusals, which is exactly the failure mode this crate exists to avoid.
    fn subst_target(&mut self, from: Term) -> u32 {
        let n = self.node_of(from);
        assert!(
            n.op == Op::Var,
            "substitution target must be a variable, not {:?}; `word`/`truncate`/`ite` \
             terms carry a value or a term id in that field, so binding one would rewrite \
             an unrelated variable",
            n.op
        );
        n.a
    }

    pub(crate) fn width_of(&mut self, t: Term) -> u8 {
        self.note_if_stale(t);
        self.terms[t.slot()].width
    }

    /// Read a term's node. Exposed to the crate so the SMT-LIB exporter can walk
    /// the same IR the solver reasons about, instead of re-deriving it.
    pub(crate) fn node_pub(&mut self, t: Term) -> Node {
        self.note_if_stale(t);
        self.terms[t.slot()]
    }

    // ------------------------- substitution -------------------------

    /// Record that variable `idx` is replaced by term `with` for subsequent
    /// [`Ctx::subst`] calls. Calling this again with the same `idx` replaces the
    /// previous binding, which is exactly what a sequence of assignments needs.
    fn set_subst(&mut self, idx: u32, with: Term) {
        if (idx as usize) < MAX_VARS {
            // A second binding for the same target is ambiguous: "keep the last" silently
            // picks one meaning for `x := 1, x := 2`, and which one it picks is the order
            // of the list rather than anything the specification says. Mark the query
            // ill-formed instead, so it answers `Unknown`.
            if self.subst_val[idx as usize] != NO_SUBST {
                self.ill_formed = true;
            }
            self.subst_val[idx as usize] = with.0;
        }
    }

    /// Record one substitution binding, refusing a width mismatch.
    ///
    /// A binding replaces a variable with a term, and the two must agree on
    /// width. `subst_target` already refuses a non-variable *target*; without the
    /// matching check on the replacement, an 8-bit variable could be bound to a
    /// 16-bit word, and the rebuilt expression would read only the low bits. The
    /// blaster then uses the *comparison's* width and silently discards the high
    /// bits, so `x == 1` with `x := 257u16` would be proved `Valid` even though
    /// `257` does not fit in `x`. That is an assignment the source language
    /// rejects, so accepting it can only produce a wrong answer; the query is
    /// marked ill-formed instead.
    fn bind_subst(&mut self, from: Term, to: Term) {
        let idx = self.subst_target(from);
        let w_from = self.width_of(from);
        let w_to = self.width_of(to);
        if w_from != w_to {
            self.ill_formed = true;
        }
        self.set_subst(idx, to);
    }

    /// Forget every binding and start a new substitution epoch.
    fn clear_subst(&mut self) {
        for i in 0..MAX_VARS {
            self.subst_val[i] = NO_SUBST;
        }
        self.bump_epoch();
    }

    /// Advance the substitution epoch, invalidating every memo entry.
    ///
    /// This must be a *bump*, never a reset to a fixed value. Restoring a
    /// previous epoch would make stamps from that epoch look current again, and
    /// the memo would hand back node ids that `reset` has since recycled. The
    /// result is a cycle in the term graph and unbounded recursion.
    fn bump_epoch(&mut self) {
        self.epoch = self.epoch.wrapping_add(1);
        if self.epoch == 0 {
            // The counter wrapped, so the stamps are meaningless: clear them.
            for i in 0..CAP {
                self.subst_epoch[i] = 0;
            }
            self.epoch = 1;
        }
    }

    /// Substitute the currently registered variables throughout `t`, rebuilding
    /// the term bottom-up.
    ///
    /// Substitution must go bottom-up because a replacement may itself mention a
    /// variable that is also being replaced (the classic `x, y := y, x` case).
    /// Doing it top-down would capture those variables and prove the wrong thing.
    fn subst(&mut self, t: Term) -> Term {
        if self.stale || t.gen_bits() != self.gen_masked() {
            self.stale = true;
            return Term(0);
        }
        let n = self.node_of(t);
        match n.op {
            Op::Var => {
                let r = self.subst_val[n.a as usize];
                if r == NO_SUBST {
                    t
                } else {
                    Term(r)
                }
            }
            Op::Const => t,
            _ => {
                // Memo keyed by term id, valid only within the current epoch.
                let key = t.slot();
                if self.subst_epoch[key] == self.epoch {
                    return Term(self.subst_memo[key]);
                }
                let a = self.subst(Term(n.a));
                // `b` is a term id for most operations, but it is a *payload* for the
                // unary and shift forms: the source width for `Trunc`, and the shift
                // amount for `Shl`/`LShr`/`Shr`. Recursing into it as if it were a term
                // id substitutes an unrelated term -- and when that id names a term that
                // contains this very shift, the recursion never bottoms out. The rebuild
                // below already carries the payload across, so it must not be traversed.
                let b = if matches!(n.op, Op::Not | Op::Trunc | Op::Shl | Op::LShr | Op::Shr) {
                    Term(0)
                } else {
                    self.subst(Term(n.b))
                };
                let c = if n.op == Op::Ite {
                    self.subst(Term(n.c))
                } else {
                    Term(0)
                };
                let rebuilt = match n.op {
                    Op::Not => self.mk_term(Node { op: n.op, a: a.0, b: 0, c: 0, width: n.width, hi: 0 }),
                    Op::Shl | Op::LShr | Op::Shr | Op::Trunc => {
                        self.mk_term(Node { op: n.op, a: a.0, b: n.b, c: 0, width: n.width, hi: 0 })
                    }
                    Op::Ite => self.mk_term(Node {
                        op: n.op,
                        a: a.0,
                        b: b.0,
                        c: c.0,
                        width: n.width,
                        hi: 0,
                    }),
                    _ => self.mk_term(Node { op: n.op, a: a.0, b: b.0, c: 0, width: n.width, hi: 0 }),
                };
                // Do not memoise after an arena overflow: the rebuilt term is
                // meaningless then, and caching it would corrupt later queries.
                if !self.overflow {
                    self.subst_memo[key] = rebuilt.0;
                    self.subst_epoch[key] = self.epoch;
                }
                rebuilt
            }
        }
    }

    fn konst(&mut self, v: u64, width: u8) -> Term {
        let masked = if width >= 64 { v } else { v & ((1u64 << width) - 1) };
        self.mk_term(Node {
            op: Op::Const,
            a: masked as u32,
            hi: (masked >> 32) as u32,
            b: 0,
            c: 0,
            width,
        })
    }

    fn const_value(&mut self, t: Term) -> u64 {
        let n = self.node_of(t);
        (n.a as u64) | ((n.hi as u64) << 32)
    }

    // ---- read-only accessors, for the SAT bit-blaster --------------------
    //
    // The SAT blaster lives in `crate::bitblast` and walks the same term arena. It is a
    // separate module rather than a method because it needs `&mut Cnf` at the same time,
    // and these accessors are what let it read terms without a second `&mut self`.
    // `note_if_stale`/`mark_stale` are called explicitly by the blaster so the stale
    // bookkeeping stays identical to the BDD path.

    /// Whether `t` carries a stale generation stamp.
    pub(crate) fn is_stale(&self, t: Term) -> bool {
        self.stale || t.gen_bits() != self.gen_masked()
    }

    /// Poison the traversal, exactly as `blast` does on a stale touch.
    pub(crate) fn mark_stale(&mut self) {
        self.stale = true;
    }

    /// Charge one step to the SAT blaster, returning `true` once [`MAX_BLAST_STEPS`] is
    /// spent. The SAT blaster runs after the BDD pass has given up, so it gets its own
    /// counter; both are reset per query.
    pub(crate) fn charge_sat_step(&mut self) -> bool {
        self.sat_blast_steps = self.sat_blast_steps.saturating_add(1);
        self.sat_blast_steps > MAX_BLAST_STEPS
    }

    /// Charge one level of recursion to the term walk, returning `true` once
    /// [`MAX_WALK_DEPTH`] is spent.
    ///
    /// The SAT blaster walks the same terms as the BDD one, so it shares the counter. A
    /// trip is reported the way the step budgets are: the query falls through to the
    /// engine that can still answer it, and `Unknown` if none can.
    pub(crate) fn charge_walk_depth(&mut self) -> bool {
        self.walk_depth = self.walk_depth.saturating_add(1);
        self.walk_depth > MAX_WALK_DEPTH
    }

    /// Release a level charged by [`Self::charge_walk_depth`].
    pub(crate) fn release_walk_depth(&mut self) {
        self.walk_depth = self.walk_depth.saturating_sub(1);
    }

    /// Mark the query ill-formed, so it answers `Unknown`. Used by the SAT blaster for the
    /// same reason the BDD one sets the flag directly: a width the blaster cannot represent
    /// must refuse the query rather than index past its buffer.
    pub(crate) fn mark_ill_formed(&mut self) {
        self.ill_formed = true;
    }

    /// Read a term node without the stale check; the caller has already done it.
    pub(crate) fn peek(&self, t: Term) -> Node {
        self.terms[t.slot()]
    }

    /// The constant payload of a `Const` term, without the stale check.
    pub(crate) fn const_of(&self, t: Term) -> u64 {
        let n = self.terms[t.slot()];
        (n.a as u64) | ((n.hi as u64) << 32)
    }

    /// Build a counterexample from a SAT model. Mirrors `model`'s truncation accounting so
    /// `Cex::is_complete` means the same thing on both paths.
    pub(crate) fn cex_from_sat(&self, val: impl Fn(u32) -> Option<bool>) -> Cex {
        let mut cex = Cex { assignments: [(0, 0, 0); MAX_CEX], n: 0, total: 0 };
        for idx in 0..self.n_vars {
            let w = self.var_width[idx];
            let mut bits = 0u64;
            let mut touched = false;
            for bit in 0..w as u32 {
                if let Some(b) = val(idx as u32 * 64 + bit) {
                    touched = true;
                    if b {
                        bits |= 1u64 << bit;
                    }
                }
            }
            if touched {
                cex.total += 1;
                if (cex.n as usize) < MAX_CEX {
                    cex.assignments[cex.n as usize] = (idx as u32, w, bits);
                    cex.n += 1;
                }
            }
        }
        cex
    }

    fn var_term(&mut self, idx: u32, width: u8) -> Term {
        if idx as usize >= MAX_VARS {
            self.overflow = true;
            self.var_overflow = true;
            return Term(0);
        }
        // A variable is identified by its *index*, and the blaster keys its BDD variables
        // by `(index, bit)`. Declaring the same index at two widths therefore aliases the
        // low bits: `var_named(0, 8)` and `var_named(0, 16)` share bits 0..7, so
        // `a == 3 => truncate(b, 8) == 3` was proved -- a theorem about one variable
        // silently constraining another. Same index at the same width is the intended
        // "fetch the same variable again" case and stays allowed; a width change is a
        // modelling mistake, and the honest answer is to refuse the query.
        let prev = self.var_width[idx as usize];
        if prev != 0 && prev != width {
            self.ill_formed = true;
        }
        self.var_width[idx as usize] = width;
        if idx as usize + 1 > self.n_vars {
            self.n_vars = idx as usize + 1;
        }
        self.mk_term(Node { op: Op::Var, a: idx, b: 0, c: 0, width, hi: 0 })
    }

    /// Word-shaped binary op (result width = operand width).
    /// Both operands must be the same width.
    ///
    /// A bit-vector operation has no natural width if its operands disagree, and the
    /// silent choice -- take the *left* operand's width and truncate the right -- is
    /// unsound. `trunc2(b) + (a + 115)` was computed in 2 bits, so the right-hand sum was
    /// masked to `y & 3`; a predicate that is false for most inputs came out `Valid`. The
    /// crate has no widening operation, so the honest answer is to refuse the mixed-width
    /// term rather than guess: use an explicit [`truncate`] to make the intent visible.
    /// This matches the convention already used by `mem::Mem::check_addr` and
    /// `mem::Mem::store_binds`.
    fn require_same_width(&mut self, a: Term, b: Term, _who: &str) {
        if self.width_of(a) != self.width_of(b) {
            self.ill_formed = true;
        }
    }

    /// Constant-fold a word operation, so a term whose operands are both literals
    /// collapses to the literal it denotes.
    ///
    /// This is a capability fix, not a speed one. A frontend reads real code, and a
    /// constant operand there is the rule rather than the exception: a scaled index
    /// (`i * 4`), a masked flag (`x & 0xff`), a remainder by a literal (`n % 10`).
    /// Without the fold every one of those builds its full circuit -- `n % 10` at 64
    /// bits is a restoring divider, ~262 terms deep -- and the query is refused for
    /// being *too big to pose* even when both operands are known. The `-7 / 3` case
    /// that motivated this is the extreme: every input is a literal and the answer
    /// was still `Unknown`, because the divider was blasted and then walked.
    ///
    /// Folding is what keeps a query *small* when it is not *interesting*: a
    /// division whose dividend is pinned to a literal by a precondition becomes a
    /// single constant, and the obligation that mentions it collapses with it.
    ///
    /// Sound because the fold is the operator's own definition -- the same
    /// `wrapping_*` on the same masked values `eval_term_body` uses -- applied to a
    /// pair that has one value each. `None` when either operand is not a literal,
    /// or when the widths disagree (`require_same_width` reports that, as it does
    /// for the unfolded path).
    ///
    /// `0 - x` is the one subtraction deliberately left unfolded. There is no unary
    /// negation in the term language, so a negation is *spelled* `0 - x`, and the
    /// frontend keys its literal-range bookkeeping on that node being distinct from
    /// the literal it negates: `-128` for an `i8` is legal while the bare literal
    /// `128` is not, and both are the same eight bits, so the only thing that tells
    /// them apart is that one is a `Sub` node and the other a `Const`. Folding the
    /// negation to the literal merges the two and refuses `-128`. Every other
    /// subtraction still folds, including the `x - y` the restoring divider is
    /// built from.
    fn const_fold_word(&mut self, op: Op, a: Term, b: Term) -> Option<Term> {
        let na = self.node_of(a);
        if na.op != Op::Const {
            return None;
        }
        let nb = self.node_of(b);
        if nb.op != Op::Const {
            return None;
        }
        if na.width != nb.width {
            return None;
        }
        let w = na.width;
        let x = self.const_of(a);
        let y = self.const_of(b);
        if op == Op::Sub && x == 0 {
            return None;
        }
        let v = match op {
            Op::Add => x.wrapping_add(y),
            Op::Sub => x.wrapping_sub(y),
            Op::Mul => x.wrapping_mul(y),
            Op::And => x & y,
            Op::Or => x | y,
            Op::Xor => x ^ y,
            _ => return None,
        };
        Some(self.konst(v, w))
    }

    fn bin_word(&mut self, op: Op, a: Term, b: Term) -> Term {
        self.require_same_width(a, b, "binary word operation");
        if let Some(t) = self.const_fold_word(op, a, b) {
            return t;
        }
        let w = self.width_of(a);
        self.mk_term(Node { op, a: a.0, b: b.0, c: 0, width: w, hi: 0 })
    }

    /// The leaves of an associative `op` tree, iteratively and with a cap.
    ///
    /// A leaf is `t` itself when its root is not `op`; otherwise the union of its operands'
    /// leaves. The walk is iterative because a path condition is as deep as the path is
    /// long, and a recursive walk over it would be the same stack risk that
    /// [`MAX_WALK_DEPTH`] exists to bound. Leaving an `op` node undecomposed at the cap is
    /// sound for the caller: the node is still entailed by the tree it came from, so a
    /// cancellation found through it is a real one.
    fn op_leaves(&mut self, op: Op, t: Term, out: &mut [Term; MAX_CONJ]) -> usize {
        let mut n = 0usize;
        let mut stack = [Term(0); MAX_CONJ];
        let mut sp = 1usize;
        stack[0] = t;
        while sp > 0 && n < MAX_CONJ {
            sp -= 1;
            let cur = stack[sp];
            let node = self.node_of(cur);
            if node.op == op && node.width == 1 && sp + 2 <= MAX_CONJ {
                stack[sp] = Term(node.a);
                sp += 1;
                stack[sp] = Term(node.b);
                sp += 1;
            } else {
                out[n] = cur;
                n += 1;
            }
        }
        n
    }

    /// `Some(constant)` when `op(a, b)` is decided by a cancellation through the operands'
    /// spines: each side contributes a leaf `x` and `!x`, which makes `And` false and `Or`
    /// true. `None` when no such pair exists.
    ///
    /// This is what a path condition needs and a top-level identity check cannot give. The
    /// `sat_mul` shape is the example: the path into the multiply is `b == 0 && a <= MAX / b`
    /// and the overflow test is `b != 0 && a > MAX / b`, so the conjuncts cancel pairwise --
    /// but they cancel *across* two spines, not at either root. Without the fold the
    /// bit-blaster expands the divider inside both terms before any solver sees the
    /// contradiction, and the query has no verdict.
    ///
    /// `!x` is a `Not` node whose child is `x`, so a cancellation is a `Not` leaf on one side
    /// whose child is a leaf on the other. Reading it that way avoids building a `Not` per
    /// leaf just to test for one.
    fn cancel_through_spine(&mut self, op: Op, a: Term, b: Term) -> Option<Term> {
        let mut left = [Term(0); MAX_CONJ];
        let mut right = [Term(0); MAX_CONJ];
        let ln = self.op_leaves(op, a, &mut left);
        let rn = self.op_leaves(op, b, &mut right);
        let child_of_not = |me: &mut Self, t: Term| -> Option<u32> {
            let n = me.node_of(t);
            if n.op == Op::Not && n.width == 1 { Some(n.a) } else { None }
        };
        for l in left.iter().take(ln) {
            if let Some(child) = child_of_not(self, *l) {
                if right[..rn].iter().any(|r| r.0 == child) {
                    return Some(self.konst((op == Op::Or) as u64, 1));
                }
            }
        }
        for r in right.iter().take(rn) {
            if let Some(child) = child_of_not(self, *r) {
                if left[..ln].iter().any(|l| l.0 == child) {
                    return Some(self.konst((op == Op::Or) as u64, 1));
                }
            }
        }
        None
    }

    /// Boolean op (result width = 1).
    fn bin_bool(&mut self, op: Op, a: Term, b: Term) -> Term {
        // Structural simplification, before any node is created. These are the
        // boolean-algebra identities, and they are not a micro-optimisation: a
        // contradiction such as `p && !p` *is* a literal false, but without the
        // fold the bit-blaster expands both copies of `p` first, and when `p`
        // contains a wide divider the diagram blows up before the SAT engine ever
        // sees the false literal. The `udiv`-guarded saturation idiom
        // (`if b != 0 && a > MAX / b`) is exactly that shape -- its guard is the
        // unsigned multiply-overflow predicate -- so the missing fold cost a whole
        // class of queries a verdict.
        let na = self.node_of(a);
        let nb = self.node_of(b);
        let konst = |n: Node| -> Option<u64> {
            if n.op == Op::Const && n.width == 1 { Some(n.a as u64) } else { None }
        };
        let is_not_of = |n: Node, t: Term| n.op == Op::Not && n.width == 1 && n.a == t.0;
        match op {
            Op::And => {
                if konst(na) == Some(0) || konst(nb) == Some(0) {
                    return self.konst(0, 1);
                }
                if konst(na) == Some(1) {
                    return b;
                }
                if konst(nb) == Some(1) {
                    return a;
                }
                if a.0 == b.0 {
                    return a;
                }
                if is_not_of(nb, a) || is_not_of(na, b) {
                    return self.konst(0, 1);
                }
            }
            Op::Or => {
                if konst(na) == Some(1) || konst(nb) == Some(1) {
                    return self.konst(1, 1);
                }
                if konst(na) == Some(0) {
                    return b;
                }
                if konst(nb) == Some(0) {
                    return a;
                }
                if a.0 == b.0 {
                    return a;
                }
                if is_not_of(nb, a) || is_not_of(na, b) {
                    return self.konst(1, 1);
                }
            }
            Op::Xor => {
                if konst(na) == Some(0) {
                    return b;
                }
                if konst(nb) == Some(0) {
                    return a;
                }
                if a.0 == b.0 {
                    return self.konst(0, 1);
                }
                if is_not_of(nb, a) || is_not_of(na, b) {
                    return self.konst(1, 1);
                }
                // `p ^ 1` is `!p`.
                if konst(na) == Some(1) {
                    return self.un_bool(Op::Not, b);
                }
                if konst(nb) == Some(1) {
                    return self.un_bool(Op::Not, a);
                }
            }
            _ => {}
        }
        if matches!(op, Op::And | Op::Or) {
            if let Some(k) = self.cancel_through_spine(op, a, b) {
                return k;
            }
        }
        self.mk_term(Node { op, a: a.0, b: b.0, c: 0, width: 1, hi: 0 })
    }

    /// Comparison op. The node keeps the *operand* width (the result is a
    /// single bit), so bit-blasting walks every operand bit but writes `out[0]`.
    fn max_of(&self, w: u8) -> u64 {
        if w >= 64 { u64::MAX } else { (1u64 << w) - 1 }
    }

    fn cmp(&mut self, op: Op, a: Term, b: Term) -> Term {
        self.require_same_width(a, b, "comparison");
        // Two literals compare to a literal, and the result is a *predicate*: a
        // one-bit constant, not one carrying the operand width. That distinction is
        // the whole point of the fold -- a comparison node stores its operands'
        // width (`Op::Eq` on two `u32` has width 32) even though it denotes one bit,
        // so leaving the folded node wide would hand a later width check a term of
        // the wrong shape. Returning the one-bit constant is what the blaster would
        // have computed, in one node instead of a chain of XOR/AND gates.
        //
        // This is what lets a *constant* dividend fold all the way through the
        // restoring divider: the loop's `ule(y, rem)` compares two literals at every
        // step, so with this fold the whole divider collapses to the quotient instead
        // of building `w` stages of adder and mux.
        let na = self.node_of(a);
        let nb = self.node_of(b);
        if na.op == Op::Const && nb.op == Op::Const && na.width == nb.width {
            let x = self.const_of(a);
            let y = self.const_of(b);
            let r = match op {
                Op::Eq => x == y,
                Op::Ult => x < y,
                Op::Ule => x <= y,
                _ => false,
            };
            return self.konst(u64::from(r), 1);
        }
        let w = self.width_of(a);
        self.mk_term(Node { op, a: a.0, b: b.0, c: 0, width: w, hi: 0 })
    }

    fn un_bool(&mut self, op: Op, a: Term) -> Term {
        if op == Op::Not {
            let n = self.node_of(a);
            // `!!p == p`. Both widths have to be 1. The inner `Not` is 1-bit by
            // construction, but its *child* need not be: a comparison node carries the
            // operand width (`Op::Eq` on two `u32` has width 32) even though it denotes a
            // single bit. Returning that child would hand the caller a wide term where a
            // predicate belongs, and a later `require_same_width` then marks the arena
            // ill-formed -- which turns a decidable query into `Unknown`.
            if n.op == Op::Not && n.width == 1 && self.width_of(Term(n.a)) == 1 {
                return Term(n.a);
            }
            // `!0 == 1`, `!1 == 0`.
            if n.op == Op::Const && n.width == 1 {
                return self.konst((n.a as u64) ^ 1, 1);
            }
        }
        self.mk_term(Node { op, a: a.0, b: 0, c: 0, width: 1, hi: 0 })
    }

    /// Change a term's width, keeping the low bits and zero-filling any new ones.
    ///
    /// Deliberately *not* constant-folded, though the value is computable. The
    /// frontend spells a *named* bound (`i8::MIN`) as `truncate(word(k, 64), w)`
    /// precisely so that it does *not* hash-cons with the literal `word(k, w)`:
    /// `i8::MIN` and `128i8` are the same eight bits, and the literal-range
    /// bookkeeping keys on the term id to tell a legal bound from an illegal
    /// literal. Folding a literal through `Trunc` merges the two and makes
    /// `y == i8::MIN` inherit `128i8`'s out-of-range envelope, so a valid contract
    /// is refused. Nothing is lost by leaving it: the folds that carry the
    /// divider's constant path are in [`Self::cmp`] and [`Self::bin_word`].
    fn trunc(&mut self, a: Term, width: u8) -> Term {
        let src = self.width_of(a);
        self.mk_term(Node {
            op: Op::Trunc,
            a: a.0,
            b: src as u32,
            c: 0,
            width,
            hi: 0,
        })
    }

    fn shift(&mut self, op: Op, a: Term, k: u32) -> Term {
        let w = self.width_of(a);
        self.mk_term(Node { op, a: a.0, b: k, c: 0, width: w, hi: 0 })
    }

    // ------------------------- ROBDD core -------------------------

    fn mk_node(&mut self, var: u32, lo: u32, hi: u32) -> u32 {
        if lo == hi {
            return lo;
        }
        let key = ((var as u64) << 32) | ((lo as u64) << 16) | (hi as u64);
        let mut i = (key as u32) & self.uniq_mask;
        // Open addressing over a table that cannot grow. If every slot is taken
        // no probe sequence can ever find `u64::MAX`, so the capacity check
        // below -- which lives *inside* that branch -- would never run and the
        // loop would spin forever. Bounding the probe makes a full table report
        // the budget instead.
        let mut probes = 0usize;
        loop {
            let k = self.uniq_key[i as usize];
            if k == u64::MAX {
                if self.n_nodes >= CAP {
                    self.overflow = true;
                    return FALSE;
                }
                let id = self.n_nodes as u32;
                self.n_nodes += 1;
                self.var[id as usize] = var;
                self.lo[id as usize] = lo;
                self.hi[id as usize] = hi;
                self.uniq_key[i as usize] = key;
                self.uniq_val[i as usize] = id;
                return id;
            }
            if k == key {
                return self.uniq_val[i as usize];
            }
            probes += 1;
            if probes > self.uniq_mask as usize {
                self.overflow = true;
                return FALSE;
            }
            i = (i + 1) & self.uniq_mask;
        }
    }

    fn top_var(&self, a: u32, b: u32) -> u32 {
        let va = self.var[a as usize];
        let vb = self.var[b as usize];
        if va == u32::MAX {
            return vb;
        }
        if vb == u32::MAX {
            return va;
        }
        if level_of(va) <= level_of(vb) {
            va
        } else {
            vb
        }
    }

    fn cofactors(&self, a: u32, v: u32) -> (u32, u32) {
        if a <= TRUE {
            return (a, a);
        }
        if self.var[a as usize] == v {
            (self.lo[a as usize], self.hi[a as usize])
        } else {
            (a, a)
        }
    }

    /// Logical complement of a BDD node.
    ///
    /// This *must* be memoised. Without a cache, `neg` walks the shared subgraph
    /// once per path, which is exponential in the number of shared nodes; a
    /// formula with a few thousand nodes then takes minutes instead of
    /// microseconds. The cache is a plain node-id keyed array.
    fn neg(&mut self, a: u32) -> u32 {
        match a {
            FALSE => TRUE,
            TRUE => FALSE,
            _ => {
                let key = (a as u64) << 1;
                let mut i = (key as u32) & self.uniq_mask;
                // Bounded like the other probes: a full cache is a miss, and the
                // complement is recomputed and re-stored below.
                let mut probes = 0usize;
                loop {
                    let k = self.not_key[i as usize];
                    if k == u64::MAX {
                        break;
                    }
                    if k == key {
                        return self.not_val[i as usize];
                    }
                    probes += 1;
                    if probes > self.uniq_mask as usize {
                        break;
                    }
                    i = (i + 1) & self.uniq_mask;
                }
                let v = self.var[a as usize];
                let lo = self.neg(self.lo[a as usize]);
                let hi = self.neg(self.hi[a as usize]);
                let r = self.mk_node(v, lo, hi);
                let mut j = (key as u32) & self.uniq_mask;
                let mut probes = 0usize;
                loop {
                    if self.not_key[j as usize] == u64::MAX || self.not_key[j as usize] == key {
                        self.not_key[j as usize] = key;
                        self.not_val[j as usize] = r;
                        break;
                    }
                    probes += 1;
                    if probes > self.uniq_mask as usize {
                        break;
                    }
                    j = (j + 1) & self.uniq_mask;
                }
                r
            }
        }
    }

    fn apply2(&mut self, op: u8, a: u32, b: u32) -> u32 {
        // The diagram recursion is bounded by `MAX_APPLY_STEPS` below, but that is a step
        // count and a deep diagram can be narrow. Guard the depth too; see `MAX_WALK_DEPTH`.
        self.walk_depth += 1;
        if self.walk_depth > MAX_WALK_DEPTH {
            self.overflow = true;
            self.walk_depth -= 1;
            return FALSE;
        }
        let r = self.apply2_bounded(op, a, b);
        self.walk_depth -= 1;
        r
    }

    /// [`Self::apply2`] with the depth already charged.
    fn apply2_bounded(&mut self, op: u8, a: u32, b: u32) -> u32 {
        // Charge the *diagram* recursion, not just the term-DAG walk `blast` charges. A
        // function whose BDD is exponentially larger than its formula (a wide division by a
        // non-power-of-two constant) blows up here, where `blast`'s counter never sees it;
        // without this the query never returns. Tripping sets `overflow`, which routes the
        // query to the SAT engine and from there to `Unknown`, exactly as the DAG budget and
        // the arena cap do -- so the answer stays sound and the call always returns.
        self.apply_steps = self.apply_steps.saturating_add(1);
        if self.apply_steps > MAX_APPLY_STEPS {
            self.overflow = true;
            return FALSE;
        }
        if op == 0 {
            if a == FALSE || b == FALSE {
                return FALSE;
            }
            if a == TRUE {
                return b;
            }
            if b == TRUE || a == b {
                return a;
            }
        } else if op == 1 {
            if a == TRUE || b == TRUE {
                return TRUE;
            }
            if a == FALSE {
                return b;
            }
            if b == FALSE || a == b {
                return a;
            }
        } else {
            if a == FALSE {
                return b;
            }
            if b == FALSE {
                return a;
            }
            if a == b {
                return FALSE;
            }
            if a == TRUE {
                return self.neg(b);
            }
            if b == TRUE {
                return self.neg(a);
            }
        }
        let (ka, kb) = if a < b { (a, b) } else { (b, a) };
        let key = ((ka as u64) << 32) | (kb as u64);
        if let Some(r) = self.cache_lookup(op, key) {
            return r;
        }

        let v = self.top_var(a, b);
        let (a_lo, a_hi) = self.cofactors(a, v);
        let (b_lo, b_hi) = self.cofactors(b, v);
        let lo = self.apply2(op, a_lo, b_lo);
        let hi = self.apply2(op, a_hi, b_hi);
        let r = self.mk_node(v, lo, hi);
        self.cache_store(op, key, r);
        r
    }

    fn cache_lookup(&self, op: u8, key: u64) -> Option<u32> {
        let (keys, vals): (&[u64], &[u32]) = match op {
            0 => (&self.and_key, &self.and_val),
            1 => (&self.or_key, &self.or_val),
            _ => (&self.xor_key, &self.xor_val),
        };
        let mut i = (key as u32) & self.uniq_mask;
        // These caches memoise `apply2`; they are not a source of truth, so a
        // full table is a *miss* and the answer is recomputed. Bounding the
        // probe keeps that true when no empty slot is left.
        let mut probes = 0usize;
        loop {
            let k = keys[i as usize];
            if k == u64::MAX {
                return None;
            }
            if k == key {
                return Some(vals[i as usize]);
            }
            probes += 1;
            if probes > self.uniq_mask as usize {
                return None;
            }
            i = (i + 1) & self.uniq_mask;
        }
    }

    fn cache_store(&mut self, op: u8, key: u64, val: u32) {
        let (keys, vals): (&mut [u64], &mut [u32]) = match op {
            0 => (&mut self.and_key, &mut self.and_val),
            1 => (&mut self.or_key, &mut self.or_val),
            _ => (&mut self.xor_key, &mut self.xor_val),
        };
        let mut i = (key as u32) & self.uniq_mask;
        // A full table drops the entry. Losing a memo costs time, never an
        // answer, and it must not become an unbounded probe.
        let mut probes = 0usize;
        loop {
            let k = keys[i as usize];
            if k == u64::MAX || k == key {
                keys[i as usize] = key;
                vals[i as usize] = val;
                return;
            }
            probes += 1;
            if probes > self.uniq_mask as usize {
                return;
            }
            i = (i + 1) & self.uniq_mask;
        }
    }

    fn and(&mut self, a: u32, b: u32) -> u32 {
        self.apply2(0, a, b)
    }
    fn or(&mut self, a: u32, b: u32) -> u32 {
        self.apply2(1, a, b)
    }
    fn xor(&mut self, a: u32, b: u32) -> u32 {
        self.apply2(2, a, b)
    }

    fn bit(&self, b: bool) -> u32 {
        if b {
            TRUE
        } else {
            FALSE
        }
    }

    fn ite_node(&mut self, c: u32, t: u32, e: u32) -> u32 {
        if c == TRUE {
            return t;
        }
        if c == FALSE {
            return e;
        }
        if t == e {
            return t;
        }
        if t == TRUE && e == FALSE {
            return c;
        }
        if t == FALSE && e == TRUE {
            return self.neg(c);
        }
        let a = self.and(c, t);
        let nc = self.neg(c);
        let b = self.and(nc, e);
        self.or(a, b)
    }

    // ------------------------- bit-blasting -------------------------

    /// The constant operand of a binary term, if exactly one is a `Const`.
    ///
    /// Both constant is deliberately `None`: the product would be constant, and
    /// folding it here would need the `w`-bit truncation this function does not
    /// have. Falling through to the schoolbook path is correct and rare.
    fn const_operand(&mut self, a: Term, b: Term) -> Option<u64> {
        let ca = self.node_of(a).op == Op::Const;
        let cb = self.node_of(b).op == Op::Const;
        if ca == cb {
            return None;
        }
        Some(self.const_value(if ca { a } else { b }))
    }

    /// The operand of a binary term that is *not* the constant one. The caller has
    /// established with [`Self::const_operand`] that exactly one is constant.
    fn other_operand(&mut self, a: Term, b: Term) -> Term {
        if self.node_of(a).op == Op::Const {
            b
        } else {
            a
        }
    }

    fn blast(&mut self, t: Term, out: &mut [u32; 64]) {
        // Bound the *depth* before the step budget, because a step budget cannot see a
        // stack overflow: a 262-level walk is a few hundred steps. See `MAX_WALK_DEPTH`.
        self.walk_depth += 1;
        if self.walk_depth > MAX_WALK_DEPTH {
            self.overflow = true;
            out.fill(FALSE);
            self.walk_depth -= 1;
            return;
        }
        self.blast_bounded(t, out);
        self.walk_depth -= 1;
    }

    /// [`Self::blast`] with the depth already charged. Split so the guard has one place to
    /// unwind from, which is what keeps `walk_depth` correct on the early returns below.
    fn blast_bounded(&mut self, t: Term, out: &mut [u32; 64]) {
        // Bound the work before doing any of it. See `MAX_BLAST_STEPS`: the memo below
        // makes the fold walks cheap, but only this counter makes the pass *guaranteed* to
        // end. Tripping it sets `overflow`, which routes the query to the SAT engine and
        // from there to `Unknown` -- never to a verdict about a half-built diagram.
        self.blast_steps = self.blast_steps.saturating_add(1);
        if self.blast_steps > MAX_BLAST_STEPS {
            self.overflow = true;
            out.fill(FALSE);
            return;
        }
        // Check `stale` first, so once any stale handle has been touched the whole
        // traversal stops. Checking only the current node is not enough: a constructor can
        // read a stale node and then *build* a current node that refers back to the stale
        // id, so the graph contains a cycle whose every node is current. Stopping the
        // whole traversal on the first stale touch is what breaks it.
        //
        // `overflow` is checked here for the same reason and it is not optional: once the
        // node table is full every `mk_node` returns `FALSE` *without* setting `overflow`
        // again, so nothing below this point can notice, and the traversal keeps recursing.
        // A term built by a fold (`pow`, the divider) is a DAG with heavy sharing, and
        // walking it to completion visits a shared subterm once per path to it -- millions
        // of times for a 32-step fold. That is not a slow answer, it is a hang: the query
        // never returns to the caller that would have fallen back to the SAT engine. The
        // check turns "the arena is full" into "stop now", and the caller's `overflow` test
        // then routes the query to the fallback.
        if self.stale || t.gen_bits() != self.gen_masked() {
            self.stale = true;
            out.fill(FALSE);
            return;
        }
        // `overflow` stops the walk too, but it is *not* `stale`: an overflowed arena is a
        // full one, not a wrong one, and the caller routes it to the SAT fallback rather
        // than refusing. Setting `stale` here would turn a fallback into a refusal and
        // would hide the SAT engine behind a query that never reaches it.
        if self.overflow {
            out.fill(FALSE);
            return;
        }
        let n = self.node_of(t);
        let w = n.width as usize;
        // The output buffer is `[u32; 64]`, so a term wider than a word cannot be
        // represented. `var`/`word`/`truncate` all bound their width, but a term reached
        // through a path that did not (or a future constructor that forgets) must be
        // *refused*, not allowed to index past the buffer: an out-of-range slice here
        // panicked inside the solver, which turns a malformed specification into an
        // unwind rather than an `Unknown`. Marking the query ill-formed keeps the
        // failure an answer.
        if w == 0 || w > 64 {
            self.ill_formed = true;
            out.fill(FALSE);
            return;
        }
        // The memo turns the shared-DAG walk from exponential into linear. See
        // `BLAST_MEMO_N`. A hit is always sound: the key is the term id, and identical ids
        // mean identical terms, whose blasted bits are deterministic.
        let memo_i = (t.0 as usize) & (BLAST_MEMO_N - 1);
        if self.blast_memo_key[memo_i] == t.0 {
            out[..w].copy_from_slice(&self.blast_memo_bits[memo_i][..w]);
            return;
        }
        match n.op {
            Op::Var => {
                let idx = n.a;
                for (bit, slot) in out[..w].iter_mut().enumerate() {
                    *slot = self.mk_node(bdd_var(idx, bit as u32), FALSE, TRUE);
                }
            }
            Op::Const => {
                let v = self.const_value(t);
                for (bit, slot) in out[..w].iter_mut().enumerate() {
                    *slot = self.bit((v >> bit) & 1 == 1);
                }
            }
            Op::Not => {
                let mut a = [FALSE; 64];
                self.blast(Term(n.a), &mut a);
                for bit in 0..w {
                    out[bit] = self.neg(a[bit]);
                }
            }
            Op::And | Op::Or | Op::Xor => {
                let mut a = [FALSE; 64];
                let mut b = [FALSE; 64];
                self.blast(Term(n.a), &mut a);
                self.blast(Term(n.b), &mut b);
                for bit in 0..w {
                    out[bit] = match n.op {
                        Op::And => self.and(a[bit], b[bit]),
                        Op::Or => self.or(a[bit], b[bit]),
                        _ => self.xor(a[bit], b[bit]),
                    };
                }
            }
            Op::Shl | Op::LShr | Op::Shr => {
                let mut a = [FALSE; 64];
                self.blast(Term(n.a), &mut a);
                let sh = n.b as usize;
                let sign = a[w - 1];
                for (bit, slot) in out[..w].iter_mut().enumerate() {
                    *slot = match n.op {
                        // `bit >= sh` is checked first so `bit - sh` cannot wrap.
                        Op::Shl if bit >= sh => a[bit - sh],
                        Op::Shl => FALSE,
                        // `sh < w - bit`, not `bit + sh < w`. The shift amount is
                        // a `u32` the user can write as `u32::MAX`; on a 32-bit
                        // target `bit + sh` overflows there, and a release build
                        // would then select `a[bit + sh]` -- reading an input bit
                        // where the result is defined to be zero. Comparing
                        // against `w - bit` (always in `1..=w`, since `bit < w`)
                        // keeps both sides small.
                        Op::LShr if sh < w - bit => a[bit + sh],
                        Op::LShr => FALSE,
                        // Arithmetic right shift replicates the sign bit.
                        _ if sh < w - bit => a[bit + sh],
                        _ => sign,
                    };
                }
            }
            Op::Add => {
                let mut a = [FALSE; 64];
                let mut b = [FALSE; 64];
                self.blast(Term(n.a), &mut a);
                self.blast(Term(n.b), &mut b);
                let mut carry = FALSE;
                for bit in 0..w {
                    let axb = self.xor(a[bit], b[bit]);
                    out[bit] = self.xor(axb, carry);
                    let ab = self.and(a[bit], b[bit]);
                    let cx = self.and(carry, axb);
                    carry = self.or(ab, cx);
                }
            }
            Op::Sub => {
                let mut a = [FALSE; 64];
                let mut b = [FALSE; 64];
                self.blast(Term(n.a), &mut a);
                self.blast(Term(n.b), &mut b);
                let mut borrow = TRUE; // a + ~b + 1
                for bit in 0..w {
                    let nb = self.neg(b[bit]);
                    let axb = self.xor(a[bit], nb);
                    out[bit] = self.xor(axb, borrow);
                    let ab = self.and(a[bit], nb);
                    let cx = self.and(borrow, axb);
                    borrow = self.or(ab, cx);
                }
            }
            Op::Mul => {
                // One constant operand makes this a sum of shifts instead of a
                // schoolbook multiply. `x * c` is `sum over the set bits k of c of
                // (x << k)`, which is *exact* -- it is the distributive law, not an
                // approximation -- and it is `popcount(c)` shift-adds rather than
                // `w^2` AND/XOR rows, so `x * 4` is one shift and `x * 255` is eight
                // additions where the multiply was 64 rows.
                //
                // This is the same shape the frontend's overflow predicate needs:
                // `i * 4`, an index scaled by an element size. It also makes the
                // *signed* case cheap, because the identity holds for a two's
                // complement word regardless of sign -- no widening is needed to
                // build the product, only to decide whether it wrapped.
                //
                // `c == 0` yields zero and `c == 1` yields `x` with no shifts at all.
                if let Some(c) = self.const_operand(Term(n.a), Term(n.b)) {
                    let operand = self.other_operand(Term(n.a), Term(n.b));
                    let mut x = [FALSE; 64];
                    self.blast(operand, &mut x);
                    // `c == 0` is the product zero, which is also what an accumulator
                    // left untouched would be -- but the shifts below never run for it,
                    // so the fill is what makes that case right rather than whatever the
                    // buffer happened to hold.
                    out[..w].fill(FALSE);
                    for k in 0..w as u32 {
                        if (c >> k) & 1 == 0 {
                            continue;
                        }
                        // `x << k` at width `w`: bits below `k` are zero, and the bits
                        // at and above `k` come from `x` at `bit - k`.
                        // A full adder, matching the schoolbook arm below: the sum is
                        // `out ^ shifted ^ carry`, and the carry out is
                        // `(out & shifted) | (carry & (out ^ shifted))`. Dropping the
                        // `^ carry` from the sum is the one-line version of this that
                        // looks right and is not -- it agrees whenever the accumulator
                        // bit and the shift agree, which is most of the time.
                        let mut carry = FALSE;
                        for bit in 0..w {
                            let shifted = if (bit as u32) < k { FALSE } else { x[bit - k as usize] };
                            let s1 = self.xor(out[bit], shifted);
                            let s2 = self.xor(s1, carry);
                            let c1 = self.and(out[bit], shifted);
                            let c2 = self.and(carry, s1);
                            carry = self.or(c1, c2);
                            out[bit] = s2;
                        }
                    }
                    // Only the low `w` bits of `c` can contribute: `x << k` for
                    // `k >= w` is zero at this width, which is the `0..w` bound above.
                } else {
                    let mut a = [FALSE; 64];
                    let mut b = [FALSE; 64];
                    self.blast(Term(n.a), &mut a);
                    self.blast(Term(n.b), &mut b);
                    out[..w].fill(FALSE);
                for j in 0..w {
                    let mut carry = FALSE;
                    for i in j..w {
                        let partial = self.and(a[i - j], b[j]);
                        let s1 = self.xor(out[i], partial);
                        let s2 = self.xor(s1, carry);
                        let c1 = self.and(out[i], partial);
                        let c2 = self.and(carry, s1);
                        carry = self.or(c1, c2);
                        out[i] = s2;
                    }
                }
                }
            }
            Op::Eq => {
                let mut a = [FALSE; 64];
                let mut b = [FALSE; 64];
                self.blast(Term(n.a), &mut a);
                self.blast(Term(n.b), &mut b);
                let mut acc = TRUE;
                for bit in 0..w {
                    let x = self.xor(a[bit], b[bit]);
                    let nx = self.neg(x);
                    acc = self.and(acc, nx);
                }
                out[0] = acc;
            }
            Op::Ult | Op::Ule => {
                let mut a = [FALSE; 64];
                let mut b = [FALSE; 64];
                self.blast(Term(n.a), &mut a);
                self.blast(Term(n.b), &mut b);
                let mut lt = FALSE;
                let mut eq = TRUE;
                for bit in (0..w).rev() {
                    let na = self.neg(a[bit]);
                    let nab = self.and(na, b[bit]);
                    let lt_here = self.and(eq, nab);
                    lt = self.or(lt, lt_here);
                    let x = self.xor(a[bit], b[bit]);
                    let e = self.neg(x);
                    eq = self.and(eq, e);
                }
                out[0] = if n.op == Op::Ule { self.or(lt, eq) } else { lt };
            }
            Op::Ite => {
                let mut c = [FALSE; 64];
                let mut t = [FALSE; 64];
                let mut e = [FALSE; 64];
                self.blast(Term(n.a), &mut c);
                self.blast(Term(n.b), &mut t);
                self.blast(Term(n.c), &mut e);
                for bit in 0..w {
                    out[bit] = self.ite_node(c[0], t[bit], e[bit]);
                }
            }
            Op::Trunc => {
                let mut a = [FALSE; 64];
                self.blast(Term(n.a), &mut a);
                let src = n.b as usize;
                for (bit, slot) in out[..w].iter_mut().enumerate() {
                    // Widening zero-fills; narrowing drops the high bits. One
                    // expression covers both because the source is only read
                    // where it exists.
                    *slot = if bit < src { a[bit] } else { FALSE };
                }
            }
        }
        // Memoise the result, but never after an overflow: an overflowed pass produced a
        // truncated diagram, and caching it would hand that truncation to a later query.
        if !self.overflow {
            self.blast_memo_key[memo_i] = t.0;
            self.blast_memo_bits[memo_i] = *out;
        }
    }

    fn blast_bool(&mut self, t: Term) -> u32 {
        let mut buf = [FALSE; 64];
        self.blast(t, &mut buf);
        buf[0]
    }

    // ------------------------- models -------------------------

    /// Walk from `root` to a terminal, collecting a bit assignment. When
    /// `want_false` is set we steer toward `FALSE` (a counterexample for a
    /// validity query); otherwise toward `TRUE` (a satisfying model).
    fn model(&self, root: u32, want_false: bool) -> Cex {
        let mut bits = [0u64; MAX_VARS];
        let mut touched = [false; MAX_VARS];
        let target = if want_false { FALSE } else { TRUE };
        let mut node = root;
        while node > TRUE {
            let v = self.var[node as usize];
            let idx = (v >> 6) as usize;
            let bit = v & 63;
            let lo = self.lo[node as usize];
            let hi = self.hi[node as usize];
            // Every variable on the path belongs in the model, including those
            // whose value is 0. Recording only the `hi` branches would silently
            // drop zero-valued variables and make `value_of` return `None`.
            touched[idx] = true;
            if lo == target {
                node = lo;
            } else if hi == target {
                bits[idx] |= 1u64 << bit;
                node = hi;
            } else if lo != TRUE && lo != FALSE {
                node = lo;
            } else {
                bits[idx] |= 1u64 << bit;
                node = hi;
            }
        }
        let mut cex = Cex { assignments: [(0, 0, 0); MAX_CEX], n: 0, total: 0 };
        for idx in 0..MAX_VARS {
            if touched[idx] {
                // Count every touched variable, whether or not it fits. The count is what
                // makes truncation visible: `n < total` means the witness has a hole, and
                // a caller that cannot see the hole will treat a partial model as a whole
                // one. The assignments that do fit are still recorded.
                cex.total += 1;
                if (cex.n as usize) < MAX_CEX {
                    let w = self.var_width[idx];
                    cex.assignments[cex.n as usize] = (idx as u32, w, bits[idx]);
                    cex.n += 1;
                }
            }
        }
        cex
    }

    fn query_valid(&mut self, t: Term) -> Verdict {
        self.blast_steps = 0;
        self.apply_steps = 0;
        self.sat_blast_steps = 0;
        self.walk_depth = 0;
        let node = self.blast_bool(t);
        if self.stale || self.ill_formed || self.var_overflow {
            return Verdict::Unknown;
        }
        if !self.overflow {
            return match node {
                TRUE => Verdict::Valid,
                FALSE => Verdict::Unsat,
                _ => Verdict::Counterexample(self.model(node, true)),
            };
        }
        // The BDD arena filled, so the diagram is a truncated approximation and cannot be
        // trusted for *either* verdict. The term graph itself is intact, so hand the same
        // query to the SAT engine, which does not have a canonical-form wall.
        self.query_valid_sat(t)
    }

    fn query_model(&mut self, t: Term) -> Verdict {
        self.blast_steps = 0;
        self.apply_steps = 0;
        self.sat_blast_steps = 0;
        self.walk_depth = 0;
        let node = self.blast_bool(t);
        if self.stale || self.ill_formed || self.var_overflow {
            return Verdict::Unknown;
        }
        if !self.overflow {
            return match node {
                TRUE => Verdict::Valid,
                FALSE => Verdict::Unsat,
                _ => Verdict::Counterexample(self.model(node, false)),
            };
        }
        self.query_model_sat(t)
    }

    /// `prove` via the SAT engine: the query is valid iff `!t` is unsatisfiable.
    ///
    /// Falls back to `Unknown` when the encoding itself overflows a capacity, because a
    /// truncated encoding proves nothing -- reporting `Valid` from one would be exactly the
    /// lie the BDD engine refuses to tell.
    fn query_valid_sat(&mut self, t: Term) -> Verdict {
        let mut enc_overflow = false;
        let (sat, model) = crate::sat::query(|cnf| {
            let mut bits = [cnf.false_lit(); crate::bitblast::MAX_BITS];
            crate::bitblast::blast(self, cnf, t, &mut bits);
            enc_overflow = cnf.overflowed();
            if enc_overflow {
                return cnf.true_lit();
            }
            bits[0].not()
        });
        // `ill_formed` is checked here too: the SAT blaster refuses an unrepresentable
        // width by marking the query, and a refusal has to outrank the verdict it produced.
        if enc_overflow || self.stale || self.ill_formed || self.var_overflow {
            return Verdict::Unknown;
        }
        match sat {
            crate::sat::Sat::Sat => Verdict::Counterexample(self.cex_from_sat(|i| model.bit(i))),
            crate::sat::Sat::Unsat => Verdict::Valid,
            crate::sat::Sat::Unknown => Verdict::Unknown,
        }
    }

    /// `find_model` via the SAT engine: satisfiable iff `t` is satisfiable.
    fn query_model_sat(&mut self, t: Term) -> Verdict {
        let mut enc_overflow = false;
        let (sat, model) = crate::sat::query(|cnf| {
            let mut bits = [cnf.false_lit(); crate::bitblast::MAX_BITS];
            crate::bitblast::blast(self, cnf, t, &mut bits);
            enc_overflow = cnf.overflowed();
            if enc_overflow {
                return cnf.true_lit();
            }
            bits[0]
        });
        if enc_overflow || self.stale || self.ill_formed || self.var_overflow {
            return Verdict::Unknown;
        }
        match sat {
            crate::sat::Sat::Sat => Verdict::Counterexample(self.cex_from_sat(|i| model.bit(i))),
            crate::sat::Sat::Unsat => Verdict::Unsat,
            crate::sat::Sat::Unknown => Verdict::Unknown,
        }
    }
}

// The proof engine needs a small amount of mutable global state. On `std` we
// use a thread-local so parallel tests do not interfere. On bare metal there is
// no `thread_local!`, so we fall back to a single static instance guarded by the
// caller's execution model (single-threaded interrupt context or an outer lock).
#[cfg(feature = "std")]
thread_local! {
    static CTX: RefCell<Ctx> = const { RefCell::new(Ctx::new()) };
}

#[cfg(feature = "std")]
pub(crate) fn with_ctx<R>(f: impl FnOnce(&mut Ctx) -> R) -> R {
    CTX.with(|c| {
        let mut c = c.borrow_mut();
        c.ensure_ready();
        f(&mut c)
    })
}

#[cfg(not(feature = "std"))]
static mut CTX: Ctx = Ctx::new();

#[cfg(not(feature = "std"))]
pub(crate) fn with_ctx<R>(f: impl FnOnce(&mut Ctx) -> R) -> R {
    // SAFETY: `CTX` is a `static mut`, so taking `&mut` to it is a promise that no other
    // reference to it exists. Two things carry that promise. First, `Ctx` is `!Send` and
    // `!Sync` (the `_not_shared` marker), so the arena cannot be shared across threads by
    // any safe code. Second, a bare-metal `no_std` build of this crate is single-threaded:
    // there is no second thread to race. What is left is re-entrancy from an interrupt on
    // the same core, which the type system cannot see -- a handler that runs a query while
    // main is inside one would alias `CTX`. That is the caller's obligation, and it is why
    // the crate documents wrapping queries in a critical section.
    unsafe {
        let ctx = &mut *core::ptr::addr_of_mut!(CTX);
        ctx.ensure_ready();
        f(ctx)
    }
}

/// Run `f` with a clean arena. Handy for tests and deterministic pipelines.
pub fn with_fresh<R>(f: impl FnOnce() -> R) -> R {
    with_ctx(|c| c.reset());
    f()
}

// NOTE: `with_fresh` must not be nested. The inner call wipes the arena, which
// invalidates every `Var` and `Pred` the enclosing scope is still holding. One
// `with_fresh` per proof.
//
// This used to be a warning only, and the warning was accurate about the symptom:
// reusing a stale handle was "use-after-free in the term arena, typically unbounded
// recursion rather than a clean panic". It is now enforced. Every term id *packs* the
// generation that created it into its high bits (see `Term`), the term accessors note a
// mismatch, and `blast`/`subst`/`eval_term` refuse to traverse a stale handle. A query
// that touches one returns `Unknown`, so nesting `with_fresh` degrades to "no answer"
// rather than "an answer about the wrong term" or a stack overflow.
//
// The generation lives *in the handle*, not in a side table keyed by slot. A side table
// cannot detect a recycled slot: the reset that recycles the slot is the same event that
// rewrites the stamp, so a stale handle would read a *current* stamp and be discharged as
// if it named its own term. Packing makes the comparison against the handle's own bits,
// which no later allocation can rewrite.
//
// The check lives in the arena rather than in each handle type on purpose: `Var`,
// `Pred`, `Mem`, `Query` and the rest all carry term ids, and a per-type stamp is one
// that a future type will forget. `proof::Certificate` and `proof::Implication` also
// stamp the generation, so they can refuse without touching the arena at all.

/// Reset the global arena.
pub fn reset() {
    with_ctx(|c| c.reset());
}

/// The current arena generation, bumped by every reset.
///
/// Term ids are recycled when the arena is reset, so a handle from one arena can name a
/// different term in the next. A [`Pred`] carries no generation of its own (it is a plain
/// handle, kept `Copy` and cheap), so anything that *stores* a handle for later use must
/// record this alongside it and re-check it before use. [`crate::proof::Certificate`] does
/// exactly that: a certificate is valid only in the arena that produced it.
pub fn generation() -> u32 {
    with_ctx(|c| c.generation)
}

/// Number of BDD nodes currently allocated, for diagnostics.
pub fn node_count() -> usize {
    with_ctx(|c| c.n_nodes)
}

/// Number of bit-vector terms currently allocated, for diagnostics.
pub fn term_count() -> usize {
    with_ctx(|c| c.n_terms)
}

// ---------------------------------------------------------------------------
// Public term API
// ---------------------------------------------------------------------------

/// A symbolic bit-vector of width 1..=64.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Var(pub(crate) Term);

impl Var {
    /// A placeholder, for initialising a fixed-size buffer of variables.
    ///
    /// Not a usable variable: comparing against it is a way to say "no variable
    /// here". It exists so that the frame computation needs no allocator.
    ///
    /// It is [`crate::smt::TERM_SENTINEL`], a term id the allocator never hands out, so
    /// it is distinguishable from every real variable. That is not decorative: the
    /// buffers in [`crate::wp`] are fixed-size and zero-initialised with this, and the
    /// reads are `[..n]`-counted, but the whole scheme assumes a sentinel cannot equal a
    /// live handle. When id 0 *was* the first real term, `Var::SENTINEL == var(8)` held.
    pub const SENTINEL: Var = Var(Term(TERM_SENTINEL));
}

/// A symbolic boolean predicate (a width-1 term).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Pred(pub(crate) Term);

impl fmt::Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let n = with_ctx(|c| c.node_of(self.0));
        write!(f, "u{}({})", n.width, n.a)
    }
}

/// Declare a symbolic variable of `width` bits. Indices are assigned in order.
pub fn var(width: u8) -> Var {
    assert!((1..=64).contains(&width), "width must be 1..=64");
    with_ctx(|c| {
        let idx = c.n_vars as u32;
        Var(c.var_term(idx, width))
    })
}

/// Declare a symbolic variable with an explicit index (readable models).
pub fn var_named(idx: u32, width: u8) -> Var {
    assert!((1..=64).contains(&width), "width must be 1..=64");
    assert!((idx as usize) < MAX_VARS, "index out of range");
    with_ctx(|c| Var(c.var_term(idx, width)))
}

/// Width of a symbolic word, in bits.
pub fn bits(v: Var) -> u8 {
    with_ctx(|c| c.width_of(v.0))
}

/// Evaluate a term under a concrete assignment, if every input is known.
///
/// This is the concrete semantics of the symbolic language, and it exists so that a
/// proof can be compared against what the terms actually *mean*. Two uses:
///
/// * [`crate::wp::verify`] decides the same terms with the bit-level engine. Any
///   disagreement between the two is a bug in one of them, and this makes that
///   disagreement observable.
/// * A counterexample reports values only for the variables the engine happened to
///   fix. Re-evaluating a term under that partial assignment turns a model into a
///   *checkable* claim: if the term is supposed to be false at the counterexample,
///   this says so without trusting the engine.
///
/// `value` answers with the value of a variable index, or `None` when it is unknown.
/// A term is evaluated only when every input it needs is known; otherwise the answer
/// is `None` rather than a guess.
///
/// Widths are honoured: results are masked to the term's own width, shifts are by the
/// constant amount stored in the node, and `Shr` is arithmetic (the sign bit
/// replicates), matching the bit-blaster exactly.
///
/// # Why this must not be inlined into a recursive caller
///
/// The [`EvalMemo`] is a local, and it is 12 KiB: `1024 * (4 + 8)` bytes. When the
/// optimiser inlines this function into a caller that *recurses*, that 12 KiB
/// temporary is allocated in the caller's frame and stays live for the whole
/// recursive descent, so one level of recursion costs 12 KiB of stack instead of a
/// few hundred bytes. The contract reader is exactly that caller -- `const_value`
/// is `evaluate`, and the parser calls it at every operator level -- and in a debug
/// build the frame grows to ~12.7 KiB per level, so `x >> ((2 << 7) + 1)` reached
/// past the 2 MiB a test thread gets and *aborted*. An abort is a crash in the
/// caller's process, not a refusal, which is the one thing the front end is not
/// allowed to do.
///
/// `#[inline(never)]` keeps the memo inside this frame, alive only for the walk.
/// Measured on the nested-amount contract, the parse depth falls from 254 KiB to
/// 15 KiB. It is deliberately not a `Box`: `no_std` without an allocator cannot
/// heap-allocate, so the memo has to be a stack local -- and being a stack local is
/// only safe once the function that owns it is not inlined into a recursion.
#[inline(never)]
pub fn evaluate(t: Var, value: impl Fn(u32) -> Option<u64>) -> Option<u64> {
    // The memo is local to this call, so it needs no invalidation: it cannot
    // outlive the assignment it was computed under, and a later call starts from
    // an empty table. It is bounded and small so that `Ctx` -- whose size the
    // crate budgets statically -- does not grow by an arena's worth of memo.
    let mut memo = EvalMemo::new();
    with_ctx(|c| eval_term(c, t.0, &value, &mut memo))
}

/// A bounded memo for one [`evaluate`] walk.
///
/// `eval_term` walks a term's DAG, and a term built by a fold (`pow`, the
/// divider) shares subterms heavily: without a memo the walk visits a shared
/// subterm once per path to it, which is exponential in the number of steps. It
/// is the same blow-up the BDD `neg` cache exists for, one layer up.
///
/// The table is direct-indexed by term slot with linear probing. A collision
/// evicts the older entry rather than failing, which is sound because a miss only
/// costs a recomputation -- the value is a pure function of the term and the
/// assignment. The size is a working-set estimate: a `pow` fold is a few hundred
/// terms, and the probe bound stops a pathological case from turning a memo miss
/// into a linear scan.
struct EvalMemo {
    /// Term slot, or [`EVAL_MEMO_EMPTY`] when the entry is free.
    slot: [u32; EVAL_MEMO_SLOTS],
    val: [u64; EVAL_MEMO_SLOTS],
}

const EVAL_MEMO_SLOTS: usize = 1024;
const EVAL_MEMO_EMPTY: u32 = u32::MAX;
/// How far a lookup probes before giving up. A miss recomputes; it never fails.
const EVAL_MEMO_PROBES: usize = 8;

impl EvalMemo {
    fn new() -> Self {
        EvalMemo { slot: [EVAL_MEMO_EMPTY; EVAL_MEMO_SLOTS], val: [0; EVAL_MEMO_SLOTS] }
    }

    fn get(&self, slot: u32) -> Option<u64> {
        let mut i = (slot as usize) & (EVAL_MEMO_SLOTS - 1);
        for _ in 0..EVAL_MEMO_PROBES {
            let k = self.slot[i];
            if k == EVAL_MEMO_EMPTY {
                return None;
            }
            if k == slot {
                return Some(self.val[i]);
            }
            i = (i + 1) & (EVAL_MEMO_SLOTS - 1);
        }
        None
    }

    fn put(&mut self, slot: u32, val: u64) {
        let mut i = (slot as usize) & (EVAL_MEMO_SLOTS - 1);
        for _ in 0..EVAL_MEMO_PROBES {
            if self.slot[i] == EVAL_MEMO_EMPTY || self.slot[i] == slot {
                self.slot[i] = slot;
                self.val[i] = val;
                return;
            }
            i = (i + 1) & (EVAL_MEMO_SLOTS - 1);
        }
        // Every probe in the window is taken by another slot; drop the entry.
        // Losing a memo costs time, never an answer.
    }
}

/// [`evaluate`] for a predicate. `None` when some input is unknown.
pub fn evaluate_pred(p: Pred, value: impl Fn(u32) -> Option<u64>) -> Option<bool> {
    evaluate(Var(p.0), value).map(|v| v != 0)
}

fn eval_term(
    ctx: &mut Ctx,
    t: Term,
    value: &impl Fn(u32) -> Option<u64>,
    memo: &mut EvalMemo,
) -> Option<u64> {
    if !ctx.is_current_term(t) {
        // A stale handle has no meaning to evaluate; `None` is "cannot say", which is
        // what `evaluate` already means by it.
        return None;
    }
    // This walk is the other recursion over a fold-built term, and it has the same failure
    // mode as the blasters: a chain of `2 * width` terms is a few hundred levels, which no
    // step budget sees and the stack cannot hold. See `MAX_WALK_DEPTH`. `None` is "cannot
    // say", which is sound here -- an unknown value can weaken a proof but never create
    // one.
    if ctx.charge_walk_depth() {
        ctx.release_walk_depth();
        return None;
    }
    let r = eval_term_inner(ctx, t, value, memo);
    ctx.release_walk_depth();
    r
}

fn eval_term_inner(
    ctx: &mut Ctx,
    t: Term,
    value: &impl Fn(u32) -> Option<u64>,
    memo: &mut EvalMemo,
) -> Option<u64> {
    let slot = t.slot() as u32;
    if let Some(v) = memo.get(slot) {
        return Some(v);
    }
    let v = eval_term_body(ctx, t, value, memo)?;
    memo.put(slot, v);
    Some(v)
}

fn eval_term_body(
    ctx: &mut Ctx,
    t: Term,
    value: &impl Fn(u32) -> Option<u64>,
    memo: &mut EvalMemo,
) -> Option<u64> {
    let n = ctx.node_of(t);
    let w = n.width;
    let mask = if w >= 64 { u64::MAX } else { (1u64 << w) - 1 };
    let v = match n.op {
        Op::Var => return value(n.a).map(|x| x & mask),
        Op::Const => (n.a as u64) | ((n.hi as u64) << 32),
        Op::Not => !eval_term(ctx, Term(n.a), value, memo)? & mask,
        Op::And => eval_term(ctx, Term(n.a), value, memo)? & eval_term(ctx, Term(n.b), value, memo)? & mask,
        Op::Or => eval_term(ctx, Term(n.a), value, memo)? | eval_term(ctx, Term(n.b), value, memo)? & mask,
        Op::Xor => eval_term(ctx, Term(n.a), value, memo)? ^ eval_term(ctx, Term(n.b), value, memo)? & mask,
        // The shift amount lives in the node, not in a term; see `shift`.
        Op::Shl => {
            let a = eval_term(ctx, Term(n.a), value, memo)?;
            let sh = n.b;
            if sh >= 64 {
                0
            } else {
                (a << sh) & mask
            }
        }
        Op::LShr => {
            let a = eval_term(ctx, Term(n.a), value, memo)?;
            let sh = n.b;
            if sh >= 64 {
                0
            } else {
                (a & mask) >> sh
            }
        }
        Op::Shr => {
            // Arithmetic: replicate the sign bit, matching the bit-blaster.
            let a = eval_term(ctx, Term(n.a), value, memo)? & mask;
            let sh = n.b;
            if sh >= w as u32 {
                if a >> (w - 1) & 1 == 1 {
                    mask
                } else {
                    0
                }
            } else {
                let sign_fill = if a >> (w - 1) & 1 == 1 { mask } else { 0 };
                (a >> sh) | (sign_fill & !(mask >> sh))
            }
        }
        Op::Add => eval_term(ctx, Term(n.a), value, memo)?.wrapping_add(eval_term(ctx, Term(n.b), value, memo)?) & mask,
        Op::Sub => eval_term(ctx, Term(n.a), value, memo)?.wrapping_sub(eval_term(ctx, Term(n.b), value, memo)?) & mask,
        Op::Mul => eval_term(ctx, Term(n.a), value, memo)?.wrapping_mul(eval_term(ctx, Term(n.b), value, memo)?) & mask,
        Op::Eq => {
            u64::from(eval_term(ctx, Term(n.a), value, memo)? == eval_term(ctx, Term(n.b), value, memo)?)
        }
        Op::Ult => {
            u64::from(eval_term(ctx, Term(n.a), value, memo)? < eval_term(ctx, Term(n.b), value, memo)?)
        }
        Op::Ule => {
            u64::from(eval_term(ctx, Term(n.a), value, memo)? <= eval_term(ctx, Term(n.b), value, memo)?)
        }
        Op::Ite => {
            let c = eval_term(ctx, Term(n.a), value, memo)?;
            if c != 0 {
                eval_term(ctx, Term(n.b), value, memo)?
            } else {
                eval_term(ctx, Term(n.c), value, memo)?
            }
        }
        Op::Trunc => {
            // Keep the low bits, zero-fill the rest.
            let a = eval_term(ctx, Term(n.a), value, memo)?;
            let src = n.b;
            if src >= 64 {
                a & mask
            } else {
                a & ((1u64 << src) - 1) & mask
            }
        }
    };
    Some(v & mask)
}

/// The numeric index of a symbolic variable (as shown in models).
pub fn index(v: Var) -> u32 {
    with_ctx(|c| c.node_of(v.0).a)
}

/// A word-shaped constant.
/// A constant of the given width.
///
/// `v` must fit in `width` bits. A constant that does not is a mistake in the
/// specification, not a value to wrap: `word(300, 8)` would otherwise be the same term as
/// `word(44, 8)`, and a DSL expression like `x + 300u32` on a `u8` would silently mean
/// `x + 44`. `eq_const` already refuses an out-of-range constant; this marks the term
/// instead, so the query answers `Unknown` rather than a verdict about a constant that was
/// never written. [`all_ones`] and [`truncate`] remain the ways to say "wrap on purpose".
///
/// `width` must be `1..=64`, like [`var`]. A wider one used to be accepted and to build a
/// term the blaster could not represent: the bit-blaster's buffers are `[u32; 64]`, so
/// `word(1, 65)` indexed `out[64]` and panicked *inside the solver* rather than being
/// refused. Marking the query ill-formed keeps the failure an answer (`Unknown`) instead
/// of an unwind, which is what every other malformed term in this crate does.
pub fn word(v: u64, width: u8) -> Var {
    with_ctx(|c| {
        if !(1..=64).contains(&width) {
            c.ill_formed = true;
        }
        if !fits(v, width) {
            c.ill_formed = true;
        }
        Var(c.konst(v, width))
    })
}

/// The largest value of the given width, i.e. every bit set.
///
/// This is the explicit spelling of the "all ones" idiom, so that `word(u64::MAX, 8)` --
/// which reads as a 64-bit constant but is the same term as `word(255, 8)` -- can go away.
/// A mask or a maximum should say what it is rather than rely on truncation.
pub fn all_ones(width: u8) -> Var {
    word(if width >= 64 { u64::MAX } else { (1u64 << width) - 1 }, width)
}

/// Whether `v` is representable in `width` bits.
fn fits(v: u64, width: u8) -> bool {
    width >= 64 || v < (1u64 << width)
}

/// `true` / `false`.
pub fn truth(b: bool) -> Pred {
    with_ctx(|c| Pred(c.konst(b as u64, 1)))
}

// --- boolean connectives ---------------------------------------------------

/// `a && b`
pub fn and(a: Pred, b: Pred) -> Pred {
    with_ctx(|c| Pred(c.bin_bool(Op::And, a.0, b.0)))
}
/// `a || b`
pub fn or(a: Pred, b: Pred) -> Pred {
    with_ctx(|c| Pred(c.bin_bool(Op::Or, a.0, b.0)))
}
/// `a ^ b`
pub fn xor(a: Pred, b: Pred) -> Pred {
    with_ctx(|c| Pred(c.bin_bool(Op::Xor, a.0, b.0)))
}
/// `!a`
pub fn not(a: Pred) -> Pred {
    with_ctx(|c| Pred(c.un_bool(Op::Not, a.0)))
}
/// `a => b`
pub fn implies(a: Pred, b: Pred) -> Pred {
    with_ctx(|c| {
        let na = c.un_bool(Op::Not, a.0);
        Pred(c.bin_bool(Op::Or, na, b.0))
    })
}
/// `a <=> b`
pub fn iff(a: Pred, b: Pred) -> Pred {
    with_ctx(|c| {
        let x = c.bin_bool(Op::Xor, a.0, b.0);
        Pred(c.un_bool(Op::Not, x))
    })
}
/// Conjunction of a slice.
pub fn all(preds: &[Pred]) -> Pred {
    with_ctx(|c| {
        let mut acc = c.konst(1, 1);
        for p in preds {
            acc = c.bin_bool(Op::And, acc, p.0);
        }
        Pred(acc)
    })
}
/// Disjunction of a slice.
pub fn any(preds: &[Pred]) -> Pred {
    with_ctx(|c| {
        let mut acc = c.konst(0, 1);
        for p in preds {
            acc = c.bin_bool(Op::Or, acc, p.0);
        }
        Pred(acc)
    })
}

// --- word comparisons and arithmetic --------------------------------------

/// `x == y`
pub fn eq(x: Var, y: Var) -> Pred {
    with_ctx(|c| Pred(c.cmp(Op::Eq, x.0, y.0)))
}
/// `x == k`
pub fn eq_const(x: Var, k: u64) -> Pred {
    with_ctx(|c| {
        let w = c.width_of(x.0);
        // A constant that cannot be represented in `w` bits makes the equality
        // unsatisfiable; say so instead of silently truncating `k`.
        if k > c.max_of(w) {
            return Pred(c.konst(0, 1));
        }
        let kt = c.konst(k, w);
        Pred(c.cmp(Op::Eq, x.0, kt))
    })
}
/// `x < y` (unsigned)
pub fn ult(x: Var, y: Var) -> Pred {
    with_ctx(|c| Pred(c.cmp(Op::Ult, x.0, y.0)))
}
/// `x <= y` (unsigned)
pub fn ule(x: Var, y: Var) -> Pred {
    with_ctx(|c| Pred(c.cmp(Op::Ule, x.0, y.0)))
}
/// The sign bit of `x` as a predicate: true when the top bit is set, which is
/// what "negative" means in two's complement.
pub fn negative(x: Var) -> Pred {
    let w = bits(x);
    // `x >= 2^(w-1)` is exactly "the top bit is set".
    uge_const(x, 1u64 << (w - 1))
}
/// Whether bit `k` of `x` is set. `k` is a *constant*, so bit 0 is the `& 1`
/// test and bit `k` is a constant shift followed by the same test.
///
/// A shift is used rather than a comparison against `2^k` because the two differ
/// at the top bit: `x >= 2^(w-1)` and `bit(w-1)` agree, but a reader that took
/// `x >= 2^k` as "bit `k`" would be right only up to the width, and the shift
/// spelling has no such edge. A `k` past the width yields `false` rather than a
/// shift the engine would have to define.
pub fn bit_set(x: Var, k: u32) -> Pred {
    let w = bits(x);
    if k >= u32::from(w) {
        return truth(false);
    }
    eq_const(band(lshr(x, k), word(1, w)), 1)
}
/// `x < y` (signed, two's complement).
///
/// The unsigned comparison next to this one is *wrong* for a signed operand, and
/// wrong in the direction that hides bugs: it calls `-1` larger than `1`. The
/// sign bits settle it -- equal signs mean the unsigned order is the signed
/// order, and differing signs mean the negative one is smaller -- so the
/// unsigned primitive is reused rather than a second ordering circuit built.
pub fn slt(x: Var, y: Var) -> Pred {
    let sx = negative(x);
    let sy = negative(y);
    let same = iff(sx, sy);
    or(and(same, ult(x, y)), and(not(same), sx))
}
/// `x <= y` (signed)
pub fn sle(x: Var, y: Var) -> Pred {
    not(slt(y, x))
}
/// `x > y` (signed)
pub fn sgt(x: Var, y: Var) -> Pred {
    slt(y, x)
}
/// `x >= y` (signed)
pub fn sge(x: Var, y: Var) -> Pred {
    not(slt(x, y))
}
/// `x < k`
pub fn ult_const(x: Var, k: u64) -> Pred {
    with_ctx(|c| {
        let w = c.width_of(x.0);
        if k > c.max_of(w) {
            // every `w`-bit value is below an out-of-range bound
            return Pred(c.konst(1, 1));
        }
        let kt = c.konst(k, w);
        Pred(c.cmp(Op::Ult, x.0, kt))
    })
}
/// `x <= k`
pub fn ule_const(x: Var, k: u64) -> Pred {
    with_ctx(|c| {
        let w = c.width_of(x.0);
        if k > c.max_of(w) {
            return Pred(c.konst(1, 1));
        }
        let kt = c.konst(k, w);
        Pred(c.cmp(Op::Ule, x.0, kt))
    })
}
/// `x > k` (unsigned)
pub fn ugt_const(x: Var, k: u64) -> Pred {
    with_ctx(|c| {
        let w = c.width_of(x.0);
        if k >= c.max_of(w) {
            // nothing exceeds the maximum representable value
            return Pred(c.konst(0, 1));
        }
        let kt = c.konst(k, w);
        Pred(c.cmp(Op::Ult, kt, x.0))
    })
}
/// `x >= k` (unsigned)
pub fn uge_const(x: Var, k: u64) -> Pred {
    with_ctx(|c| {
        let w = c.width_of(x.0);
        if k > c.max_of(w) {
            return Pred(c.konst(0, 1));
        }
        let kt = c.konst(k, w);
        Pred(c.cmp(Op::Ule, kt, x.0))
    })
}
/// `x / c` and `x % c` for a constant `c` whose magnitude is a power of two.
///
/// This exists because the *signed* divider is a BDD wall at 64 bits, and it is not the
/// divider that costs -- the unsigned `divmod` blasts a constant divisor in milliseconds.
/// The cost is the sign fixup in [`sdivmod`]: it negates and selects on a 64-bit value
/// whose bits are the divider's symbolic output, which is the shape that blows the
/// diagram up. Measured on the pinned-quotient query, `udiv(x, 2)` at 64 bits is 47ms and
/// `sdiv(x, 2)` is 9.3 seconds, so a signed `a / 2` -- the shape that actually appears in
/// code -- was reported `incomplete`.
///
/// Dividing by `2^k` needs neither of those. On the positive side it is a shift. On the
/// negative side it is a shift after adding `2^k - 1`, which turns truncation toward zero
/// into a floor: `trunc(x / 2^k) == floor((x + (2^k - 1 if x < 0 else 0)) / 2^k)`, and an
/// arithmetic shift *is* that floor. The bias is `(2^k - 1)` masked by the sign, and the
/// sign mask is the sign bit replicated, which is one arithmetic shift by `w - 1`.
///
/// So the whole thing is constant shifts, a `band`, an `add`, a `sub` and (for a negative
/// `c`) a negation -- no divider, no `ite` over a symbolic value. The remainder is
/// `x - q * 2^k`, and it needs no sign fixup at all: `x % -c == x % c`, because a
/// remainder takes the dividend's sign.
///
/// `|c| >= 2` is required, and that is what makes this safe to use rather than merely
/// fast: `MIN / c` is representable for every such `c`, so this path can never disagree
/// with the overflow the signed divider reports. `|c| == 1` is left out on purpose --
/// `x / -1` overflows at `MIN` and is the one constant where the general path's explicit
/// handling is wanted -- and `c == 0` is a different obligation entirely.
pub fn sdivmod_pow2(x: Var, c: i128, w: u8) -> Option<(Var, Var)> {
    let d = c.unsigned_abs();
    if d < 2 || !d.is_power_of_two() {
        return None;
    }
    let k = d.trailing_zeros();
    if k >= u32::from(w) {
        return None;
    }
    // `d <= 2^(w-1)` for any representable `c`, so `d - 1` fits in `w` bits.
    let mask = word((d - 1) as u64, w);
    // All-ones when `x` is negative, zero otherwise: the sign bit replicated across
    // the word by one arithmetic shift.
    let sign_mask = ashr(x, u32::from(w) - 1);
    let biased = add(x, band(sign_mask, mask));
    // `trunc(x / |c|)`. The remainder is built from *this* and not from the sign-fixed
    // quotient: `x % c == x % |c|` for every `c`, since a remainder takes the dividend's
    // sign, so negating first would flip it.
    let magnitude_quotient = ashr(biased, k);
    let quotient = if c < 0 {
        sub(word(0, w), magnitude_quotient)
    } else {
        magnitude_quotient
    };
    let remainder = sub(x, shl(magnitude_quotient, k));
    Some((quotient, remainder))
}

/// `x / 2^k` and `x % 2^k`, *unsigned*, as a logical shift and a mask.
///
/// The unsigned twin of [`sdivmod_pow2`], and it is simpler for the reason the signed one
/// is expensive: there is no sign to fix up. Truncating division of an unsigned value by
/// `2^k` *is* the logical shift `x >> k`, and the remainder is the low `k` bits, `x &
/// (2^k - 1)`. No divider, no bias, no negation -- two operators.
///
/// This exists because the general [`divmod`] blasts a restoring divider whose term is
/// ~`2 * w` deep, and an obligation that reads a *symbolic* dividend through it is refused
/// for the size of the diagram: `requires: n <= 1000; n / 4` at `u64` was `incomplete` in
/// ~0.9 s, while the same body with a signed `n` was already decided by the signed fast
/// path. The shift identity costs a handful of terms.
///
/// `d >= 2` is required rather than `d >= 1`, matching [`sdivmod_pow2`]. It is a
/// convenience and not a soundness need -- `x / 1` and `x % 1` are `x` and `0` for any
/// unsigned `x`, with no overflow to worry about -- and leaving `1` to the general path
/// keeps the two functions' guards identical. `d == 0` is excluded by the power-of-two
/// test, so a division by zero never reaches here.
pub fn udivmod_pow2(x: Var, d: u64, w: u8) -> Option<(Var, Var)> {
    if d < 2 || !d.is_power_of_two() {
        return None;
    }
    let k = d.trailing_zeros();
    if k >= u32::from(w) {
        return None;
    }
    // `d <= 2^(w-1)` for any `d` that fits in `w` bits, so `d - 1` is a `w`-bit mask.
    Some((lshr(x, k), band(x, word(d - 1, w))))
}

/// `x / y` and `x % y`, unsigned, as a *restoring divider* built from the
/// operators the engine already has.
///
/// Division used to be absent from the vocabulary, which meant a frontend reading
/// real code had to refuse `a / b` -- and the MIR frontend does refuse what it
/// cannot model. But division is not actually out of reach: a restoring divider
/// is nothing but shifts by constants, a subtract, a compare and a select, all of
/// which are here. Building it costs `w` steps and `O(w)` terms, and it is exact,
/// so a proof that goes through it is a real proof about `a / b`.
///
/// Two cases, and the split is what keeps it sound. If `y` has its top bit set
/// then `x < 2^w <= 2y`, so the quotient is 0 or 1 and the remainder is `x` or
/// `x - y`. Otherwise `y < 2^(w-1)`, so a running remainder that stays below `y`
/// can be doubled without losing its top bit -- which is exactly what the
/// restoring loop needs, and exactly what would break if the wide case were run
/// through the same loop.
///
/// `y == 0` is given a defined result rather than being left as a trap: the
/// quotient is all ones and the remainder is `x`. That keeps the function total,
/// which matters because an undefined operation in a verifier is a hole. Callers
/// that want Rust's panic on division by zero must state `y != 0` -- and the MIR
/// frontend does, because `rustc` emits that assert for them.
pub fn divmod(x: Var, y: Var) -> (Var, Var) {
    let w = bits(x);
    // Two literals divide to two literals. The restoring loop below is *exact*, so
    // this is not a shortcut past the semantics -- it is the same answer the loop
    // computes, reached without building `w` stages of adder and mux. That matters
    // because the loop is what makes the query too big to *pose* when nothing about
    // it is unknown: `-7 / 3` under `requires: a == -7` is a query with no symbolic
    // input at all, and it was reported `Unknown` purely for the size of its own
    // circuit. `y == 0` keeps the same defined result as the general path.
    if let (Some(xv), Some(yv)) = (const_of(x), const_of(y)) {
        let mask = if w >= 64 { u64::MAX } else { (1u64 << w) - 1 };
        let xv = xv & mask;
        let yv = yv & mask;
        if yv == 0 {
            return (all_ones(w), word(xv, w));
        }
        return (word(xv / yv, w), word(xv % yv, w));
    }
    if w == 1 {
        // 1-bit: for a nonzero divisor the quotient is `x & y` and the remainder
        // is `x & !y`. The `y == 0` case still has to go through the same
        // definition as every other width, or this fast path would disagree with
        // the general one at exactly the input the contract calls out.
        let y_zero = eq_const(y, 0);
        let q = ite(y_zero, all_ones(1), band(x, y));
        let r = ite(y_zero, x, band(x, bxor(y, all_ones(1))));
        return (q, r);
    }
    let zero = word(0, w);
    let one = word(1, w);
    // Does `y` have its top bit set?
    let top = word(1u64 << (w - 1), w);
    let y_top_set = not(eq_const(band(y, top), 0));
    let y_zero = eq_const(y, 0);

    // Wide divisor: quotient is 0 or 1.
    let ge = ule(y, x);
    let q_wide = ite(ge, one, zero);
    let r_wide = ite(ge, sub(x, y), x);

    // Narrow divisor: the restoring loop. The remainder stays below `y`, so
    // `rem << 1` cannot lose a bit.
    let mut rem = zero;
    let mut quot = zero;
    let mut i = w;
    while i > 0 {
        i -= 1;
        let bit = band(lshr(x, i as u32), one);
        rem = bor(shl(rem, 1), bit);
        let enough = ule(y, rem);
        rem = ite(enough, sub(rem, y), rem);
        quot = ite(enough, bor(quot, word(1u64 << i, w)), quot);
    }

    let q = ite(y_zero, all_ones(w), ite(y_top_set, q_wide, quot));
    let r = ite(y_zero, x, ite(y_top_set, r_wide, rem));
    (q, r)
}

/// `x / y`, unsigned. See [`divmod`] for the semantics, including `y == 0`.
pub fn udiv(x: Var, y: Var) -> Var {
    divmod(x, y).0
}

/// `x % y`, unsigned. See [`divmod`] for the semantics, including `y == 0`.
pub fn urem(x: Var, y: Var) -> Var {
    divmod(x, y).1
}

/// Interpret the low `w` bits of `v` as a two's-complement signed value.
///
/// Used only by the constant path of [`sdivmod`]; the symbolic path never needs it
/// because the sign lives in the bit pattern and the circuits handle it.
fn signed_value(v: u64, w: u8) -> i128 {
    let masked = if w >= 64 { v } else { v & ((1u64 << w) - 1) };
    if w >= 64 {
        masked as i64 as i128
    } else if masked & (1u64 << (w - 1)) != 0 {
        masked as i128 - (1i128 << w)
    } else {
        masked as i128
    }
}

/// `x / y` and `x % y`, *signed*, two's complement, truncating toward zero.
///
/// The unsigned divider computes a non-negative quotient from non-negative
/// operands, so the signed case reduces to it once the operands are made
/// non-negative and the signs of the results are put back. Rust truncates toward
/// zero, so the remainder takes the *dividend's* sign.
///
/// The overflow case, `MIN / -1`, is given a defined value -- `MIN`, matching the
/// wrapping result Rust would produce if the operation were unchecked -- rather
/// than being left as a hole. rustc guards it with its own `assert`, so a path
/// that reaches the division with that pair is already a reported panic; defining
/// it keeps the function total, exactly as `y == 0` is handled. `-1` is a
/// nonzero divisor here, so the two holes are independent.
pub fn sdivmod(x: Var, y: Var) -> (Var, Var) {
    let w = bits(x);
    // Two literals divide to two literals, signed and truncating toward zero --
    // Rust's own `/` and `%` on `i128`, which is exact for every width the engine
    // models. The general path below is the definition; this is that definition
    // reached without building the magnitudes, the divider and the sign fixups.
    // Without it a *fully literal* query such as `-7 / 3` still builds the whole
    // circuit, and the circuit is what gets the query refused for size rather than
    // for anything being unknown. The three special cases are the general path's:
    // `y == 0` is all-ones with the dividend as remainder, and `MIN / -1` is `MIN`.
    if let (Some(xv), Some(yv)) = (const_of(x), const_of(y)) {
        let sx = signed_value(xv, w);
        let sy = signed_value(yv, w);
        if sy == 0 {
            return (all_ones(w), x);
        }
        let min = -(1i128 << (w - 1));
        if sx == min && sy == -1 {
            return (word(1u64 << (w - 1), w), word(0, w));
        }
        // Mask before `word`: a negative quotient is a full-width two's-complement
        // pattern, and `word` rejects a value that does not fit its width -- the
        // check that catches a caller's modelling mistake. The pattern is the
        // answer here, so it is narrowed to the width it denotes rather than
        // handed over un-masked.
        let mask = if w >= 64 { u64::MAX } else { (1u64 << w) - 1 };
        let q = (sx / sy) as u64 & mask;
        let r = (sx % sy) as u64 & mask;
        return (word(q, w), word(r, w));
    }
    let zero = word(0, w);
    let nx = negative(x);
    let ny = negative(y);
    // Magnitudes as unsigned values. Negating `MIN` wraps back to `MIN`, whose
    // bit pattern *is* the magnitude `2^(w-1)`, so the plain wrapping subtract
    // is already the right magnitude for every input.
    let ax = ite(nx, sub(zero, x), x);
    let ay = ite(ny, sub(zero, y), y);
    let (q, r) = divmod(ax, ay);
    // Truncation toward zero: the quotient is negative when the signs differ,
    // and the remainder takes the *dividend's* sign. Getting the remainder's
    // sign backwards is a wrong value, not a weak proof -- `-127 % 3` is `-1`,
    // and `1` is a different number.
    let q = ite(iff(nx, ny), q, sub(zero, q));
    let r = ite(nx, sub(zero, r), r);
    // `y == 0` is given the same defined value as the unsigned divider: the
    // quotient is all ones and the remainder is the dividend. The unsigned
    // `divmod` already does that, but its inputs here are *magnitudes*, so the
    // remainder would come back as `|x|` and the sign fixup above would turn it
    // into `-x`. Overriding both explicitly keeps the signed zero case equal to
    // the unsigned one rather than one sign away from it.
    let is_zero = eq(y, zero);
    let q = ite(is_zero, all_ones(w), q);
    let r = ite(is_zero, x, r);
    // `MIN / -1` wraps to `MIN` with remainder 0; select it explicitly.
    let min = word(1u64 << (w - 1), w);
    let minus_one = all_ones(w);
    let overflow = and(eq(x, min), eq(y, minus_one));
    (ite(overflow, min, q), ite(overflow, zero, r))
}

/// `x / y`, signed. See [`sdivmod`].
pub fn sdiv(x: Var, y: Var) -> Var {
    sdivmod(x, y).0
}

/// `x % y`, signed. See [`sdivmod`].
pub fn srem(x: Var, y: Var) -> Var {
    sdivmod(x, y).1
}

/// `x + y == z`
pub fn add_eq(x: Var, y: Var, z: Var) -> Pred {
    with_ctx(|c| {
        let s = c.bin_word(Op::Add, x.0, y.0);
        Pred(c.cmp(Op::Eq, s, z.0))
    })
}
/// `x - y == z`
pub fn sub_eq(x: Var, y: Var, z: Var) -> Pred {
    with_ctx(|c| {
        let s = c.bin_word(Op::Sub, x.0, y.0);
        Pred(c.cmp(Op::Eq, s, z.0))
    })
}
/// `x * y == z`
pub fn mul_eq(x: Var, y: Var, z: Var) -> Pred {
    with_ctx(|c| {
        let s = c.bin_word(Op::Mul, x.0, y.0);
        Pred(c.cmp(Op::Eq, s, z.0))
    })
}
/// The constant value of `v`, when `v` is a literal.
///
/// `None` for anything else. The MIR frontend uses this to keep a shift by a
/// *constant* amount on the cheap `Op::Shl` path instead of paying for a barrel
/// shifter; both paths agree, but only one of them is free. `pow_fold` uses it for
/// the same reason: a constant exponent lets the fold skip the steps that cannot
/// run instead of building them behind a zero gate. The divider's constant paths
/// ([`divmod`], [`sdivmod`]) use it too, which is why it is *not* gated on `std`:
/// those run at every build, including bare metal.
pub(crate) fn const_of(v: Var) -> Option<u64> {
    with_ctx(|c| {
        let n = c.node_of(v.0);
        if n.op == Op::Const {
            Some(c.const_value(v.0))
        } else {
            None
        }
    })
}

/// `x + y` as a word.
pub fn add(x: Var, y: Var) -> Var {
    with_ctx(|c| Var(c.bin_word(Op::Add, x.0, y.0)))
}
/// `x - y` as a word.
pub fn sub(x: Var, y: Var) -> Var {
    with_ctx(|c| Var(c.bin_word(Op::Sub, x.0, y.0)))
}
/// `x * y` as a word.
pub fn mul(x: Var, y: Var) -> Var {
    with_ctx(|c| Var(c.bin_word(Op::Mul, x.0, y.0)))
}
/// `x & y`
pub fn band(x: Var, y: Var) -> Var {
    with_ctx(|c| Var(c.bin_word(Op::And, x.0, y.0)))
}
/// `x | y`
pub fn bor(x: Var, y: Var) -> Var {
    with_ctx(|c| Var(c.bin_word(Op::Or, x.0, y.0)))
}
/// `x ^ y`
pub fn bxor(x: Var, y: Var) -> Var {
    with_ctx(|c| Var(c.bin_word(Op::Xor, x.0, y.0)))
}
/// `x` widened to `wide` bits by replicating its sign bit.
///
/// A *value* operation, unlike [`truncate`], which zero-fills. The difference is
/// the whole of signed multiplication: zero-extending `-1` to 16 bits gives `255`
/// rather than `65535`, and a product computed from the wrong magnitude is a
/// product that misses its overflow. Built from shifts the engine already has:
/// move the `w` significant bits to the top of the wide word, then bring them
/// back with the sign fill.
pub fn sign_extend(x: Var, wide: u8) -> Var {
    let w = bits(x);
    if wide <= w {
        return truncate(x, wide);
    }
    let sh = (wide - w) as u32;
    ashr(shl(truncate(x, wide), sh), sh)
}

/// `x << k`
pub fn shl(x: Var, k: u32) -> Var {
    with_ctx(|c| Var(c.shift(Op::Shl, x.0, k)))
}
/// `x >> k` (logical)
pub fn lshr(x: Var, k: u32) -> Var {
    with_ctx(|c| Var(c.shift(Op::LShr, x.0, k)))
}
/// `x >> k` (arithmetic)
pub fn ashr(x: Var, k: u32) -> Var {
    with_ctx(|c| Var(c.shift(Op::Shr, x.0, k)))
}

/// Which shift `x << n` / `x >> n` with a *variable* amount means.
///
/// `Shr` is arithmetic for a signed operand and logical for an unsigned one, and
/// the bit pattern does not say which, so the caller states it rather than the
/// engine guessing. The constant-amount functions above are the same three
/// operations at a fixed amount.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Shift {
    /// `x << n`. Zero fill from the low end.
    Left,
    /// `x >> n` on an unsigned value. Zero fill from the high end.
    LogicalRight,
    /// `x >> n` on a signed value. The sign bit is replicated.
    ArithmeticRight,
}

/// `x << n`, `x >> n` (logical) or `x >> n` (arithmetic) with a *symbolic* amount.
///
/// A barrel shifter: `log2(w)` stages of select, each conditionally shifting by one
/// power of two, driven by one bit of `n`. `u16` costs 4 stages, `u64` costs 6, and
/// the cost is linear in the width rather than quadratic, which is what keeps it
/// inside the BDD arena where a `w`-bit multiplier is not.
///
/// # The out-of-range amount
///
/// `n >= w` has a *defined* result here — zero for [`Shift::Left`] and
/// [`Shift::LogicalRight`], sign fill for [`Shift::ArithmeticRight`] — rather than
/// being left unknown. That is the same choice [`divmod`] makes for `y == 0`, and
/// for the same reason: rustc guards a variable shift with `assert(n < w)`, so a
/// path that reaches the shift out of range has already been reported as a panic,
/// and a value left unknown here would refuse every function that shifts by a
/// variable rather than by a literal.
pub fn shift_var(op: Shift, x: Var, n: Var) -> Var {
    with_ctx(|c| {
        let w = c.width_of(x.0);
        let hop = match op {
            Shift::Left => Op::Shl,
            Shift::LogicalRight => Op::LShr,
            Shift::ArithmeticRight => Op::Shr,
        };
        // The amount is tested in *its own* width, not the value's. `_1 >> _2`
        // where `_1: u8` and `_2: u32` is the ordinary shape -- Rust takes the
        // shift amount as any integer type -- and building the mask at the
        // value's width made `n & mask` mix 32 bits with 8, which is ill-formed
        // and refused the whole function. `n`'s width is at least the `log2(w)`
        // bits the stages read for every real shift-amount type, so no bit is
        // lost; an amount *narrower* than the value is the case the mask has to
        // be read from, and it is read from `n`.
        let nw = c.width_of(n.0);
        let mut acc = x;
        let mut i = 0u32;
        while (1u32 << i) < w as u32 {
            let amt = 1u32 << i;
            // Bit `i` of `n`, as `(n & 2^i) == 2^i`. Testing the masked value
            // against the mask avoids needing a bit-extraction primitive.
            let mask = c.konst(amt as u64, nw);
            let masked = c.bin_word(Op::And, n.0, mask);
            let bit = c.cmp(Op::Eq, masked, mask);
            let shifted = c.shift(hop, acc.0, amt);
            acc = Var(c.mk_term(Node { op: Op::Ite, a: bit.0, b: shifted.0, c: acc.0.0, width: w, hi: 0 }));
            i += 1;
        }
        // The stages above only read the low `ceil(log2(w))` bits of `n`, so an
        // amount at or above the width -- which sets a higher bit that no stage
        // covers -- would otherwise come out as the identity. Select the defined
        // out-of-range value explicitly. Without this, `x << 4` at 4 bits returns
        // `x`, which is neither the documented value nor anything Rust does;
        // `tests/shift.rs` pins it.
        // `w <= 64` and every shift-amount type is at least 8 bits wide, so this
        // constant is exact in `n`'s width rather than truncated.
        let wt = c.konst(w as u64, nw);
        let in_range = c.cmp(Op::Ult, n.0, wt);
        let oor = match op {
            // An arithmetic shift by `w - 1` replicates the sign bit across the
            // whole word, which is exactly the sign fill.
            Shift::ArithmeticRight => c.shift(Op::Shr, x.0, (w - 1) as u32),
            _ => c.konst(0, w),
        };
        Var(c.mk_term(Node { op: Op::Ite, a: in_range.0, b: acc.0.0, c: oor.0, width: w, hi: 0 }))
    })
}

/// `x` re-typed to `width` bits: low bits kept, high bits zero-filled or dropped.
/// The one operation in the language that changes a width. It is what makes an
/// index wider than its address space expressible, which a loop over addresses
/// needs: see [`crate::mem::Mem::addr_of`].
///
/// # Panics
///
/// If `width` is not in `1..=64`. Shrinking never loses information silently —
/// the dropped bits are gone by definition, and that is the point of the
/// operation — but a caller who wants to be sure nothing is dropped should check
/// `x < 2^width` first.
pub fn truncate(x: Var, width: u8) -> Var {
    assert!((1..=64).contains(&width), "width must be 1..=64");
    with_ctx(|c| Var(c.trunc(x.0, width)))
}

/// `c ? t : e`
pub fn ite(c: Pred, t: Var, e: Var) -> Var {
    with_ctx(|c_| {
        c_.require_same_width(t.0, e.0, "ite branches");
        let w = c_.width_of(t.0);
        // A literal condition selects a branch: the term is that branch, not a mux
        // with a constant selector. This is what lets a constant-pinned dividend
        // reach the divider's constant path instead of building the general loop.
        let cn = c_.node_of(c.0);
        if cn.op == Op::Const {
            return if c_.const_of(c.0) != 0 { t } else { e };
        }
        Var(c_.mk_term(Node { op: Op::Ite, a: c.0.0, b: t.0.0, c: e.0.0, width: w, hi: 0 }))
    })
}

// --- queries ---------------------------------------------------------------
/// Prove `p` holds for every input.
pub fn prove(p: Pred) -> Verdict {
    with_ctx(|c| c.query_valid(p.0))
}

/// Whether the arena currently holds an *ill-formed* term: a binary operation over
/// operands of different widths, a constant that does not fit its width, or two bindings
/// for the same substitution target.
///
/// Such a query answers [`Verdict::Unknown`], never a wrong verdict. This accessor exists
/// for the *exporter*: a term the engine refuses still has a tree, and printing that tree
/// produces SMT-LIB2 that no solver accepts -- `(bvadd x0_12 x1_8)` is ill-sorted, and z3
/// rejects the file outright. So the export has to check the same flag the engine does, or
/// it would hand a reviewer an artifact that cannot be checked and looks like a failed
/// proof rather than a refused term.
pub fn is_ill_formed() -> bool {
    with_ctx(|c| c.ill_formed)
}

/// Whether `p` is a closed predicate that evaluates to true.
///
/// The [`EvalMemo`] is a 12 KiB local, so it lives here rather than in
/// [`prove_implies`]: `#[inline(never)]` keeps that temporary inside this frame and
/// alive only for the walk, the same reason [`evaluate`] is marked so. `prove_implies`
/// is not itself recursive, but it is called from the executor and from the macro
/// expansion, and a 12 KiB frame that the optimiser is free to hoist into a caller is
/// exactly the stack cost the crate budgets for elsewhere.
///
/// `false` means "not this arm", never "false theorem": an open term, a closed false
/// term, an ill-formed arena and a stale handle all return `false` and send the caller
/// to the engine. So a wrong `false` can only lose a proof, never invent one.
#[inline(never)]
fn goal_is_closed_true(ctx: &mut Ctx, p: Term) -> bool {
    if ctx.ill_formed || ctx.var_overflow {
        return false;
    }
    let mut memo = EvalMemo::new();
    eval_term(ctx, p, &|_| None, &mut memo) == Some(1)
}

/// Prove that `pre` implies `post` for every input.
///
/// A goal that is closed and true is decided without building the implication's
/// diagram. That case is worth its own arm because the *goal* can be tiny while the
/// assumption is not: an obligation whose postcondition is a closed arithmetic fact
/// (`12 / 4 == 3`, once the body's operands folded to literals) follows from any
/// precondition at all, yet the ordinary route first builds `!pre || post` -- and when
/// `pre` carries a 64-bit multiply the diagram is refused for its own size before the
/// trivial goal is ever examined. Evaluating the goal alone is a walk over the goal's
/// own DAG, which is small, and it is exactly the check that says "nothing to prove".
///
/// Soundness does not depend on the assumption: a closed term has one value for every
/// input, so a `true` from [`eval_term`] is a proof that the goal holds
/// unconditionally. A goal with a free variable, or a closed false one, falls through
/// to the engine.
pub fn prove_implies(pre: Pred, post: Pred) -> Verdict {
    with_ctx(|c| {
        if goal_is_closed_true(c, post.0) {
            return Verdict::Valid;
        }
        let np = c.un_bool(Op::Not, pre.0);
        let goal = c.bin_bool(Op::Or, np, post.0);
        c.query_valid(goal)
    })
}

/// Prove that `a` and `b` are equivalent for every input.
pub fn prove_equiv(a: Pred, b: Pred) -> Verdict {
    with_ctx(|c| {
        let x = c.bin_bool(Op::Xor, a.0, b.0);
        let nx = c.un_bool(Op::Not, x);
        c.query_valid(nx)
    })
}

/// Find an input satisfying `p`; `Valid` means "always satisfiable".
pub fn find_model(p: Pred) -> Verdict {
    with_ctx(|c| c.query_model(p.0))
}

// --- substitution (the engine behind weakest-precondition generation) -------

/// Apply `bindings` to a word, returning the rewritten word.
///
/// Bindings are simultaneous: `[(x, y), (y, x)]` swaps the two variables rather
/// than assigning `x := y` and then clobbering `y` with the already-updated `x`.
/// This is what makes assignment semantics in [`crate::wp`] correct.
pub fn substitute_word(w: Var, bindings: &[(Var, Var)]) -> Var {
    with_ctx(|c| {
        c.clear_subst();
        for (from, to) in bindings {
            c.bind_subst(from.0, to.0);
        }
        Var(c.subst(w.0))
    })
}

/// The internal shape of `p`, for tools that need to walk the formula.
///
/// This is the crate's escape hatch for the SMT-LIB exporter in
/// [`crate::smtscript`]. It is deliberately `pub(crate)`: the representation is
/// not a stable interface.
pub(crate) fn pred_node(p: Pred) -> Node {
    with_ctx(|c| c.node_pub(p.0))
}

/// Apply `bindings` to a predicate, returning the rewritten predicate.
pub fn substitute(p: Pred, bindings: &[(Var, Var)]) -> Pred {
    with_ctx(|c| {
        c.clear_subst();
        for (from, to) in bindings {
            c.bind_subst(from.0, to.0);
        }
        Pred(c.subst(p.0))
    })
}

/// The most variables one precondition may pin to a constant.
///
/// `std`-only for the same reason as [`pinned_vars`]: its only caller is the MIR
/// frontend, which is behind the feature.
#[cfg(feature = "std")]
pub(crate) const MAX_PINS: usize = 16;

/// `(variable index, value)` for each conjunct of `p` that pins a variable to a
/// constant: `v == k` or `k == v`, under any nesting of `&&`.
///
/// The caller seeds a pinned argument with its literal instead of a fresh symbolic
/// input. That is *sound* -- every model of `p` has `v == k`, so evaluating the body
/// at `v == k` leaves the obligation under `p` unchanged -- and it is what makes a
/// query whose precondition pins a variable decidable. The body then builds its
/// operations on a literal, and the constant folds collapse them; a symbolic operand
/// instead builds the whole circuit and the query is refused for the size of its own
/// diagram. `requires: a == -7` with the body `a / 3` is the motivating shape: the
/// 64-bit restoring divider is a documented scaling wall, and the precondition says
/// there is only one `a` to divide.
///
/// The extraction runs to a *fixpoint*, not one pass, because a pin's right-hand side
/// may name a variable another conjunct pins. `a == 5 && b == a + 1` pins `a := 5` in
/// the first pass and `b := 6` in the second, and the same chain reaches any depth the
/// pin list has room for. Each round is justified by the rounds before it: `b := 6`
/// follows from `b == a + 1` *and* `a == 5`, and both are conjuncts, so `b := 6` is a
/// consequence of `p` by the same transitivity that makes `a := 5` one. Nothing here
/// is an assumption beside `p`; a value the conjuncts do not force stays unpinned and
/// the body keeps its symbolic operand.
///
/// Only a *closed* right-hand side pins -- closed meaning "the pins so far evaluate it
/// to a value", not "it contains no variable". `v == w` between two variables whose
/// values the pins do not fix is not a pin -- it is a relation, and folding it would
/// fix both -- so it is left alone.
#[cfg(feature = "std")]
pub(crate) fn pinned_vars(p: Pred, out: &mut [(u32, u64); MAX_PINS]) -> usize {
    with_ctx(|c| {
        let mut leaves = [Term(0); MAX_CONJ];
        let n = c.op_leaves(Op::And, p.0, &mut leaves);
        let mut pins = [(0u32, 0u64); MAX_PINS];
        let mut count = 0usize;
        // Each round re-scans every conjunct with the pins found so far in scope, so a
        // right-hand side that names an already-pinned variable evaluates. A round that
        // adds nothing ends the walk: `count` only grows, so it terminates in at most
        // `MAX_PINS` rounds, and a chain longer than the list simply stops being pinned
        // rather than looping.
        loop {
            let before = count;
            for leaf in leaves[..n].iter() {
                if count >= MAX_PINS {
                    break;
                }
                let node = c.node_of(*leaf);
                if node.op != Op::Eq {
                    continue;
                }
                let (a, b) = (Term(node.a), Term(node.b));
                let (na, nb) = (c.node_of(a), c.node_of(b));
                // One side a variable, the other a term the pins evaluate. A variable on
                // *both* sides is a relation rather than a pin.
                let (idx, other) = match (na.op, nb.op) {
                    (Op::Var, Op::Var) => continue,
                    (Op::Var, _) => (na.a, b),
                    (_, Op::Var) => (nb.a, a),
                    _ => continue,
                };
                // The first pin of a variable is the one to keep: a second conjunct
                // naming it restates what the first already fixed (or contradicts it, in
                // which case the precondition is unsatisfiable and no pin is needed).
                if pins[..count].iter().any(|&(i, _)| i == idx) {
                    continue;
                }
                // A fresh memo per round: the closure changed, so a term that evaluated
                // to `None` last round (and so was not cached) must be asked again.
                let mut memo = EvalMemo::new();
                let lookup = |i: u32| pins[..count].iter().find(|&&(j, _)| j == i).map(|&(_, k)| k);
                let Some(k) = eval_term(c, other, &lookup, &mut memo) else { continue };
                pins[count] = (idx, k);
                count += 1;
            }
            if count == before {
                break;
            }
        }
        out[..count].copy_from_slice(&pins[..count]);
        count
    })
}

#[cfg(test)]
mod subst_tests {
    use super::*;

    #[test]
    fn a_binding_target_must_be_a_variable() {
        // `word(7, 8)` is a `Const` whose `a` field is the *value* 7, not an index. Binding
        // it used to substitute variable index 7, so an assignment written with a constant
        // target silently rewrote an unrelated variable and proved things about it.
        with_fresh(|| {
            let v = var_named(7, 8);
            let p = eq_const(v, 0);
            let r = std::panic::catch_unwind(|| substitute(p, &[(word(7, 8), word(0, 8))]));
            assert!(r.is_err(), "binding a constant must be refused, not misread as index 7");
        });
        // The same for an operation term, whose `a` is a term id.
        with_fresh(|| {
            let x = var(8);
            let t = truncate(x, 4);
            let p = eq_const(x, 0);
            let r = std::panic::catch_unwind(|| substitute(p, &[(t, word(0, 8))]));
            assert!(r.is_err(), "binding a non-variable term must be refused");
        });
        // And a genuine variable binding still works, so the check is not refusing everything.
        with_fresh(|| {
            let x = var(8);
            let p = eq_const(x, 0);
            // `x == 0` with `x := 9` is `9 == 0`, which is false: `Unsat`, not `Valid`.
            let q = substitute(p, &[(x, word(9, 8))]);
            assert_eq!(prove(q), Verdict::Unsat);
        });
    }

    #[test]
    fn a_binding_whose_width_does_not_match_is_refused() {
        // An 8-bit variable bound to a 16-bit word. The blaster reads the rebuilt
        // expression at the *comparison's* width, so binding `x := 257u16` into
        // `x == 1` would read only the low byte (`1`) and prove `Valid` -- a
        // theorem about an assignment the source language rejects. The query must
        // be refused rather than answered.
        with_fresh(|| {
            let x = var(8);
            let p = eq_const(x, 1);
            let q = substitute(p, &[(x, word(257, 16))]);
            assert_eq!(
                prove(q),
                Verdict::Unknown,
                "an 8-bit target bound to a 16-bit word must be refused, not proved"
            );
        });
        // The control: the same binding at the right width is decided, so the
        // refusal is not refusing every binding. `x == 1` with `x := 1` is true.
        with_fresh(|| {
            let x = var(8);
            let p = eq_const(x, 1);
            let q = substitute(p, &[(x, word(1, 8))]);
            assert_eq!(prove(q), Verdict::Valid);
        });
        // And the wrong *value* at the right width is still refuted, which is the
        // answer the mismatched binding was wrongly giving.
        with_fresh(|| {
            let x = var(8);
            let p = eq_const(x, 1);
            let q = substitute(p, &[(x, word(2, 8))]);
            assert_eq!(prove(q), Verdict::Unsat);
        });
    }

    #[test]
    fn two_bindings_for_one_target_are_refused() {
        // `x := 1, x := 2` has no single meaning. Keeping the last silently proves
        // `x == 2`; keeping the first proves `x == 1`; and which one you get is the order
        // of the list, not anything the specification says. The query must refuse.
        with_fresh(|| {
            let x = var(8);
            let p = eq_const(x, 2);
            let q = substitute(p, &[(x, word(1, 8)), (x, word(2, 8))]);
            assert_eq!(prove(q), Verdict::Unknown);
        });
        with_fresh(|| {
            let x = var(8);
            let p = eq_const(x, 1);
            let q = substitute(p, &[(x, word(2, 8)), (x, word(1, 8))]);
            assert_eq!(prove(q), Verdict::Unknown);
        });
        // Two *different* targets are still fine, so the check is not refusing everything.
        with_fresh(|| {
            let x = var(8);
            let y = var(8);
            let p = and(eq_const(x, 1), eq_const(y, 2));
            let q = substitute(p, &[(x, word(1, 8)), (y, word(2, 8))]);
            assert_eq!(prove(q), Verdict::Valid);
        });
    }
}

#[cfg(test)]
mod pin_tests {
    use super::*;

    fn pins(p: Pred) -> Vec<(u32, u64)> {
        let mut buf = [(0u32, 0u64); MAX_PINS];
        let n = pinned_vars(p, &mut buf);
        buf[..n].to_vec()
    }

    /// `v == k` pins `v` to `k`, whichever side the constant is written on.
    ///
    /// The value is the *bit pattern*, not the signed number: `-7` at eight bits is
    /// `249`. That is deliberate -- the caller masks it to the argument's width and
    /// builds a literal from it, and `word(249, 8)` *is* `-7` at eight bits. A
    /// signed value here would have to be re-signed at the caller's width, which is
    /// exactly the width information this function does not have.
    #[test]
    fn an_equality_to_a_constant_pins_the_variable() {
        with_fresh(|| {
            let a = var_named(1, 8);
            assert_eq!(pins(eq_const(a, 200)), vec![(1, 200)]);
        });
        // The constant on the left is the same pin.
        with_fresh(|| {
            let a = var_named(1, 8);
            assert_eq!(pins(eq(word(200, 8), a)), vec![(1, 200)]);
        });
        // A negated literal, as the spec parser spells it: `0 - 7` at eight bits.
        with_fresh(|| {
            let a = var_named(1, 8);
            let neg7 = sub(word(0, 8), word(7, 8));
            assert_eq!(pins(eq(a, neg7)), vec![(1, 249)], "`-7` at eight bits is the bit pattern 249");
        });
    }

    /// A relation between two variables is *not* a pin, and a non-equality is not
    /// either.
    ///
    /// `v == w` fixes neither one on its own: seeding either with a literal would
    /// discard the relation and could decide a query that the precondition does not
    /// actually leave decided. The honest answer is no pin, which is what this
    /// asserts -- the negative direction, without which a function that pinned every
    /// `Eq` it saw would pass the test above.
    #[test]
    fn a_relation_between_two_variables_is_not_a_pin() {
        with_fresh(|| {
            let a = var_named(1, 8);
            let b = var_named(2, 8);
            assert!(pins(eq(a, b)).is_empty(), "`a == b` must not pin either side");
        });
        // `a < 200` constrains `a` without fixing it.
        with_fresh(|| {
            let a = var_named(1, 8);
            assert!(pins(ult(a, word(200, 8))).is_empty(), "`a < 200` must not pin `a`");
        });
    }

    /// The conjuncts are found under any nesting of `&&`, and a conjunct that is
    /// itself a disjunction is *not* decomposed: `a == 1 || a == 2` leaves two
    /// values, so it pins nothing.
    #[test]
    fn a_pin_is_found_through_conjunction_but_not_disjunction() {
        with_fresh(|| {
            let a = var_named(1, 8);
            let b = var_named(2, 8);
            let p = and(eq_const(a, 1), and(eq_const(b, 2), ult(a, word(9, 8))));
            let mut got = pins(p);
            got.sort_unstable();
            assert_eq!(got, vec![(1, 1), (2, 2)], "both pins must be found under a nested `&&`");
        });
        with_fresh(|| {
            let a = var_named(1, 8);
            let p = or(eq_const(a, 1), eq_const(a, 2));
            assert!(pins(p).is_empty(), "a disjunction of two values is not a pin");
        });
    }

    /// The pin is *sound*: the query under the precondition is unchanged by
    /// specialising the variable. `a == 5 && a / 2 == 2` holds for exactly one `a`,
    /// and pinning `a := 5` must keep it `Valid` rather than change the answer.
    #[test]
    fn pinning_a_variable_preserves_the_query_under_its_precondition() {
        with_fresh(|| {
            let a = var_named(1, 8);
            let pre = eq_const(a, 5);
            let goal = eq(udiv(a, word(2, 8)), word(2, 8));
            // Under `pre`, the goal holds. Substitute the pin and the closed formula
            // is still `Valid` -- which is the property the executor relies on.
            let pinned = substitute(goal, &[(a, word(5, 8))]);
            assert_eq!(prove(pinned), Verdict::Valid);
            // The *false* direction stays false, so the pin does not make anything true.
            let bad = eq(udiv(a, word(2, 8)), word(3, 8));
            let pinned_bad = substitute(bad, &[(a, word(5, 8))]);
            assert_eq!(prove(pinned_bad), Verdict::Unsat);
            let _ = pre;
        });
    }

    /// A pin whose right-hand side names an already-pinned variable is pinned too, in
    /// a later round.
    ///
    /// `a == 5 && b == a + 1` leaves `b` fixed at `6` by transitivity, so the second
    /// round must find it. One pass would miss it, because `a + 1` does not evaluate
    /// without `a`'s value -- and the whole point of the fixpoint is that the *first*
    /// round's result is what makes the second round's right-hand side closed.
    #[test]
    fn a_pin_whose_rhs_names_a_pinned_variable_is_found_in_a_later_round() {
        with_fresh(|| {
            let a = var_named(1, 8);
            let b = var_named(2, 8);
            let p = and(eq_const(a, 5), eq(b, add(a, word(1, 8))));
            let mut got = pins(p);
            got.sort_unstable();
            assert_eq!(got, vec![(1, 5), (2, 6)], "`b == a + 1` must pin `b := 6`");
        });
        // The same through a multiply, and through a three-link chain, so the walk is
        // not accidentally limited to one extra round.
        with_fresh(|| {
            let a = var_named(1, 8);
            let b = var_named(2, 8);
            let p = and(eq_const(a, 6), eq(b, mul(a, word(2, 8))));
            let mut got = pins(p);
            got.sort_unstable();
            assert_eq!(got, vec![(1, 6), (2, 12)]);
        });
        with_fresh(|| {
            let a = var_named(1, 8);
            let b = var_named(2, 8);
            let c = var_named(3, 8);
            let p = and(
                eq_const(a, 5),
                and(eq(b, add(a, word(1, 8))), eq(c, mul(b, word(2, 8)))),
            );
            let mut got = pins(p);
            got.sort_unstable();
            assert_eq!(got, vec![(1, 5), (2, 6), (3, 12)], "a three-link chain must resolve");
        });
    }

    /// A chain whose root is missing pins nothing, and that is the honest answer.
    ///
    /// `b == a + 1 && c == b * 2` fixes neither `b` nor `c`: `a` is free, so every `b`
    /// is possible. The fixpoint must not invent a value for `a` to make the chain
    /// resolve -- the negative direction of the test above.
    #[test]
    fn a_chain_with_no_pinned_root_stays_unpinned() {
        with_fresh(|| {
            let a = var_named(1, 8);
            let b = var_named(2, 8);
            let c = var_named(3, 8);
            let p = and(eq(b, add(a, word(1, 8))), eq(c, mul(b, word(2, 8))));
            assert!(pins(p).is_empty(), "a free root must not be pinned to anything");
        });
    }
}

#[cfg(test)]
mod prove_implies_tests {
    use super::*;

    /// A closed goal that is true is proved without building the implication.
    ///
    /// The assumption carries a 64-bit multiply, which is the shape that made the
    /// engine refuse the whole query for the size of its diagram even though the goal
    /// -- `12 / 4 == 3`, as the interpreter's divider spells it -- is a fact about
    /// literals. The goal alone is what the short-circuit evaluates.
    #[test]
    fn a_closed_true_goal_is_proved_even_when_the_assumption_is_a_wall() {
        with_fresh(|| {
            let a = var_named(1, 64);
            let b = var_named(2, 64);
            let c = var_named(3, 64);
            let pre = and(
                and(eq_const(a, 5), eq(b, add(a, word(1, 64)))),
                eq(c, mul(b, word(2, 64))),
            );
            let twelve = word(12, 64);
            let quotient = ashr(add(twelve, band(ashr(twelve, 63), word(3, 64))), 2);
            assert_eq!(prove_implies(pre, eq(quotient, word(3, 64))), Verdict::Valid);
        });
    }

    /// The short-circuit must not decide a goal that is closed but *false*, and it
    /// must not decide one that is still open.
    ///
    /// This is the negative direction of the test above, and it is the one that keeps
    /// the arm from being a "prove anything" rule: a closed false goal evaluates to
    /// `Some(0)` and a goal with a free variable evaluates to `None`, so both fall
    /// through to the engine rather than being reported `Valid`. The engine's own
    /// verdict for each is not what this test pins down -- only that neither is a
    /// proof.
    #[test]
    fn a_closed_false_goal_and_an_open_goal_still_go_to_the_engine() {
        with_fresh(|| {
            let v = prove_implies(truth(true), eq(word(12, 8), word(13, 8)));
            assert_ne!(v, Verdict::Valid, "a closed false goal is not a theorem");
        });
        with_fresh(|| {
            let x = var_named(1, 8);
            let v = prove_implies(truth(true), eq(x, word(3, 8)));
            assert_ne!(v, Verdict::Valid, "an open goal is not decided by evaluation alone");
            assert!(matches!(v, Verdict::Counterexample(_)), "and the engine must find its witness");
        });
    }
}

#[cfg(test)]
mod var_tests {
    use super::*;

    #[test]
    fn one_index_at_two_widths_is_refused() {
        // The low bits of the two declarations are the same BDD variables, so without the
        // refusal `b`'s low byte is `a` and this comes out `Valid`.
        with_fresh(|| {
            let a = var_named(0, 8);
            let b = var_named(0, 16);
            let forced = implies(eq_const(a, 3), eq_const(truncate(b, 8), 3));
            assert_eq!(
                prove(forced),
                Verdict::Unknown,
                "a re-declared index at a different width must not alias"
            );
        });
    }

    #[test]
    fn one_index_at_one_width_is_the_same_variable() {
        // The intended use: naming a variable for a readable model. Fetching it twice
        // gives the same variable, which is what makes an explicit index useful.
        with_fresh(|| {
            let a = var_named(0, 8);
            let b = var_named(0, 8);
            assert_eq!(prove(eq(a, b)), Verdict::Valid);
        });
    }
}

#[cfg(test)]
mod word_tests {
    use super::*;

    #[test]
    fn word_flags_a_constant_that_does_not_fit() {
        // In range: no clash, and the value is exact.
        with_fresh(|| {
            assert_eq!(prove(eq_const(word(255, 8), 255)), Verdict::Valid);
            assert_eq!(prove(eq_const(word(0, 8), 0)), Verdict::Valid);
        });
        // Out of range: refuse, do not wrap to `word(v & mask, w)`.
        for (v, w) in [(256u64, 8u8), (300, 8), (u64::MAX, 8), (65536, 16)] {
            with_fresh(|| {
                let c = word(v, w);
                assert_eq!(
                    prove(eq_const(c, v & ((1u64 << w) - 1))),
                    Verdict::Unknown,
                    "word({}, {}) must not silently wrap",
                    v,
                    w
                );
            });
        }
    }

    #[test]
    fn all_ones_is_the_explicit_mask() {
        for w in [1u8, 4, 8, 16, 32, 64] {
            with_fresh(|| {
                let ones = all_ones(w);
                // Every bit set: OR-ing in anything changes nothing.
                let x = var(w);
                assert_eq!(prove(eq(bor(x, ones), ones)), Verdict::Valid);
            });
        }
        // And it does not trip the out-of-range check.
        with_fresh(|| {
            assert_eq!(prove(eq_const(all_ones(8), 255)), Verdict::Valid);
        });
    }
}

#[cfg(test)]
mod const_fold_tests {
    use super::*;

    /// A predicate read as a word, for the folds that produce one.
    fn pv(p: Pred) -> Var {
        Var(p.0)
    }

    /// A word operation on two literals collapses to the literal, and the value is
    /// the operator's own wrapping definition.
    #[test]
    fn a_word_operation_on_two_literals_is_the_literal() {
        with_fresh(|| {
            let a = word(200, 8);
            let b = word(100, 8);
            // `200 + 100` wraps to `44` at eight bits, exactly as `eval_term_body` says.
            assert_eq!(const_of(add(a, b)), Some(44));
            assert_eq!(const_of(sub(a, b)), Some(100));
            assert_eq!(const_of(mul(a, b)), Some(32));
            assert_eq!(const_of(band(word(0xf0, 8), word(0x3c, 8))), Some(0x30));
            assert_eq!(const_of(bor(word(0xf0, 8), word(0x0f, 8))), Some(0xff));
            assert_eq!(const_of(bxor(word(0xff, 8), word(0x0f, 8))), Some(0xf0));
        });
    }

    /// A comparison of two literals is a *one-bit* constant, not one carrying the
    /// operand width. A comparison node stores its operands' width even though it
    /// denotes one bit, and a folded node left wide would hand a later width check a
    /// term of the wrong shape -- the bug the `un_bool` guard exists for.
    #[test]
    fn a_comparison_of_two_literals_is_one_bit() {
        with_fresh(|| {
            let lt = ult(word(3, 32), word(5, 32));
            assert_eq!(const_of(pv(lt)), Some(1));
            assert_eq!(bits(pv(lt)), 1, "a folded comparison must be one bit wide");
            let eq = eq(word(4, 64), word(9, 64));
            assert_eq!(const_of(pv(eq)), Some(0));
            assert_eq!(bits(pv(eq)), 1, "a folded comparison must be one bit wide");
            let le = ule(word(5, 8), word(5, 8));
            assert_eq!(const_of(pv(le)), Some(1));
        });
    }

    /// The whole point of the fold: a query with no symbolic input at all is
    /// *decided*, at every width, instead of being refused for the size of its own
    /// circuit. `sdiv(-7, 3)` is `-2` -- `prove` on a closed formula must not be
    /// `Unknown` merely because the formula is a divider.
    #[test]
    fn a_fully_literal_signed_division_is_decided_at_every_width() {
        for w in [8u8, 16, 32, 64] {
            with_fresh(|| {
                let mask = if w >= 64 { u64::MAX } else { (1u64 << w) - 1 };
                let minus7 = word((-7i64 as u64) & mask, w);
                let three = word(3, w);
                let minus2 = word((-2i64 as u64) & mask, w);
                let q = sdiv(minus7, three);
                assert_eq!(
                    const_of(q),
                    Some((-2i64 as u64) & mask),
                    "`-7 / 3` at {w} bits must fold to `-2`"
                );
                assert_eq!(
                    prove(eq(q, minus2)),
                    Verdict::Valid,
                    "a closed `-7 / 3 == -2` at {w} bits must be proved, not refused"
                );
            });
        }
    }

    /// The division folds agree with Rust's own `/` and `%` on the edges the
    /// general path special-cases: a zero divisor and `MIN / -1`.
    #[test]
    fn the_constant_divider_matches_the_general_path_on_its_edges() {
        with_fresh(|| {
            // `y == 0`: quotient all ones, remainder the dividend.
            let (q, r) = sdivmod(word(5, 8), word(0, 8));
            assert_eq!(const_of(q), Some(255));
            assert_eq!(const_of(r), Some(5));
        });
        with_fresh(|| {
            // `i8::MIN / -1` wraps to `i8::MIN`, remainder zero.
            let (q, r) = sdivmod(word(128, 8), word(255, 8));
            assert_eq!(const_of(q), Some(128));
            assert_eq!(const_of(r), Some(0));
        });
        with_fresh(|| {
            // The unsigned divider's zero case, for the same reason.
            let (q, r) = divmod(word(5, 8), word(0, 8));
            assert_eq!(const_of(q), Some(255));
            assert_eq!(const_of(r), Some(5));
        });
    }

    /// A *negation* (`0 - x`) is deliberately not folded, because the frontend
    /// spells a unary `-` that way and tells `-128` from the bare literal `128` by
    /// the node being a `Sub` rather than a `Const`. Folding it would merge the two
    /// and refuse a valid `y == -128`. The other subtractions still fold.
    #[test]
    fn a_negation_is_not_folded_but_a_real_subtraction_is() {
        with_fresh(|| {
            let n = sub(word(0, 8), word(128, 8));
            assert_eq!(
                const_of(n),
                None,
                "`0 - x` must stay a `Sub` node: the frontend keys literal-range \
                 bookkeeping on it not aliasing the literal it negates"
            );
        });
        with_fresh(|| {
            // `x - y` with a nonzero left operand still folds -- the divider is built
            // from it.
            assert_eq!(const_of(sub(word(10, 8), word(3, 8))), Some(7));
        });
    }

    /// `truncate` is deliberately not folded: the frontend builds a named bound
    /// (`i8::MIN`) as `truncate(word(k, 64), w)` so it does *not* hash-cons with the
    /// literal `word(k, w)`. Folding a literal through `Trunc` would merge them and
    /// make the bound inherit the literal's out-of-range envelope.
    #[test]
    fn a_truncated_literal_keeps_its_own_term() {
        with_fresh(|| {
            let t = truncate(word(128, 64), 8);
            assert_ne!(
                t.0 .0, word(128, 8).0 .0,
                "`truncate(word(128,64), 8)` must not hash-cons with `word(128, 8)`"
            );
            assert_eq!(evaluate(t, |_| None), Some(128), "but it still denotes 128");
        });
    }

    /// A fold may not change a verdict: the folded term and the circuit it replaces
    /// must satisfy the same predicates. This pins the property rather than a list
    /// of cases, by evaluating both.
    #[test]
    fn a_fold_preserves_the_value_it_replaces() {
        with_fresh(|| {
            let a = word(37, 8);
            let b = word(11, 8);
            let folded = add(a, b);
            let wide = add(truncate(a, 16), truncate(b, 16));
            assert_eq!(evaluate(folded, |_| None), Some(48));
            assert_eq!(evaluate(wide, |_| None), Some(48));
        });
    }
}

#[cfg(test)]
mod generation_tests {
    use super::*;

    /// A handle from one arena must never be validated by a *recycled slot*.
    ///
    /// The staleness check used to be a per-slot table, `term_gen[slot]`, written by
    /// `mk_term` and compared against the current generation. A reset restarts slot
    /// numbering at 1 and the next `mk_term` rewrites that slot's stamp, so a predicate
    /// saved from an earlier arena found a *current* stamp on whatever term now occupied
    /// its slot and was discharged as if it were itself. A predicate that is false for
    /// every input (`x == 1 && x == 2`) came back `Valid` once enough terms were built to
    /// land a true term on its slot -- a proof of a false statement.
    ///
    /// The generation is now packed into the handle, so the comparison is against bits
    /// nothing later can rewrite. This sweeps the filler count that reproduced it.
    #[test]
    fn a_recycled_slot_does_not_validate_a_stale_handle() {
        let saved: Pred = with_fresh(|| {
            let x = var(8);
            and(x.eq_val(1), x.eq_val(2))
        });
        for filler in 0..48u64 {
            let out = with_fresh(|| {
                for j in 0..filler {
                    let _ = word(j, 8);
                }
                saved.prove()
            });
            assert_ne!(
                out,
                Verdict::Valid,
                "a false predicate from an earlier arena was proved (filler = {filler})"
            );
        }
    }

    /// And the fix must not refuse everything: a handle in its own arena still proves.
    #[test]
    fn a_current_handle_still_discharges() {
        with_fresh(|| {
            let x = var(8);
            assert_eq!(implies(x.lt_val(16), x.lt_val(32)).prove(), Verdict::Valid);
        });
    }

    /// A width the blaster cannot represent must be refused, not panicked on.
    ///
    /// `word` bounds its width, but a term reached another way (or built by a future
    /// constructor that forgets) still has to be refused at blast time: the blaster's
    /// buffers are `[u32; 64]`, so a 65-bit term indexed `out[64]` and panicked inside the
    /// solver, turning a malformed specification into an unwind rather than an `Unknown`.
    #[test]
    fn an_unrepresentable_width_is_refused_not_panicked_on() {
        // `word` refuses the width up front.
        for w in [0u8, 65, 100, 255] {
            with_fresh(|| {
                let c = word(1, w);
                assert_eq!(
                    prove(eq(c, c)),
                    Verdict::Unknown,
                    "word(1, {w}) must be refused"
                );
            });
        }
        // In-range widths are unaffected.
        for w in [1u8, 8, 16, 64] {
            with_fresh(|| {
                let c = word(1, w);
                assert_eq!(prove(eq(c, c)), Verdict::Valid, "word(1, {w}) must hold");
            });
        }
    }

    /// The boolean identities are folded at construction, and the two that matter most
    /// are the ones a *path condition* needs.
    ///
    /// A contradiction has to become a literal `false` before the bit-blaster runs. If it
    /// does not, both copies of the operand are expanded first, and when the operand
    /// contains a wide divider the diagram blows up before any solver sees the false
    /// literal -- which is how the `u16` saturating multiply stayed undecided.
    #[test]
    fn boolean_identities_fold_at_construction() {
        with_fresh(|| {
            let p = ult(var(8), word(5, 8));
            // `p && !p` is `false`, and `p || !p` is `true`, at the root.
            assert_eq!(prove(and(p, not(p))), Verdict::Unsat);
            assert_eq!(prove(or(p, not(p))), Verdict::Valid);
            // The same with the two operands built independently: hash-consing returns the
            // same handle, so this is the same term, and the fold must not be matching a
            // handle by accident.
            let q = || ult(var_named(0, 8), word(5, 8));
            assert_eq!(prove(and(q(), not(q()))), Verdict::Unsat);
            // `!!p == p`, and the fold must not turn a predicate into a wide term: a
            // comparison node carries the operand width, so the width check is what keeps
            // the arena well-formed.
            assert_eq!(prove_equiv(p, not(not(p))), Verdict::Valid);
            assert!(!is_ill_formed(), "the double-negation fold must not change a width");
            // Constants.
            assert_eq!(prove_equiv(and(truth(true), p), p), Verdict::Valid);
            assert_eq!(prove(not(truth(true))), Verdict::Unsat);
        });
    }

    /// Cancellation through the `&&`/`||` spine, which is what a path condition needs.
    ///
    /// The `sat_mul` shape: the path into the multiply is the conjunction
    /// `b == 0 && a <= MAX / b` and the overflow test is `b != 0 && a > MAX / b`. The
    /// conjuncts cancel pairwise, but across two `&&` spines rather than at either root --
    /// so a top-level identity check misses it, and the divider inside both terms is
    /// blasted before any solver sees the contradiction.
    #[test]
    fn a_path_contradiction_cancels_through_the_spine() {
        with_fresh(|| {
            let w = 16u8;
            let a = var(w);
            let b = var(w);
            let max = word((1u64 << w) - 1, w);
            let zero = word(0, w);
            // The exact unsigned multiply-overflow predicate, as `exec::overflow_pred`
            // builds it: `b != 0 && a > MAX / b`.
            let over = and(not(eq(b, zero)), ult(udiv(max, b), a));
            // The path that reaches the multiply when the guard does not fire. This is the
            // conjunction rustc's two `switchInt`s leave on the path: `b == 0` from the
            // first, `!(a > MAX / b)` from the second.
            let path = and(eq(b, zero), not(ult(udiv(max, b), a)));
            // `path && over` is unsatisfiable, and it has to be decided without the
            // 16-bit divider ever being blasted -- which is exactly what the spine
            // cancellation buys. If the fold were missing this would come back `Unknown`
            // after expanding both dividers, not `Unsat`.
            assert_eq!(
                find_model(and(path, over)),
                Verdict::Unsat,
                "the guard and its negation must cancel across the spine"
            );
        });
    }
}

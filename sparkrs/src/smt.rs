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

/// Worst-case arena memory in bytes, so an integrator can budget statically.
pub const ARENA_BYTES: usize =
    CAP * (core::mem::size_of::<Node>() + 2 * core::mem::size_of::<u32>());

/// Maximum number of symbolic variables per thread.
pub const MAX_VARS: usize = 256;

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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Term(pub(crate) u32);

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
    generation: u32,
    /// The generation that created each term id. A handle is stale when its id's stamp is
    /// not the current generation. Deliberately *not* cleared by `reset`: remembering the
    /// old stamps is what makes staleness detectable.
    term_gen: [u32; CAP],
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

impl Ctx {
    const fn new() -> Self {
        Ctx {
            terms: [Node { op: Op::Const, a: 0, b: 0, c: 0, width: 0, hi: 0 }; CAP],
            n_terms: 0,
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
            ready: false,
            subst_val: [NO_SUBST; MAX_VARS],
            subst_memo: [0; CAP],
            subst_epoch: [0; CAP],
            epoch: 1,
            generation: 1,
            term_gen: [0; CAP],
            stale: false,
            ill_formed: false,
            _not_shared: core::marker::PhantomData,
        }
    }

    /// Clear the arena in place. Deliberately avoids `*self = Ctx::new()`, which
    /// would materialise a large temporary on the stack (bad on small firmware
    /// stacks) just to throw it away.
    fn reset(&mut self) {
        self.n_terms = 0;
        self.n_nodes = 2;
        self.n_vars = 0;
        self.overflow = false;
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
        // Term ids restart at 0, so every handle from the previous arena now names a
        // different term. Bumping the generation is what lets a handle say which arena
        // justified it, and be rejected in any other. Must be bumped, never reset to a
        // constant: a repeated generation would validate a stale handle.
        self.generation = self.generation.wrapping_add(1);
        if self.generation == 0 {
            // The counter wrapped, so the old stamps would match again. Clear them; the
            // stamp for anything still live is rewritten by `mk_term`.
            for i in 0..CAP {
                self.term_gen[i] = u32::MAX;
            }
            self.generation = 1;
        }
        self.stale = false;
        self.ill_formed = false;
        self.ensure_ready();
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
                self.term_gen[id as usize] = self.generation;
                self.term_key[i as usize] = key;
                self.term_val[i as usize] = id;
                return Term(id);
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
                    return Term(self.term_val[i as usize]);
                }
            }
            i = (i + 1) & self.term_mask;
        }
    }

    /// Note a stale handle. Every accessor funnels through here, so one check covers
    /// `Var`, `Pred`, and anything else that carries a term id — the caller does not have
    /// to remember to look.
    pub(crate) fn is_current_term(&mut self, t: Term) -> bool {
        if self.term_gen[t.0 as usize] != self.generation {
            self.stale = true;
            false
        } else {
            true
        }
    }

    fn note_if_stale(&mut self, t: Term) {
        if self.term_gen[t.0 as usize] != self.generation {
            self.stale = true;
        }
    }

    fn node_of(&mut self, t: Term) -> Node {
        self.note_if_stale(t);
        self.terms[t.0 as usize]
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
        self.terms[t.0 as usize].width
    }

    /// Read a term's node. Exposed to the crate so the SMT-LIB exporter can walk
    /// the same IR the solver reasons about, instead of re-deriving it.
    pub(crate) fn node_pub(&mut self, t: Term) -> Node {
        self.note_if_stale(t);
        self.terms[t.0 as usize]
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
        if self.stale || self.term_gen[t.0 as usize] != self.generation {
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
                let key = t.0 as usize;
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

    fn var_term(&mut self, idx: u32, width: u8) -> Term {
        if idx as usize >= MAX_VARS {
            self.overflow = true;
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

    fn bin_word(&mut self, op: Op, a: Term, b: Term) -> Term {
        self.require_same_width(a, b, "binary word operation");
        let w = self.width_of(a);
        self.mk_term(Node { op, a: a.0, b: b.0, c: 0, width: w, hi: 0 })
    }

    /// Boolean op (result width = 1).
    fn bin_bool(&mut self, op: Op, a: Term, b: Term) -> Term {
        self.mk_term(Node { op, a: a.0, b: b.0, c: 0, width: 1, hi: 0 })
    }

    /// Comparison op. The node keeps the *operand* width (the result is a
    /// single bit), so bit-blasting walks every operand bit but writes `out[0]`.
    fn max_of(&self, w: u8) -> u64 {
        if w >= 64 { u64::MAX } else { (1u64 << w) - 1 }
    }

    fn cmp(&mut self, op: Op, a: Term, b: Term) -> Term {
        self.require_same_width(a, b, "comparison");
        let w = self.width_of(a);
        self.mk_term(Node { op, a: a.0, b: b.0, c: 0, width: w, hi: 0 })
    }

    fn un_bool(&mut self, op: Op, a: Term) -> Term {
        self.mk_term(Node { op, a: a.0, b: 0, c: 0, width: 1, hi: 0 })
    }

    /// Change a term's width, keeping the low bits and zero-filling any new ones.
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
                loop {
                    let k = self.not_key[i as usize];
                    if k == u64::MAX {
                        break;
                    }
                    if k == key {
                        return self.not_val[i as usize];
                    }
                    i = (i + 1) & self.uniq_mask;
                }
                let v = self.var[a as usize];
                let lo = self.neg(self.lo[a as usize]);
                let hi = self.neg(self.hi[a as usize]);
                let r = self.mk_node(v, lo, hi);
                let mut j = (key as u32) & self.uniq_mask;
                loop {
                    if self.not_key[j as usize] == u64::MAX || self.not_key[j as usize] == key {
                        self.not_key[j as usize] = key;
                        self.not_val[j as usize] = r;
                        break;
                    }
                    j = (j + 1) & self.uniq_mask;
                }
                r
            }
        }
    }

    fn apply2(&mut self, op: u8, a: u32, b: u32) -> u32 {
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
        loop {
            let k = keys[i as usize];
            if k == u64::MAX {
                return None;
            }
            if k == key {
                return Some(vals[i as usize]);
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
        loop {
            let k = keys[i as usize];
            if k == u64::MAX || k == key {
                keys[i as usize] = key;
                vals[i as usize] = val;
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

    fn blast(&mut self, t: Term, out: &mut [u32; 64]) {
        // Check `stale` first, so once any stale handle has been touched the whole
        // traversal stops. Checking only the current node is not enough: a constructor can
        // read a stale node and then *build* a current node that refers back to the stale
        // id, so the graph contains a cycle whose every node is current. Stopping the
        // whole traversal on the first stale touch is what breaks it.
        if self.stale || self.term_gen[t.0 as usize] != self.generation {
            self.stale = true;
            out.fill(FALSE);
            return;
        }
        let n = self.node_of(t);
        let w = n.width as usize;
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
                        Op::LShr if bit + sh < w => a[bit + sh],
                        Op::LShr => FALSE,
                        // Arithmetic right shift replicates the sign bit.
                        _ if bit + sh < w => a[bit + sh],
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
        let node = self.blast_bool(t);
        if self.overflow || self.stale || self.ill_formed {
            return Verdict::Unknown;
        }
        match node {
            TRUE => Verdict::Valid,
            FALSE => Verdict::Unsat,
            _ => Verdict::Counterexample(self.model(node, true)),
        }
    }

    fn query_model(&mut self, t: Term) -> Verdict {
        let node = self.blast_bool(t);
        if self.overflow || self.stale || self.ill_formed {
            return Verdict::Unknown;
        }
        match node {
            TRUE => Verdict::Valid,
            FALSE => Verdict::Unsat,
            _ => Verdict::Counterexample(self.model(node, false)),
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
// recursion rather than a clean panic". It is now enforced. Every term id records the
// generation that created it (`term_gen`), the term accessors note a mismatch, and
// `blast`/`subst`/`eval_term` refuse to traverse a stale handle. A query that touches
// one returns `Unknown`, so nesting `with_fresh` degrades to "no answer" rather than
// "an answer about the wrong term" or a stack overflow.
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
    pub const SENTINEL: Var = Var(Term(0));
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
pub fn evaluate(t: Var, value: impl Fn(u32) -> Option<u64>) -> Option<u64> {
    with_ctx(|c| eval_term(c, t.0, &value))
}

/// [`evaluate`] for a predicate. `None` when some input is unknown.
pub fn evaluate_pred(p: Pred, value: impl Fn(u32) -> Option<u64>) -> Option<bool> {
    evaluate(Var(p.0), value).map(|v| v != 0)
}

fn eval_term(ctx: &mut Ctx, t: Term, value: &impl Fn(u32) -> Option<u64>) -> Option<u64> {
    if !ctx.is_current_term(t) {
        // A stale handle has no meaning to evaluate; `None` is "cannot say", which is
        // what `evaluate` already means by it.
        return None;
    }
    let n = ctx.node_of(t);
    let w = n.width;
    let mask = if w >= 64 { u64::MAX } else { (1u64 << w) - 1 };
    let v = match n.op {
        Op::Var => return value(n.a).map(|x| x & mask),
        Op::Const => (n.a as u64) | ((n.hi as u64) << 32),
        Op::Not => !eval_term(ctx, Term(n.a), value)? & mask,
        Op::And => eval_term(ctx, Term(n.a), value)? & eval_term(ctx, Term(n.b), value)? & mask,
        Op::Or => eval_term(ctx, Term(n.a), value)? | eval_term(ctx, Term(n.b), value)? & mask,
        Op::Xor => eval_term(ctx, Term(n.a), value)? ^ eval_term(ctx, Term(n.b), value)? & mask,
        // The shift amount lives in the node, not in a term; see `shift`.
        Op::Shl => {
            let a = eval_term(ctx, Term(n.a), value)?;
            let sh = n.b;
            if sh >= 64 {
                0
            } else {
                (a << sh) & mask
            }
        }
        Op::LShr => {
            let a = eval_term(ctx, Term(n.a), value)?;
            let sh = n.b;
            if sh >= 64 {
                0
            } else {
                (a & mask) >> sh
            }
        }
        Op::Shr => {
            // Arithmetic: replicate the sign bit, matching the bit-blaster.
            let a = eval_term(ctx, Term(n.a), value)? & mask;
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
        Op::Add => eval_term(ctx, Term(n.a), value)?.wrapping_add(eval_term(ctx, Term(n.b), value)?) & mask,
        Op::Sub => eval_term(ctx, Term(n.a), value)?.wrapping_sub(eval_term(ctx, Term(n.b), value)?) & mask,
        Op::Mul => eval_term(ctx, Term(n.a), value)?.wrapping_mul(eval_term(ctx, Term(n.b), value)?) & mask,
        Op::Eq => {
            u64::from(eval_term(ctx, Term(n.a), value)? == eval_term(ctx, Term(n.b), value)?)
        }
        Op::Ult => {
            u64::from(eval_term(ctx, Term(n.a), value)? < eval_term(ctx, Term(n.b), value)?)
        }
        Op::Ule => {
            u64::from(eval_term(ctx, Term(n.a), value)? <= eval_term(ctx, Term(n.b), value)?)
        }
        Op::Ite => {
            let c = eval_term(ctx, Term(n.a), value)?;
            if c != 0 {
                eval_term(ctx, Term(n.b), value)?
            } else {
                eval_term(ctx, Term(n.c), value)?
            }
        }
        Op::Trunc => {
            // Keep the low bits, zero-fill the rest.
            let a = eval_term(ctx, Term(n.a), value)?;
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
pub fn word(v: u64, width: u8) -> Var {
    with_ctx(|c| {
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
/// `x` re-typed to `width` bits: low bits kept, high bits zero-filled or dropped.
///
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

/// Prove that `pre` implies `post` for every input.
pub fn prove_implies(pre: Pred, post: Pred) -> Verdict {
    with_ctx(|c| {
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
            let idx = c.subst_target(from.0);
            c.set_subst(idx, to.0);
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
            let idx = c.subst_target(from.0);
            c.set_subst(idx, to.0);
        }
        Pred(c.subst(p.0))
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

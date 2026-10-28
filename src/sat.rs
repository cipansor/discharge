//! A CDCL SAT solver, so the crate has a decision procedure that scales.
//!
//! # Why this module exists
//!
//! The BDD engine in [`crate::smt`] is exact and canonical, and that canonicity is why
//! `prove` can answer "equivalent" by comparing two node ids. Its weakness is measured,
//! not assumed: it gives up at **8-bit multiplication** (`examples/probe.rs` prints the
//! table). Safety-critical code is full of wider arithmetic, so a BDD-only prover is
//! honest but not enough.
//!
//! This is the second engine, reached only when the BDD arena fills. It walks the *same
//! term graph* the BDD engine reasons about -- the ripple adders, the comparators, the
//! shift networks, as nodes in [`crate::smt`]'s arena -- and re-derives the gate structure
//! for each node into CNF, then runs CDCL over it.
//!
//! **One term graph, two blasters.** There are two bit-slicing functions,
//! [`crate::smt`]'s `blast` (which writes BDD node ids) and [`crate::bitblast`]'s `blast`
//! (which writes [`Lit`]s). They are kept structurally identical node-for-node on purpose.
//! What the two engines share is the *term graph*, so each operation is named once -- its
//! operands and width are fixed when the node is built -- but each blaster writes its own
//! adder, subtractor, multiplier and comparator circuit. The arithmetic is therefore *not*
//! shared code and the two circuits could diverge. The slicing is duplicated because the two
//! gate arenas are both `&mut` and cannot be one function without either splitting an arena
//! or hiding a pointer behind a trait; the divergence that duplication risks is treated as a
//! property to *check*, not to hope away -- see the header of [`crate::bitblast`],
//! `tests/differential.rs` and `tests/sat_engine.rs`. Of those, only [`crate::bitblast`]'s own
//! `tests` module actually reaches the SAT blaster: the differential corpus and the z3 oracle
//! run at widths the BDD engine finishes, so they exercise `smt::blast` and never call
//! `bitblast::blast`. A differential test between two engines proves nothing about the engine
//! that never runs.
//!
//! This is deliberately not the stronger "one bit-slicer" claim: the CNF is rebuilt from
//! the term graph rather than consumed from a BDD-produced netlist.
//!
//! What it buys is bounded, and the bound is honest: adder equivalence now settles at
//! **64 bits**, where the BDD engine alone returns `Unknown`. Wide *multiplier*
//! equivalence stays out of reach, which is the state `examples/probe.rs` documents.
//!
//! # What is here
//!
//! * [`Cnf`] -- Tseitin encoder over `and`/`or`/`xor`/`mux`, with constant folding and
//!   structural hashing, so `a & a` is one gate and `a & !a` is a constant.
//! * [`Solver`] -- CDCL: occurrence-list propagation, 1UIP learning with non-chronological
//!   backjumping, VSIDS, phase saving, restarts, and clause-database reduction with arena
//!   compaction.
//! * [`query`] -- one call is one query: encode with `f`, solve, read the model with `g`.
//!
//! # Honesty
//!
//! Fixed-capacity and heap-free, like the rest of the crate: no allocator, no OOM abort,
//! and a statically bounded worst case ([`SOLVER_BYTES`]). When a capacity runs out, or the
//! conflict budget ([`MAX_CONFLICTS`]) expires, the solver returns [`Sat::Unknown`], never
//! [`Sat::Unsat`]. Conflating the two would turn "I could not finish" into "there is no
//! counterexample", which is the one mistake a verifier must never make.

use core::fmt;

// ---------------------------------------------------------------------------
// Capacities
// ---------------------------------------------------------------------------

/// Maximum SAT variables. A bit-blasted 32-bit multiply needs a few thousand.
pub const MAX_VARS: usize = 1 << 13;
/// Maximum clauses, learnt clauses included. Learnt clauses share the arena, so this
/// bounds the search as well as the encoding.
pub const MAX_CLAUSES: usize = 1 << 15;
/// Maximum literals across all clauses.
pub const MAX_LITS: usize = 1 << 17;
/// Total literal occurrences across non-learnt clauses, for the occurrence lists.
pub const MAX_OCC: usize = MAX_LITS;
/// Number of bit-level inputs addressable, matching `smt`'s `MAX_VARS * 64`.
pub const MAX_INPUT_BITS: usize = 256 * 64;

/// Conflicts the solver will attempt before giving up.
///
/// The solver is exact but not fast: a query it cannot settle in this many conflicts is
/// reported [`Sat::Unknown`] rather than allowed to run for minutes. A verifier that hangs
/// is worse than one that says "I could not decide this", and the caller can always raise
/// the budget by rebuilding. Bit-level adder equivalence settles well inside this; a wide
/// multiplier equivalence generally does not.
pub const MAX_CONFLICTS: u64 = 50_000;

/// Worst-case solver memory in bytes, so an integrator can budget statically.
///
/// Derived from `size_of::<Solver>()` rather than hand-summed, because a hand-summed
/// constant silently goes stale the moment a field is added -- and it did, when the
/// occurrence lists and the compaction scratch were introduced.
pub const SOLVER_BYTES: usize = core::mem::size_of::<Solver>();

/// Worst-case CNF-builder memory in bytes.
pub const CNF_BYTES: usize = core::mem::size_of::<Cnf>();

// ---------------------------------------------------------------------------
// Literals
// ---------------------------------------------------------------------------

/// A SAT variable, 0-based.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct Var(pub u32);

/// A literal: a variable with a sign, encoded as `var << 1 | sign`.
///
/// The encoding makes negation `^ 1` and comparison a plain `u32` compare, which keeps
/// the propagation loop short.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Lit(pub u32);

impl Lit {
    /// The positive literal of `v`.
    pub const fn pos(v: Var) -> Lit {
        Lit(v.0 << 1)
    }
    /// The negative literal of `v`.
    pub const fn neg(v: Var) -> Lit {
        Lit((v.0 << 1) | 1)
    }
    /// The variable this literal is about.
    pub const fn var(self) -> Var {
        Var(self.0 >> 1)
    }
    /// Whether the literal is negated.
    pub const fn sign(self) -> bool {
        self.0 & 1 == 1
    }
    /// The complementary literal.
    pub const fn not(self) -> Lit {
        Lit(self.0 ^ 1)
    }
    /// Index into a per-literal array.
    const fn idx(self) -> usize {
        self.0 as usize
    }
}

/// The outcome of a SAT query.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Sat {
    /// Satisfiable; read the model with [`Solver::model_value`].
    Sat,
    /// Unsatisfiable, established by a conflict at decision level 0.
    Unsat,
    /// A fixed capacity was exhausted. Not a proof of anything.
    Unknown,
}

impl fmt::Display for Sat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Sat::Sat => f.write_str("sat"),
            Sat::Unsat => f.write_str("unsat"),
            Sat::Unknown => f.write_str("unknown (resource exhausted)"),
        }
    }
}

// ---------------------------------------------------------------------------
// CNF construction (Tseitin)
// ---------------------------------------------------------------------------

const GATE_CACHE: usize = 1 << 14;
const G_AND: u64 = 0x11;
const G_OR: u64 = 0x22;
const G_XOR: u64 = 0x44;
const G_MUX: u64 = 0x88;
const G_TRUE: u64 = 0x100;

/// A gate-level CNF builder.
///
/// Gates are added as definitions (`out <-> a & b`), not as bare clauses. That is what
/// makes the encoding *equisatisfiable*: a model of the CNF restricted to the input
/// variables is a model of the original formula, and vice versa. The differential oracles
/// depend on exactly that.
pub struct Cnf {
    clauses: [u32; MAX_LITS],
    spans: [(u32, u32); MAX_CLAUSES],
    n_clauses: usize,
    n_lits: usize,
    n_vars: usize,
    gate_key: [u64; GATE_CACHE],
    gate_val: [u32; GATE_CACHE],
    gate_mask: u32,
    /// Bit-level input index -> SAT variable, or [`NO_VAR`] if not yet requested.
    ///
    /// Inputs are addressed by `word_index * 64 + bit`, the same key `smt` uses for its BDD
    /// variables, so the two blasters agree on what "input 5, bit 3" means without a
    /// translation table. Lazy allocation keeps the SAT variable count proportional to the
    /// inputs a query actually mentions.
    input_var: [u32; MAX_INPUT_BITS],
    overflow: bool,
}

const NO_VAR: u32 = u32::MAX;

impl Cnf {
    const fn new() -> Cnf {
        Cnf {
            clauses: [0; MAX_LITS],
            spans: [(0, 0); MAX_CLAUSES],
            n_clauses: 0,
            n_lits: 0,
            n_vars: 0,
            gate_key: [u64::MAX; GATE_CACHE],
            gate_val: [0; GATE_CACHE],
            gate_mask: (GATE_CACHE - 1) as u32,
            input_var: [NO_VAR; MAX_INPUT_BITS],
            overflow: false,
        }
    }

    fn clear(&mut self) {
        self.n_clauses = 0;
        self.n_lits = 0;
        self.n_vars = 0;
        self.gate_key.fill(u64::MAX);
        self.input_var.fill(NO_VAR);
        self.overflow = false;
    }

    /// A fresh internal variable.
    pub fn new_var(&mut self) -> Var {
        if self.n_vars >= MAX_VARS {
            self.overflow = true;
            return Var((MAX_VARS - 1) as u32);
        }
        let v = Var(self.n_vars as u32);
        self.n_vars += 1;
        v
    }

    /// The SAT literal for input bit `input` (`word * 64 + bit`), created on first use.
    ///
    /// Returns a stable literal, so two references to the same input bit are the same
    /// variable and the solver sees them as equal.
    pub fn input_bit(&mut self, word: u32, bit: u32) -> Lit {
        let key = (word as usize) * 64 + bit as usize;
        if key >= MAX_INPUT_BITS {
            self.overflow = true;
            return Lit::pos(self.new_var());
        }
        if self.input_var[key] == NO_VAR {
            let v = self.new_var();
            self.input_var[key] = v.0;
            return Lit::pos(v);
        }
        Lit::pos(Var(self.input_var[key]))
    }

    /// The SAT variable for input bit `input`, if the query mentioned it.
    pub fn input_var_of(&self, input: u32) -> Option<Var> {
        let key = input as usize;
        if key >= MAX_INPUT_BITS || self.input_var[key] == NO_VAR {
            None
        } else {
            Some(Var(self.input_var[key]))
        }
    }

    /// Number of variables allocated so far.
    pub fn n_vars(&self) -> usize {
        self.n_vars
    }
    /// Number of clauses added so far.
    pub fn n_clauses(&self) -> usize {
        self.n_clauses
    }
    /// Whether a capacity was exceeded while building. An overflowing encoding must be
    /// read as `Unknown`, never as a proof.
    pub fn overflowed(&self) -> bool {
        self.overflow
    }

    fn push_clause(&mut self, lits: &[Lit]) {
        if self.n_clauses >= MAX_CLAUSES || self.n_lits + lits.len() > MAX_LITS {
            self.overflow = true;
            return;
        }
        let start = self.n_lits as u32;
        for l in lits {
            self.clauses[self.n_lits] = l.0;
            self.n_lits += 1;
        }
        self.spans[self.n_clauses] = (start, lits.len() as u32);
        self.n_clauses += 1;
    }

    /// Assert a clause of literals. An empty slice is the empty clause, i.e. a conflict.
    pub fn add_clause(&mut self, lits: &[Lit]) {
        self.push_clause(lits);
    }

    fn hash_key(kind: u64, a: u32, b: u32, c: u32) -> u64 {
        (a as u64)
            .wrapping_mul(0x9e37_79b9_7f4a_7c15)
            .wrapping_add((b as u64).wrapping_mul(0xc2b2_ae3d_27d4_eb4f))
            .wrapping_add((c as u64).wrapping_mul(0x1656_67b1_9e37_79f9))
            .wrapping_add(kind.wrapping_mul(0xd6e8_feb8_6659_fd93))
    }

    fn gate_lookup(&self, key: u64) -> Option<u32> {
        let mut i = (key as u32) & self.gate_mask;
        loop {
            let k = self.gate_key[i as usize];
            if k == u64::MAX {
                return None;
            }
            if k == key {
                return Some(self.gate_val[i as usize]);
            }
            i = (i + 1) & self.gate_mask;
        }
    }

    fn gate_insert(&mut self, key: u64, out: u32) {
        let mut i = (key as u32) & self.gate_mask;
        loop {
            let k = self.gate_key[i as usize];
            if k == u64::MAX {
                self.gate_key[i as usize] = key;
                self.gate_val[i as usize] = out;
                return;
            }
            if k == key {
                return;
            }
            i = (i + 1) & self.gate_mask;
        }
    }

    /// A literal forced true, created once and cached.
    pub fn true_lit(&mut self) -> Lit {
        let key = Self::hash_key(G_TRUE, 0, 0, 0);
        if let Some(o) = self.gate_lookup(key) {
            return Lit(o);
        }
        let l = Lit::pos(self.new_var());
        self.push_clause(&[l]);
        self.gate_insert(key, l.0);
        l
    }

    /// A literal forced false.
    pub fn false_lit(&mut self) -> Lit {
        self.true_lit().not()
    }

    /// Define `out <-> a & b`.
    pub fn and(&mut self, a: Lit, b: Lit) -> Lit {
        if a == b {
            return a;
        }
        if a.0 == b.not().0 {
            return self.false_lit();
        }
        let key = Self::hash_key(G_AND, a.0, b.0, 0);
        if let Some(o) = self.gate_lookup(key) {
            return Lit(o);
        }
        let out = Lit::pos(self.new_var());
        self.push_clause(&[a.not(), b.not(), out]);
        self.push_clause(&[a, out.not()]);
        self.push_clause(&[b, out.not()]);
        self.gate_insert(key, out.0);
        out
    }

    /// Define `out <-> a | b`.
    pub fn or(&mut self, a: Lit, b: Lit) -> Lit {
        if a == b {
            return a;
        }
        if a.0 == b.not().0 {
            return self.true_lit();
        }
        let key = Self::hash_key(G_OR, a.0, b.0, 0);
        if let Some(o) = self.gate_lookup(key) {
            return Lit(o);
        }
        let out = Lit::pos(self.new_var());
        self.push_clause(&[a, b, out.not()]);
        self.push_clause(&[a.not(), out]);
        self.push_clause(&[b.not(), out]);
        self.gate_insert(key, out.0);
        out
    }

    /// Define `out <-> a ^ b`.
    pub fn xor(&mut self, a: Lit, b: Lit) -> Lit {
        if a == b {
            return self.false_lit();
        }
        if a.0 == b.not().0 {
            return self.true_lit();
        }
        let key = Self::hash_key(G_XOR, a.0, b.0, 0);
        if let Some(o) = self.gate_lookup(key) {
            return Lit(o);
        }
        let out = Lit::pos(self.new_var());
        self.push_clause(&[a.not(), b.not(), out.not()]);
        self.push_clause(&[a, b, out.not()]);
        self.push_clause(&[a.not(), b, out]);
        self.push_clause(&[a, b.not(), out]);
        self.gate_insert(key, out.0);
        out
    }

    /// Define `out <-> (c ? t : e)`.
    pub fn mux(&mut self, c: Lit, t: Lit, e: Lit) -> Lit {
        if t == e {
            return t;
        }
        if t == c {
            return self.or(c, e);
        }
        if e == c {
            return self.and(c, t);
        }
        let key = Self::hash_key(G_MUX, c.0, t.0, e.0);
        if let Some(o) = self.gate_lookup(key) {
            return Lit(o);
        }
        let out = Lit::pos(self.new_var());
        self.push_clause(&[c.not(), t.not(), out]);
        self.push_clause(&[c.not(), t, out.not()]);
        self.push_clause(&[c, e.not(), out]);
        self.push_clause(&[c, e, out.not()]);
        self.gate_insert(key, out.0);
        out
    }
}

// ---------------------------------------------------------------------------
// CDCL
// ---------------------------------------------------------------------------

const NO_CLAUSE: u32 = u32::MAX;

/// A CDCL SAT solver.
pub struct Solver {
    lits: [u32; MAX_LITS],
    c_start: [u32; MAX_CLAUSES],
    c_len: [u32; MAX_CLAUSES],
    c_act: [f32; MAX_CLAUSES],
    c_learnt: [bool; MAX_CLAUSES],
    n_clauses: usize,
    n_lits: usize,

    n_vars: usize,
    /// 0 unassigned, 1 true, 2 false.
    assign: [u8; MAX_VARS],
    level: [u32; MAX_VARS],
    reason: [u32; MAX_VARS],
    phase: [bool; MAX_VARS],
    activity: [f32; MAX_VARS],

    /// Occurrence lists over the non-learnt clauses, indexed by literal.
    ///
    /// A flat `occ` array plus per-literal `(start, len)` spans, so literal `l`'s clauses
    /// are `occ[occ_start[l] .. occ_start[l] + occ_len[l]]`. The previous scheme kept one
    /// shared array with a per-literal *count* but no per-literal *offset*, so two literals'
    /// entries overlapped and overwrote each other; the solver then missed unit
    /// propagations and reported `Sat` for unsatisfiable queries. The differential tests
    /// caught it.
    occ: [u32; MAX_OCC],
    occ_start: [u32; 2 * MAX_VARS + 1],
    occ_len: [u32; 2 * MAX_VARS],
    /// Scratch cursor used only while filling `occ`.
    occ_cursor: [u32; 2 * MAX_VARS],
    /// Scratch for [`Solver::reduce_db`]. These are fields, not locals, so the arrays live
    /// in the `Solver`'s storage rather than on the caller's stack: two `MAX_CLAUSES`-sized
    /// arrays are ~290 KB, which was enough to overflow a 2 MB test-thread stack.
    red_cand: [(f32, u32); MAX_CLAUSES],
    /// Scratch for [`Solver::compact`]: which clauses survive, and their new ids.
    keep: [bool; MAX_CLAUSES],
    remap: [u32; MAX_CLAUSES],

    trail: [u32; MAX_VARS],
    trail_lim: [u32; MAX_VARS + 1],
    trail_n: usize,
    n_levels: usize,
    qhead: usize,

    var_inc: f32,
    clause_inc: f32,
    budget_hit: bool,
    conflicts: u64,
    decisions: u64,
    propagations: u64,
}

impl Solver {
    const fn new() -> Solver {
        Solver {
            lits: [0; MAX_LITS],
            c_start: [0; MAX_CLAUSES],
            c_len: [0; MAX_CLAUSES],
            c_act: [0.0; MAX_CLAUSES],
            c_learnt: [false; MAX_CLAUSES],
            n_clauses: 0,
            n_lits: 0,
            n_vars: 0,
            assign: [0; MAX_VARS],
            level: [0; MAX_VARS],
            reason: [NO_CLAUSE; MAX_VARS],
            phase: [false; MAX_VARS],
            activity: [0.0; MAX_VARS],
            occ: [0; MAX_OCC],
            occ_start: [0; 2 * MAX_VARS + 1],
            occ_len: [0; 2 * MAX_VARS],
            occ_cursor: [0; 2 * MAX_VARS],
            red_cand: [(0.0, 0); MAX_CLAUSES],
            keep: [false; MAX_CLAUSES],
            remap: [0; MAX_CLAUSES],
            trail: [0; MAX_VARS],
            trail_lim: [0; MAX_VARS + 1],
            trail_n: 0,
            n_levels: 0,
            qhead: 0,
            var_inc: 1.0,
            clause_inc: 1.0,
            budget_hit: false,
            conflicts: 0,
            decisions: 0,
            propagations: 0,
        }
    }

    /// Conflicts seen by the last solve, for diagnostics.
    pub fn n_conflicts(&self) -> u64 {
        self.conflicts
    }
    /// Decisions made by the last solve.
    pub fn n_decisions(&self) -> u64 {
        self.decisions
    }
    /// Propagations performed by the last solve.
    pub fn n_propagations(&self) -> u64 {
        self.propagations
    }
    /// Number of variables the solver was given.
    pub fn n_vars(&self) -> usize {
        self.n_vars
    }

    /// The value of a variable in the last model, or `None` if unassigned.
    pub fn model_value(&self, v: Var) -> Option<bool> {
        match self.assign[v.0 as usize] {
            0 => None,
            1 => Some(true),
            _ => Some(false),
        }
    }

    /// Clear the solver for a new query, in place.
    ///
    /// Deliberately does not do `*self = Solver::new()`: that materialises a ~2 MB temporary
    /// on the stack, and a test thread's stack is 2 MB, so the first query overflowed the
    /// stack. This is the same reason `smt::Ctx::reset` avoids `*self = Ctx::new()`.
    ///
    /// Only the state that *persists between queries* is cleared. The clause arrays
    /// (`lits`, `c_start`, `c_len`, `c_act`, `c_learnt`, `watch0`, `watch1`) are written by
    /// index as clauses are added and are never read past `n_clauses`, so they need no
    /// clearing; the watch *list* is rebuilt from `watch_head` on attach.
    fn reset(&mut self) {
        self.n_clauses = 0;
        self.n_lits = 0;
        self.n_vars = 0;
        self.trail_n = 0;
        self.n_levels = 0;
        self.qhead = 0;
        self.var_inc = 1.0;
        self.clause_inc = 1.0;
        self.budget_hit = false;
        self.conflicts = 0;
        self.decisions = 0;
        self.propagations = 0;
        // Per-variable state must be cleared: a variable index is reused from 0 each query,
        // so a stale assignment would be read as if it belonged to the new query.
        self.assign.fill(0);
        self.level.fill(0);
        self.reason.fill(NO_CLAUSE);
        self.phase.fill(false);
        self.activity.fill(0.0);
    }

    fn add_clause(&mut self, lits: &[u32], learnt: bool) -> u32 {
        if self.n_clauses >= MAX_CLAUSES || self.n_lits + lits.len() > MAX_LITS {
            // A learnt clause that does not fit is not fatal: drop the low-value learnt
            // clauses and try again. Without this the literal arena fills with learnt
            // clauses that are never freed, and a query the solver could still decide is
            // reported `Unknown`. Original clauses are never dropped, so the retry cannot
            // make the formula weaker.
            if learnt && self.n_clauses < MAX_CLAUSES {
                self.reduce_db();
                if self.n_lits + lits.len() <= MAX_LITS {
                    // fall through and append
                } else {
                    self.budget_hit = true;
                    return NO_CLAUSE;
                }
            } else {
                self.budget_hit = true;
                return NO_CLAUSE;
            }
        }
        let id = self.n_clauses as u32;
        let start = self.n_lits as u32;
        for &l in lits {
            self.lits[self.n_lits] = l;
            self.n_lits += 1;
        }
        let ci = id as usize;
        self.c_start[ci] = start;
        self.c_len[ci] = lits.len() as u32;
        self.c_act[ci] = if learnt { self.clause_inc } else { 0.0 };
        self.c_learnt[ci] = learnt;
        self.n_clauses += 1;
        id
    }

    /// Build the occurrence lists from the clauses loaded so far.
    ///
    /// Learnt clauses are excluded: they are asserted at a level and are never a unit
    /// propagation source for a *later* assignment, so including them only costs work.
    /// Every literal is walked once to count, once to prefix-sum, once to place.
    fn build_occ(&mut self) {
        self.occ_len.fill(0);
        self.occ_cursor.fill(0);
        for id in 0..self.n_clauses {
            let len = self.c_len[id];
            if len < 2 {
                continue;
            }
            let start = self.c_start[id] as usize;
            for j in 0..len as usize {
                let l = self.lits[start + j] as usize;
                self.occ_len[l] += 1;
            }
        }
        let mut acc = 0u32;
        for l in 0..2 * MAX_VARS {
            self.occ_start[l] = acc;
            acc += self.occ_len[l];
        }
        self.occ_start[2 * MAX_VARS] = acc;
        if acc as usize > MAX_OCC {
            // Clamping would silently drop occurrences and make the solver unsound, so
            // record the overflow instead and let `solve` report `Unknown`.
            self.budget_hit = true;
            return;
        }
        for l in 0..2 * MAX_VARS {
            self.occ_cursor[l] = self.occ_start[l];
        }
        for id in 0..self.n_clauses {
            let len = self.c_len[id];
            if len < 2 {
                continue;
            }
            let start = self.c_start[id] as usize;
            for j in 0..len as usize {
                let l = self.lits[start + j] as usize;
                let c = self.occ_cursor[l] as usize;
                self.occ[c] = id as u32;
                self.occ_cursor[l] += 1;
            }
        }
    }

    /// 1 true, 0 false, -1 unassigned.
    fn value_lit(&self, l: Lit) -> i8 {
        match self.assign[l.var().0 as usize] {
            0 => -1,
            1 => {
                if l.sign() {
                    0
                } else {
                    1
                }
            }
            _ => {
                if l.sign() {
                    1
                } else {
                    0
                }
            }
        }
    }

    fn enqueue(&mut self, l: Lit, reason: u32) -> bool {
        let v = l.var().0 as usize;
        if self.trail_n >= MAX_VARS {
            self.budget_hit = true;
            return false;
        }
        self.assign[v] = if l.sign() { 2 } else { 1 };
        self.level[v] = self.n_levels as u32;
        self.reason[v] = reason;
        self.phase[v] = !l.sign();
        self.trail[self.trail_n] = l.0;
        self.trail_n += 1;
        true
    }

    fn bump_var(&mut self, v: usize) {
        self.activity[v] += self.var_inc;
        if self.activity[v] > 1e30 {
            for a in self.activity.iter_mut() {
                *a *= 1e-30;
            }
            self.var_inc *= 1e-30;
        }
    }

    /// Propagate pending assignments. Returns the conflicting clause id, or [`NO_CLAUSE`].
    ///
    /// For each clause containing the falsified literal, rescan it. If it is satisfied, do
    /// nothing; if it has exactly one unassigned literal, assign it; if it has none, that
    /// clause is the conflict. Rescanning is O(clause length) per occurrence rather than
    /// O(1) like two-watched-literal propagation, but it has no per-literal bookkeeping to
    /// corrupt and the bit-blasted clauses are short.
    fn propagate(&mut self) -> u32 {
        while self.qhead < self.trail_n {
            let l = Lit(self.trail[self.qhead]);
            self.qhead += 1;
            self.propagations += 1;
            let li = l.not().idx();
            let s = self.occ_start[li] as usize;
            let n = self.occ_len[li] as usize;
            for k in 0..n {
                let id = self.occ[s + k];
                let ci = id as usize;
                let len = self.c_len[ci] as usize;
                let start = self.c_start[ci] as usize;
                let mut unassigned = 0u32;
                let mut nun = 0u32;
                let mut satisfied = false;
                for j in 0..len {
                    let q = Lit(self.lits[start + j]);
                    match self.value_lit(q) {
                        1 => {
                            satisfied = true;
                            break;
                        }
                        -1 => {
                            nun += 1;
                            unassigned = q.0;
                        }
                        _ => {}
                    }
                }
                if satisfied {
                    continue;
                }
                if nun == 0 {
                    return id;
                }
                if nun == 1 && !self.enqueue(Lit(unassigned), id) {
                    return NO_CLAUSE;
                }
            }
        }
        NO_CLAUSE
    }

    fn pick_branch(&self) -> Option<Var> {
        let mut best: Option<usize> = None;
        let mut best_act = -1.0f32;
        for v in 0..self.n_vars {
            if self.assign[v] != 0 {
                continue;
            }
            if self.activity[v] > best_act {
                best_act = self.activity[v];
                best = Some(v);
            }
        }
        best.map(|v| Var(v as u32))
    }

    /// Analyze a conflict into a 1UIP learnt clause.
    ///
    /// Returns `(len, backjump_level)`, with the asserting literal in `out[0]` and the
    /// highest-level literal of the rest in `out[1]`, so the clause is unit after the
    /// backjump and the solver can enqueue `out[0]`.
    ///
    /// `out[0]` is the *negation* of the 1UIP literal on the trail. The conflict proves the
    /// 1UIP cannot hold, so the learnt clause asserts its opposite; taking the trail literal
    /// un-negated produces a clause that re-asserts the assignment that just conflicted, and
    /// the solver then reports `Unsat` for satisfiable formulas. `tests/sat_engine.rs` is the
    /// check that catches that.
    fn analyze(
        &mut self,
        conflict: u32,
        out: &mut [u32; MAX_VARS],
        seen: &mut [bool; MAX_VARS],
        touched: &mut [u32; MAX_VARS],
    ) -> (usize, u32) {
        // `out[0]` is reserved for the 1UIP, so the other literals start at 1.
        let mut n = 1usize;
        let mut ntouch = 0usize;
        let mut path_c = 0usize;
        let mut resolved = u32::MAX;
        let mut clause = conflict;
        let mut idx = self.trail_n;
        let mut uip = 0u32;

        loop {
            let start = self.c_start[clause as usize] as usize;
            let len = self.c_len[clause as usize] as usize;
            for j in 0..len {
                let l = Lit(self.lits[start + j]);
                if l.0 == resolved {
                    // The literal this clause propagated; it was already accounted for.
                    continue;
                }
                let v = l.var().0 as usize;
                if !seen[v] && self.level[v] > 0 {
                    seen[v] = true;
                    if ntouch < MAX_VARS {
                        touched[ntouch] = v as u32;
                        ntouch += 1;
                    }
                    self.bump_var(v);
                    if self.level[v] == self.n_levels as u32 {
                        path_c += 1;
                    } else {
                        out[n] = l.0;
                        n += 1;
                    }
                }
            }
            // Walk the trail newest-first to the next literal still on the conflict path.
            while idx > 0 && !seen[Lit(self.trail[idx - 1]).var().0 as usize] {
                idx -= 1;
            }
            if idx == 0 {
                // Unreachable for a genuine conflict: the conflict clause's own literal is
                // always on the trail. Stop rather than index out of bounds.
                break;
            }
            idx -= 1;
            let p = Lit(self.trail[idx]);
            let v = p.var().0 as usize;
            seen[v] = false;
            resolved = p.0;
            uip = p.0;
            path_c -= 1;
            if path_c == 0 {
                break;
            }
            clause = self.reason[v];
            if clause == NO_CLAUSE {
                // A decision literal is the end of the path.
                break;
            }
        }

        // Clear every flag this call set, so the next `analyze` starts clean.
        for i in 0..ntouch {
            seen[touched[i] as usize] = false;
        }

        // The learnt clause asserts the opposite of the 1UIP.
        out[0] = uip ^ 1;
        if n == 1 {
            return (1, 0);
        }
        // Backjump to the highest level among the rest, and make it the second literal so
        // the clause is watched/asserting there.
        let mut best = 1usize;
        let mut best_lv = self.level[Lit(out[1]).var().0 as usize];
        for (i, &lit) in out.iter().enumerate().take(n).skip(2) {
            let lv = self.level[Lit(lit).var().0 as usize];
            if lv > best_lv {
                best_lv = lv;
                best = i;
            }
        }
        out.swap(1, best);
        (n, best_lv)
    }

    fn backtrack(&mut self, level: u32) {
        if self.n_levels <= level as usize {
            return;
        }
        let bound = self.trail_lim[level as usize + 1] as usize;
        let mut i = self.trail_n;
        while i > bound {
            i -= 1;
            let v = Lit(self.trail[i]).var().0 as usize;
            self.assign[v] = 0;
            self.reason[v] = NO_CLAUSE;
        }
        self.trail_n = bound;
        self.qhead = bound;
        self.n_levels = level as usize;
    }

    /// Drop low-activity learnt clauses, then compact the clause arena.
    ///
    /// A clause is kept if it is an original clause, is currently a propagation reason, or
    /// is among the higher-activity half of the learnt clauses. Everything else is removed
    /// and the surviving literals are moved down, so the space is actually reclaimed.
    ///
    /// Tombstoning alone is not enough: a tombstoned clause keeps its literals in the
    /// arena, so a search that learns many clauses exhausts `MAX_LITS` and reports
    /// `Unknown` even though most of those clauses are worthless.
    fn reduce_db(&mut self) {
        self.keep.fill(false);
        for id in 0..self.n_clauses {
            if !self.c_learnt[id] {
                self.keep[id] = true;
            }
        }
        // Anything currently justifying a trail assignment must survive, or the trail would
        // no longer be justified and `analyze` would follow a reason to a removed clause.
        for t in 0..self.trail_n {
            let v = Lit(self.trail[t]).var().0 as usize;
            let r = self.reason[v];
            if r != NO_CLAUSE {
                self.keep[r as usize] = true;
            }
        }
        let mut m = 0usize;
        for id in 0..self.n_clauses {
            if self.c_learnt[id] && !self.keep[id] {
                self.red_cand[m] = (self.c_act[id], id as u32);
                m += 1;
            }
        }
        if m < 4 {
            return;
        }
        for i in 1..m {
            let key = self.red_cand[i];
            let mut j = i;
            while j > 0 && self.red_cand[j - 1].0 < key.0 {
                self.red_cand[j] = self.red_cand[j - 1];
                j -= 1;
            }
            self.red_cand[j] = key;
        }
        // Keep the more active half of the removable clauses.
        for k in 0..(m / 2) {
            let id = self.red_cand[k].1;
            self.keep[id as usize] = true;
        }
        self.compact();
    }

    /// Re-layout the clause arena, keeping only the clauses `self.keep` marks.
    ///
    /// Ids change, so `reason` is remapped and the occurrence lists are rebuilt. Literals
    /// are copied forward (destination never past source, because ids only shrink), so this
    /// works in place.
    fn compact(&mut self) {
        let mut new_n = 0u32;
        for id in 0..self.n_clauses {
            if self.keep[id] {
                self.remap[id] = new_n;
                new_n += 1;
            } else {
                self.remap[id] = NO_CLAUSE;
            }
        }
        let mut new_lits = 0u32;
        for id in 0..self.n_clauses {
            if !self.keep[id] {
                continue;
            }
            let ni = self.remap[id] as usize;
            let start = self.c_start[id] as usize;
            let len = self.c_len[id] as usize;
            let dst = new_lits as usize;
            if dst != start {
                for j in 0..len {
                    self.lits[dst + j] = self.lits[start + j];
                }
            }
            self.c_start[ni] = new_lits;
            self.c_len[ni] = len as u32;
            self.c_act[ni] = self.c_act[id];
            self.c_learnt[ni] = self.c_learnt[id];
            new_lits += len as u32;
        }
        self.n_clauses = new_n as usize;
        self.n_lits = new_lits as usize;
        for v in 0..self.n_vars {
            let r = self.reason[v];
            if r != NO_CLAUSE {
                self.reason[v] = self.remap[r as usize];
            }
        }
        self.build_occ();
    }

    fn load(&mut self, cnf: &Cnf) {
        self.n_vars = cnf.n_vars;
        for id in 0..cnf.n_clauses {
            let (start, len) = cnf.spans[id];
            let lits = &cnf.clauses[start as usize..(start + len) as usize];
            self.add_clause(lits, false);
        }
    }

    /// Solve. The clauses must already be loaded via `Solver::load`.
    pub fn solve(&mut self) -> Sat {
        self.build_occ();
        if self.budget_hit {
            return Sat::Unknown;
        }
        // Seed unit clauses onto the trail before searching.
        //
        // Without this the search starts with nothing assigned, so a formula whose only
        // force is a unit clause -- including the trivial `[l] ∧ [¬l]` that an asserted
        // constant produces -- looks satisfiable and the solver returns `Sat` for an
        // unsatisfiable query. That is a *wrong verdict*, not a missed optimisation, so it
        // is done here rather than left to propagation: watched literals only fire when a
        // literal is falsified, and a unit clause has no second literal to watch.
        for id in 0..self.n_clauses {
            match self.c_len[id] {
                0 => return Sat::Unsat,
                1 => {
                    let l = Lit(self.lits[self.c_start[id] as usize]);
                    match self.value_lit(l) {
                        0 => return Sat::Unsat,
                        -1 if !self.enqueue(l, id as u32) => return Sat::Unknown,
                        _ => {}
                    }
                }
                _ => {}
            }
        }
        self.trail_lim[0] = 0;
        let mut seen = [false; MAX_VARS];
        let mut touched = [0u32; MAX_VARS];
        let mut learnt = [0u32; MAX_VARS];
        const RESTART_BUDGET: u64 = 1024;
        let mut next_restart: u64 = RESTART_BUDGET;

        loop {
            if self.budget_hit || self.conflicts >= MAX_CONFLICTS {
                return Sat::Unknown;
            }
            let conflict = self.propagate();
            if conflict != NO_CLAUSE {
                self.conflicts += 1;
                if self.n_levels == 0 {
                    return Sat::Unsat;
                }
                let (n, bt) = self.analyze(conflict, &mut learnt, &mut seen, &mut touched);
                if n == 0 {
                    return Sat::Unknown;
                }
                self.backtrack(bt);
                let id = self.add_clause(&learnt[..n], true);
                if id == NO_CLAUSE {
                    return Sat::Unknown;
                }
                let asserting = Lit(learnt[0]);
                match self.value_lit(asserting) {
                    0 => return Sat::Unsat,
                    -1 if !self.enqueue(asserting, id) => return Sat::Unknown,
                    _ => {}
                }
                self.var_inc /= 0.95;
                self.clause_inc /= 0.999;
                if self.conflicts % 2000 == 0 {
                    self.reduce_db();
                }
                if self.conflicts >= next_restart {
                    next_restart = self.conflicts + RESTART_BUDGET;
                    self.backtrack(0);
                }
                continue;
            }
            match self.pick_branch() {
                None => return Sat::Sat,
                Some(v) => {
                    self.decisions += 1;
                    self.n_levels += 1;
                    if self.n_levels >= MAX_VARS {
                        return Sat::Unknown;
                    }
                    self.trail_lim[self.n_levels] = self.trail_n as u32;
                    let lit = if self.phase[v.0 as usize] {
                        Lit::pos(v)
                    } else {
                        Lit::neg(v)
                    };
                    if !self.enqueue(lit, NO_CLAUSE) {
                        return Sat::Unknown;
                    }
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Arena storage
// ---------------------------------------------------------------------------

/// Number of word indices a model can report, matching `smt`'s `MAX_VARS`.
pub const MAX_WORDS: usize = 256;
/// Words of bitset needed for `MAX_WORDS * 64` input bits.
const MODEL_WORDS: usize = MAX_WORDS;

/// A snapshot of the SAT model over the *input* bits.
///
/// Taken while the solver is alive so the caller can build a counterexample afterwards,
/// without holding a borrow on either arena. A bit is `present` only if the query mentioned
/// it, which is what lets the caller tell "constrained to 0" from "unconstrained".
#[derive(Clone, Copy)]
pub struct Model {
    present: [u64; MODEL_WORDS],
    value: [u64; MODEL_WORDS],
}

impl Model {
    const fn empty() -> Model {
        Model { present: [0; MODEL_WORDS], value: [0; MODEL_WORDS] }
    }

    fn set(&mut self, input: u32, v: bool) {
        let w = (input as usize) >> 6;
        let b = input & 63;
        if w < MODEL_WORDS {
            self.present[w] |= 1u64 << b;
            if v {
                self.value[w] |= 1u64 << b;
            }
        }
    }

    /// The value of input bit `input`, or `None` if the query never mentioned it.
    pub fn bit(&self, input: u32) -> Option<bool> {
        let w = (input as usize) >> 6;
        let b = input & 63;
        if w < MODEL_WORDS && self.present[w] & (1u64 << b) != 0 {
            Some(self.value[w] & (1u64 << b) != 0)
        } else {
            None
        }
    }
}

// The arenas live in `static`s, not in a thread-local.
//
// A `thread_local!` initialiser is a *temporary* `Cnf`/`Solver` on the stack that is then
// copied into the thread-local slot, so a 2 MB test thread had to hold a whole ~3 MB arena
// before any query ran, and it overflowed. `static`s have no such temporary: the storage is
// in the binary's BSS and is only ever borrowed.
//
// Sharing one arena across threads needs a lock, so on `std` the borrow is a `Mutex` guard
// rather than a `RefCell` borrow. The bare-metal build is single-threaded by contract,
// exactly as `smt::with_ctx` documents, so it uses the raw statics and no lock.
//
// The consequence is stated plainly rather than left to be discovered: the `std` build
// **serializes** every SAT query, including the encoding, because both `Mutex` guards are
// held for the whole of [`query`]. The BDD engine does not, since `smt::with_ctx` is a
// `thread_local!` on `std`; so two threads running hard proofs that fall back to SAT run
// one after the other rather than in parallel. This is a throughput cost, not a
// correctness one -- the solver is deterministic and the lock is never taken in the other
// order -- and it is the price of a compile-time-sized arena in BSS with no allocator. A
// per-thread arena would need either an allocator or a fixed pool, and neither is worth
// the complexity for the queries this engine is meant to answer.
#[cfg(feature = "std")]
static CNF: std::sync::Mutex<Cnf> = std::sync::Mutex::new(Cnf::new());
#[cfg(feature = "std")]
static SOLVER: std::sync::Mutex<Solver> = std::sync::Mutex::new(Solver::new());

#[cfg(not(feature = "std"))]
static mut CNF: Cnf = Cnf::new();
#[cfg(not(feature = "std"))]
static mut SOLVER: Solver = Solver::new();

/// Build a CNF with `f` (which returns the literal to assert), solve it, and return the
/// verdict plus a snapshot of the input model.
///
/// One call is one query: the CNF and the solver are reset first, so a fresh encode never
/// sees the previous query's clauses. Keeping encode and solve inside one closure also makes
/// it unrepresentable to hold a `Cnf` across a reset -- the stale-handle trap
/// [`crate::smt`] documents.
///
/// The two arenas are separate `Mutex`es, taken in the order CNF then SOLVER. Nothing takes
/// them in the other order, so this cannot deadlock.
#[cfg(feature = "std")]
pub fn query(f: impl FnOnce(&mut Cnf) -> Lit) -> (Sat, Model) {
    // A poisoned lock means a previous query panicked while holding it. The arena is
    // rebuilt from scratch by `clear()`/`reset()` before use, so the poison carries no
    // information worth propagating; recovering keeps one panic from disabling the engine.
    let mut cnf = match CNF.lock() {
        Ok(g) => g,
        Err(p) => p.into_inner(),
    };
    cnf.clear();
    let goal = f(&mut cnf);
    cnf.add_clause(&[goal]);
    let mut sol = match SOLVER.lock() {
        Ok(g) => g,
        Err(p) => p.into_inner(),
    };
    sol.reset();
    sol.load(&cnf);
    let r = sol.solve();
    let mut m = Model::empty();
    if r == Sat::Sat {
        for input in 0..MAX_INPUT_BITS as u32 {
            if let Some(v) = cnf.input_var_of(input) {
                if let Some(b) = sol.model_value(v) {
                    m.set(input, b);
                }
            }
        }
    }
    (r, m)
}

/// See the `std` version. The `no_std` build has one arena, so the same re-entrancy
/// obligation as `smt::with_ctx` applies.
#[cfg(not(feature = "std"))]
pub fn query(f: impl FnOnce(&mut Cnf) -> Lit) -> (Sat, Model) {
    // SAFETY: as in `smt::with_ctx`: the arenas are `!Send`/`!Sync` and a bare-metal build
    // is single-threaded; a re-entrant call from an interrupt is the caller's obligation,
    // which the crate documents.
    unsafe {
        let cnf = &mut *core::ptr::addr_of_mut!(CNF);
        let sol = &mut *core::ptr::addr_of_mut!(SOLVER);
        cnf.clear();
        let goal = f(cnf);
        cnf.add_clause(&[goal]);
        sol.reset();
        sol.load(cnf);
        let r = sol.solve();
        let mut m = Model::empty();
        if r == Sat::Sat {
            for input in 0..MAX_INPUT_BITS as u32 {
                if let Some(v) = cnf.input_var_of(input) {
                    if let Some(b) = sol.model_value(v) {
                        m.set(input, b);
                    }
                }
            }
        }
        (r, m)
    }
}

#[cfg(all(test, feature = "std"))]
mod reduce_db_tests {
    //! The oracle for [`Solver::reduce_db`]'s soundness guard.
    //!
    //! The rest of the crate reaches `reduce_db` only through a search hard enough to
    //! cross the 2000-conflict reduction interval. `tests/sat_engine.rs` uses 1..=6
    //! variable CNFs, which decide in a handful of conflicts, and the BDD-backed tests
    //! never touch this file at all. So the only checks on the reduction path were
    //! incidental: deleting the guard entirely left every test green.
    //!
    //! The guard is the loop that marks every clause currently justifying a trail
    //! assignment as `keep`. Without it `compact` removes a clause that a trail entry
    //! points at, `reason[v]` remaps to `NO_CLAUSE`, and a propagated literal becomes
    //! indistinguishable from a decision. The verdict usually stays correct, which is
    //! exactly why a verdict-level test cannot see the damage: `analyze` then stops at a
    //! reason-less literal and learns a weaker clause than it should.
    //!
    //! So the oracle drives `reduce_db` on a hand-built trail and asserts two things the
    //! verdict cannot show:
    //!
    //! * every surviving reason clause is a *real justification* -- it contains the
    //!   literal it propagated and every other literal in it is false; and
    //! * `compact` remaps a reason to the *same clause*, compared by literal content,
    //!   not merely to some in-range id.
    //!
    //! The second point is the one that is easy to get wrong. Checking `reason[v] <
    //! n_clauses` passes as long as *any* clause survives, so it would accept a remap
    //! that pointed at an unrelated clause. Comparing the literal set is what pins the
    //! clause's identity across the renumbering.

    use super::*;

    /// Each decision level must hold exactly one reason-free literal (its decision), and
    /// that literal must be the first entry of the level.
    ///
    /// Returns the first level that breaks the rule, with how many reason-free literals it
    /// held, or `None` when the trail is well formed.
    fn first_bad_level(s: &Solver) -> Option<(usize, usize)> {
        for lvl in 1..=s.n_levels {
            let lo = s.trail_lim[lvl] as usize;
            let hi = if lvl < s.n_levels {
                s.trail_lim[lvl + 1] as usize
            } else {
                s.trail_n
            };
            let mut reasonless = 0usize;
            let mut first_is_reasonless = false;
            for t in lo..hi {
                let v = Lit(s.trail[t]).var().0 as usize;
                if s.reason[v] == NO_CLAUSE {
                    reasonless += 1;
                    if t == lo {
                        first_is_reasonless = true;
                    }
                }
            }
            if reasonless != 1 || !first_is_reasonless {
                return Some((lvl, reasonless));
            }
        }
        None
    }

    /// Whether clause `id` really justifies assigning the literal `l` to true: it must
    /// contain `l`, and every *other* literal in it must be false under the current
    /// assignment. That is the unit-propagation condition, and it is the whole content of
    /// "this clause is the reason for that assignment".
    fn clause_justifies(s: &Solver, id: u32, l: u32) -> bool {
        let start = s.c_start[id as usize] as usize;
        let len = s.c_len[id as usize] as usize;
        let mut found = false;
        for j in 0..len {
            let m = s.lits[start + j];
            if m == l {
                found = true;
                continue;
            }
            // `assign[v]` is 1 for true and 2 for false. A positive literal is false when
            // its variable is false; a negative literal is false when its variable is true.
            let a = s.assign[Lit(m).var().0 as usize];
            let is_false = if Lit(m).sign() { a == 1 } else { a == 2 };
            if !is_false {
                return false;
            }
        }
        found
    }

    /// Whether clause `id`'s literals are exactly `expected`, order aside. This is the
    /// clause-identity check: a remap must land on the same clause, not just a live one.
    fn clause_is(s: &Solver, id: u32, expected: &[u32]) -> bool {
        let start = s.c_start[id as usize] as usize;
        let len = s.c_len[id as usize] as usize;
        if len != expected.len() {
            return false;
        }
        (0..len).all(|j| expected.contains(&s.lits[start + j]))
    }

    /// Every trail literal with a reason must be justified by that clause.
    fn first_unjustified(s: &Solver) -> Option<usize> {
        for t in 0..s.trail_n {
            let l = s.trail[t];
            let v = Lit(l).var().0 as usize;
            let r = s.reason[v];
            if r == NO_CLAUSE {
                continue;
            }
            if !clause_justifies(s, r, l) {
                return Some(v);
            }
        }
        None
    }

    // The literal sets of the two reason clauses, so a remap can be compared by content.
    // Derived from `Lit` rather than written as raw bit patterns, because a hand-computed
    // encoding is exactly the kind of constant that drifts silently.
    fn reason_x2_lits() -> [u32; 2] {
        [Lit::pos(Var(2)).0, Lit::neg(Var(6)).0] // (x2 | ¬x6)
    }
    fn reason_x4_lits() -> [u32; 2] {
        [Lit::pos(Var(4)).0, Lit::neg(Var(7)).0] // (x4 | ¬x7)
    }

    /// Fill the shared solver with a trail whose two propagated literals are justified by
    /// genuine unit clauses, plus enough removable learnt clauses that `reduce_db` passes
    /// its `m < 4` early return and actually compacts.
    ///
    /// The state is built by hand rather than searched for, so the test is fast and its
    /// teeth do not depend on a particular seed or conflict count. The solver comes from
    /// the shared static: a `Solver` is 2.2 MB, which overflows the test thread's stack.
    ///
    /// The two reason clauses carry *low* activity so that, with the guard removed, the
    /// "keep the more active half" rule drops them and the damage is real rather than
    /// hidden behind a lucky tie. With every clause at the same activity the sort is
    /// stable by id, the low ids survive, and the guard would look unnecessary.
    fn solver_with_learnt_reasons() -> std::sync::MutexGuard<'static, Solver> {
        let mut s = SOLVER.lock().unwrap_or_else(|p| p.into_inner());
        s.reset();
        s.n_vars = 8;

        // Original clause 0: (x0 | x1). Never removed (not learnt).
        let _ = s.add_clause(&[Lit::pos(Var(0)).0, Lit::pos(Var(1)).0], false);

        // Six learnt clauses that nothing points at, with high activity so the
        // "keep the more active half" rule prefers them.
        for v in 0..6u32 {
            let a = Lit::pos(Var(10 + v));
            let b = Lit::pos(Var(11 + v));
            let id = s.add_clause(&[a.0, b.0], true);
            s.c_act[id as usize] = 100.0 + v as f32;
        }

        // (x2 | x6): with x6 false this is unit on x2, so it is a real reason for x2.
        let reason_x2 = s.add_clause(&reason_x2_lits(), true);
        s.c_act[reason_x2 as usize] = 1.0;
        // (x4 | x7): likewise for x4 with x7 false.
        let reason_x4 = s.add_clause(&reason_x4_lits(), true);
        s.c_act[reason_x4 as usize] = 1.0;
        s.build_occ();

        // Two decision levels, laid out the way `solve` lays them out: `trail_lim[lvl]` is
        // the index of the first trail entry at `lvl`, and the decision is that entry.
        // Level 1 decides x6 true; level 2 decides x7 true and then propagates x2 and x4.
        // With x6 true the `¬x6` in `(x2 | ¬x6)` is false, so the clause is unit on x2 and
        // is a genuine reason for it; likewise x7 for x4.
        s.n_levels = 1;
        s.trail_lim[1] = 0;
        s.enqueue(Lit::pos(Var(6)), NO_CLAUSE);
        s.n_levels = 2;
        s.trail_lim[2] = s.trail_n as u32;
        s.enqueue(Lit::pos(Var(7)), NO_CLAUSE);
        s.enqueue(Lit::pos(Var(2)), reason_x2);
        s.enqueue(Lit::pos(Var(4)), reason_x4);
        s.qhead = s.trail_n;

        s
    }

    #[test]
    fn a_hand_built_trail_is_well_formed_and_justified_before_reduction() {
        let s = solver_with_learnt_reasons();
        assert_eq!(
            first_bad_level(&s),
            None,
            "the fixture itself must satisfy the invariant, or the test proves nothing"
        );
        assert_eq!(
            first_unjustified(&s),
            None,
            "the fixture's reason clauses must genuinely justify their literals"
        );
    }

    #[test]
    fn reduce_db_keeps_every_clause_that_justifies_a_trail_literal() {
        let mut s = solver_with_learnt_reasons();
        assert_ne!(s.reason[2], NO_CLAUSE);
        assert_ne!(s.reason[4], NO_CLAUSE);

        s.reduce_db();

        // Both reasons must still name a live clause, and it must still be a real
        // justification: the clause contains the propagated literal and every other
        // literal in it is false. A dropped reason shows up as `NO_CLAUSE`, which turns the
        // propagated literal into a phantom decision.
        assert_ne!(
            s.reason[2], NO_CLAUSE,
            "reduce_db dropped the clause justifying x2"
        );
        assert_ne!(
            s.reason[4], NO_CLAUSE,
            "reduce_db dropped the clause justifying x4"
        );
        assert_eq!(
            first_unjustified(&s),
            None,
            "reduce_db left a trail literal whose reason clause no longer justifies it"
        );
        assert_eq!(
            first_bad_level(&s),
            None,
            "reduce_db left a propagated literal looking like a decision"
        );
    }

    #[test]
    fn compact_remaps_a_reason_to_the_same_clause_not_just_a_live_one() {
        let mut s = solver_with_learnt_reasons();
        s.reduce_db();
        // The reason must point at *the same clause*, identified by its literals. Checking
        // only `reason < n_clauses` would pass for any surviving clause, including one that
        // says nothing about the literal it is supposed to justify.
        for (v, expected) in [(2usize, reason_x2_lits()), (4usize, reason_x4_lits())] {
            let r = s.reason[v];
            assert_ne!(r, NO_CLAUSE, "the reason for x{v} was dropped");
            assert!(
                (r as usize) < s.n_clauses,
                "reason for x{v} is clause {r}, but only {} clauses survive",
                s.n_clauses
            );
            assert!(
                clause_is(&s, r, &expected),
                "reason for x{v} remapped to a different clause (id {r})"
            );
        }
    }

    /// A remap that lands on a live but *wrong* clause must be caught. This is the case
    /// the range check alone cannot see, so the test pins it directly by asking whether the
    /// identity check distinguishes two clauses that are both alive.
    #[test]
    fn the_clause_identity_check_distinguishes_two_live_clauses() {
        let s = solver_with_learnt_reasons();
        let r2 = s.reason[2];
        let r4 = s.reason[4];
        assert_ne!(r2, r4, "the fixture's two reasons must be different clauses");
        assert!(
            clause_is(&s, r2, &reason_x2_lits()),
            "clause {r2} should be the x2 reason"
        );
        assert!(
            !clause_is(&s, r2, &reason_x4_lits()),
            "clause {r2} must not also look like the x4 reason"
        );
        assert!(
            clause_is(&s, r4, &reason_x4_lits()),
            "clause {r4} should be the x4 reason"
        );
        assert!(
            !clause_is(&s, r4, &reason_x2_lits()),
            "clause {r4} must not also look like the x2 reason"
        );
    }
}

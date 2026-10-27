//! Shared IR for the differential oracles.
//!
//! This module is compiled into two separate example binaries, `kanidiff` and `verusdiff`.
//! Each uses one of the two source generators (`rust_word`/`rust_pred` for Kani,
//! `verus_word`/`verus_pred` for Verus) and sees the other as unused, so `dead_code` is
//! allowed here rather than at each call site.
//!
//! `z3diff` checks the *exporter* (does the printed query mean what the engine proved?).
//! The `kanidiff` and `verusdiff` harnesses check the *engine*, by compiling each predicate
//! the engine proved into a real program and asking an independent verifier (Kani, or
//! Verus) to prove the same property of that program.
//!
//! The cases live here, in one place, for one reason: if each harness carried its own
//! corpus and generator, "the engine agrees with Kani" and "the engine agrees with Verus"
//! would be claims about two different sets of formulas, and neither would say much. One
//! IR, three backends (the engine, Kani, Verus) means a case that any backend mishandles is
//! visible as a disagreement rather than as a harness-specific blind spot.
//!
//! The IR is also why the generated code describes the *same* property as the predicate:
//! the two are interpretations of one tree, not two independent generations. Generating
//! them separately would compare unrelated formulas and every disagreement would be noise.
#![allow(dead_code)]

use discharge::smt::{self, Pred, Var};

/// Width of every word. Everything is `u8` so both sides stay well-sorted: the engine
/// refuses mixed-width comparisons, and a case it refuses makes no claim to confirm.
pub const W: u8 = 8;
/// The parameters every case is built over. Three reaches every binary operator and `ite`.
pub const PARAMS: [&str; 3] = ["a", "b", "c"];

/// A small linear-congruential generator, so the sweeps are reproducible from a seed.
pub struct Lcg(pub u64);
impl Lcg {
    pub fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0 >> 33
    }
    pub fn below(&mut self, n: u64) -> u64 {
        if n == 0 { 0 } else { self.next() % n }
    }
}

/// Interpret a word tree as a Rust expression of type `u8`, for the Kani backend.
///
/// The translation is the whole content of the Kani harness, so it is written to be
/// auditable by eye: `Add` is `wrapping_add` because the engine's `Add` wraps, and `Mask`
/// is `& ((1<<k)-1)` because the engine's narrowing `truncate` keeps the low bits. A mistake
/// *here* shows up as a mismatch, which is the right outcome -- the harness reports its own
/// bug rather than silently vouching for the engine.
///
/// Shifts go through the emitted helpers `shl_eng`/`lshr_eng`/`ashr_eng`, and the reason is
/// a *real* divergence the first version of this harness tripped over. The engine defines a
/// shift by `k >= width` to be 0 (or the sign bit), the SMT-LIB rule its tests pin. Rust
/// does not: `x << 8` on a `u8` is an arithmetic-overflow *error* at compile time and panics
/// at run time. Emitting `x << k` would either fail to compile or check a different
/// operation, so the helpers spell the engine's rule out in Rust.
pub fn rust_word(e: &WExpr) -> String {
    match e {
        WExpr::Const(k) => format!("{k}u8"),
        WExpr::Param(i) => PARAMS[*i].to_string(),
        WExpr::Add(x, y) => format!("({}).wrapping_add({})", rust_word(x), rust_word(y)),
        WExpr::Sub(x, y) => format!("({}).wrapping_sub({})", rust_word(x), rust_word(y)),
        WExpr::Mul(x, y) => format!("({}).wrapping_mul({})", rust_word(x), rust_word(y)),
        WExpr::Band(x, y) => format!("(({}) & ({}))", rust_word(x), rust_word(y)),
        WExpr::Bor(x, y) => format!("(({}) | ({}))", rust_word(x), rust_word(y)),
        WExpr::Bxor(x, y) => format!("(({}) ^ ({}))", rust_word(x), rust_word(y)),
        WExpr::Shl(x, k) => format!("shl_eng({}, {k})", rust_word(x)),
        WExpr::Lshr(x, k) => format!("lshr_eng({}, {k})", rust_word(x)),
        WExpr::Ashr(x, k) => format!("ashr_eng({}, {k})", rust_word(x)),
        WExpr::Mask(x, k) => {
            if *k >= 8 {
                format!("({})", rust_word(x))
            } else {
                format!("(({}) & {}u8)", rust_word(x), (1u16 << k) - 1)
            }
        }
        WExpr::Ite(c, t, f) => {
            format!("(if {} {{ {} }} else {{ {} }})", rust_pred(c), rust_word(t), rust_word(f))
        }
    }
}

/// Interpret a predicate tree as a Rust expression of type `bool`.
pub fn rust_pred(e: &PExpr) -> String {
    match e {
        PExpr::Eq(x, y) => format!("(({}) == ({}))", rust_word(x), rust_word(y)),
        PExpr::Ne(x, y) => format!("(({}) != ({}))", rust_word(x), rust_word(y)),
        PExpr::Ult(x, y) => format!("(({}) < ({}))", rust_word(x), rust_word(y)),
        PExpr::Ule(x, y) => format!("(({}) <= ({}))", rust_word(x), rust_word(y)),
        PExpr::And(x, y) => format!("(({}) && ({}))", rust_pred(x), rust_pred(y)),
        PExpr::Or(x, y) => format!("(({}) || ({}))", rust_pred(x), rust_pred(y)),
        // Boolean xor and iff are `!=` and `==` on `bool`, which Rust has.
        PExpr::Xor(x, y) => format!("(({}) != ({}))", rust_pred(x), rust_pred(y)),
        PExpr::Not(x) => format!("(!({}))", rust_pred(x)),
        PExpr::Iff(x, y) => format!("(({}) == ({}))", rust_pred(x), rust_pred(y)),
    }
}

/// Interpret a word tree as a Verus `spec fn` expression of type `u8`.
///
/// Deliberately a separate function from [`rust_word`] rather than a shared one: the two
/// targets need different spellings, and a shared printer would have to be parameterised in
/// ways that make the translation harder to audit -- which is the one property that matters
/// here. The semantics are identical; the two are cross-checked against each other by
/// agreeing with the same engine.
///
/// Arithmetic goes through the emitted spec helpers `add_eng`/`sub_eng`/`mul_eng`, which
/// wrap. That is not cosmetic: `#[verifier(bit_vector)]` rejects `wrapping_mul` when an
/// operand is a literal ("expected finite-width integer in `bit_vector` proof, got
/// Int(Nat)"), and a constant expression like `255u8 * 255u8` is a rustc const-eval overflow
/// *error* that aborts the whole run, so neither form can be written inline. In a spec fn the
/// operands are already lifted to `int`, so `(x * y) as u8` is the wrapping operation and
/// there is no const-eval to overflow.
pub fn verus_word(e: &WExpr) -> String {
    match e {
        WExpr::Const(k) => format!("{k}u8"),
        WExpr::Param(i) => PARAMS[*i].to_string(),
        WExpr::Add(x, y) => format!("add_eng({}, {})", verus_word(x), verus_word(y)),
        WExpr::Sub(x, y) => format!("sub_eng({}, {})", verus_word(x), verus_word(y)),
        WExpr::Mul(x, y) => format!("mul_eng({}, {})", verus_word(x), verus_word(y)),
        WExpr::Band(x, y) => format!("(({}) & ({}))", verus_word(x), verus_word(y)),
        WExpr::Bor(x, y) => format!("(({}) | ({}))", verus_word(x), verus_word(y)),
        WExpr::Bxor(x, y) => format!("(({}) ^ ({}))", verus_word(x), verus_word(y)),
        WExpr::Shl(x, k) => format!("shl_eng({}, {k})", verus_word(x)),
        WExpr::Lshr(x, k) => format!("lshr_eng({}, {k})", verus_word(x)),
        WExpr::Ashr(x, k) => format!("ashr_eng({}, {k})", verus_word(x)),
        WExpr::Mask(x, k) => {
            if *k >= 8 {
                format!("({})", verus_word(x))
            } else {
                format!("(({}) & {}u8)", verus_word(x), (1u16 << k) - 1)
            }
        }
        WExpr::Ite(c, t, f) => {
            format!("(if {} {{ {} }} else {{ {} }})", verus_pred(c), verus_word(t), verus_word(f))
        }
    }
}

/// Interpret a predicate tree as a Verus `spec` boolean expression.
pub fn verus_pred(e: &PExpr) -> String {
    match e {
        PExpr::Eq(x, y) => format!("(({}) == ({}))", verus_word(x), verus_word(y)),
        PExpr::Ne(x, y) => format!("(({}) != ({}))", verus_word(x), verus_word(y)),
        PExpr::Ult(x, y) => format!("(({}) < ({}))", verus_word(x), verus_word(y)),
        PExpr::Ule(x, y) => format!("(({}) <= ({}))", verus_word(x), verus_word(y)),
        PExpr::And(x, y) => format!("(({}) && ({}))", verus_pred(x), verus_pred(y)),
        PExpr::Or(x, y) => format!("(({}) || ({}))", verus_pred(x), verus_pred(y)),
        // Verus has `!=`/`==` on `bool`, same as Rust.
        PExpr::Xor(x, y) => format!("(({}) != ({}))", verus_pred(x), verus_pred(y)),
        PExpr::Not(x) => format!("(!({}))", verus_pred(x)),
        PExpr::Iff(x, y) => format!("(({}) == ({}))", verus_pred(x), verus_pred(y)),
    }
}

/// Word expressions. One tree, interpreted into the engine ([`to_word`]) and into each
/// backend's source ([`rust_word`] for Kani, [`verus_word`] for Verus).
pub enum WExpr {
    Const(u64),
    Param(usize),
    Add(Box<WExpr>, Box<WExpr>),
    Sub(Box<WExpr>, Box<WExpr>),
    Mul(Box<WExpr>, Box<WExpr>),
    Band(Box<WExpr>, Box<WExpr>),
    Bor(Box<WExpr>, Box<WExpr>),
    Bxor(Box<WExpr>, Box<WExpr>),
    Shl(Box<WExpr>, u32),
    Lshr(Box<WExpr>, u32),
    Ashr(Box<WExpr>, u32),
    /// Narrow to `k` bits then widen back: a mask, through the one width-changing operation.
    /// The pairing is deliberate -- a bare narrowing leaves a width-`k` term every comparison
    /// refuses, so the case would be `Unknown` rather than checked.
    Mask(Box<WExpr>, u8),
    Ite(Box<PExpr>, Box<WExpr>, Box<WExpr>),
}

/// Predicate expressions.
pub enum PExpr {
    Eq(Box<WExpr>, Box<WExpr>),
    Ne(Box<WExpr>, Box<WExpr>),
    Ult(Box<WExpr>, Box<WExpr>),
    Ule(Box<WExpr>, Box<WExpr>),
    And(Box<PExpr>, Box<PExpr>),
    Or(Box<PExpr>, Box<PExpr>),
    Xor(Box<PExpr>, Box<PExpr>),
    Not(Box<PExpr>),
    Iff(Box<PExpr>, Box<PExpr>),
}

/// Interpret a word tree as an engine term.
pub fn to_word(e: &WExpr, vars: &[Var]) -> Var {
    match e {
        WExpr::Const(k) => smt::word(*k, W),
        WExpr::Param(i) => vars[*i],
        WExpr::Add(x, y) => smt::add(to_word(x, vars), to_word(y, vars)),
        WExpr::Sub(x, y) => smt::sub(to_word(x, vars), to_word(y, vars)),
        WExpr::Mul(x, y) => smt::mul(to_word(x, vars), to_word(y, vars)),
        WExpr::Band(x, y) => smt::band(to_word(x, vars), to_word(y, vars)),
        WExpr::Bor(x, y) => smt::bor(to_word(x, vars), to_word(y, vars)),
        WExpr::Bxor(x, y) => smt::bxor(to_word(x, vars), to_word(y, vars)),
        WExpr::Shl(x, k) => smt::shl(to_word(x, vars), *k),
        WExpr::Lshr(x, k) => smt::lshr(to_word(x, vars), *k),
        WExpr::Ashr(x, k) => smt::ashr(to_word(x, vars), *k),
        WExpr::Mask(x, k) => smt::truncate(smt::truncate(to_word(x, vars), *k), W),
        WExpr::Ite(c, t, f) => smt::ite(to_pred(c, vars), to_word(t, vars), to_word(f, vars)),
    }
}

/// Interpret a predicate tree as an engine predicate.
pub fn to_pred(e: &PExpr, vars: &[Var]) -> Pred {
    match e {
        PExpr::Eq(x, y) => smt::eq(to_word(x, vars), to_word(y, vars)),
        PExpr::Ne(x, y) => smt::not(smt::eq(to_word(x, vars), to_word(y, vars))),
        PExpr::Ult(x, y) => smt::ult(to_word(x, vars), to_word(y, vars)),
        PExpr::Ule(x, y) => smt::ule(to_word(x, vars), to_word(y, vars)),
        PExpr::And(x, y) => smt::and(to_pred(x, vars), to_pred(y, vars)),
        PExpr::Or(x, y) => smt::or(to_pred(x, vars), to_pred(y, vars)),
        PExpr::Xor(x, y) => smt::xor(to_pred(x, vars), to_pred(y, vars)),
        PExpr::Not(x) => smt::not(to_pred(x, vars)),
        PExpr::Iff(x, y) => smt::iff(to_pred(x, vars), to_pred(y, vars)),
    }
}

pub fn rand_word(r: &mut Lcg, depth: u32) -> WExpr {
    if depth == 0 || r.below(3) == 0 {
        return if r.below(3) == 0 {
            WExpr::Const(r.below(256))
        } else {
            WExpr::Param(r.below(PARAMS.len() as u64) as usize)
        };
    }
    let tag = r.below(12);
    match tag {
        0 => bin(r, depth, WExpr::Add),
        1 => bin(r, depth, WExpr::Sub),
        2 => bin(r, depth, WExpr::Mul),
        3 => bin(r, depth, WExpr::Band),
        4 => bin(r, depth, WExpr::Bor),
        5 => bin(r, depth, WExpr::Bxor),
        // Shift amounts run to `W + 1` so the "shift everything out" edge is reachable,
        // which is where a `bit - sh` underflow would live.
        6 => {
            let a = rand_word(r, depth - 1);
            let k = r.below(W as u64 + 2) as u32;
            WExpr::Shl(Box::new(a), k)
        }
        7 => {
            let a = rand_word(r, depth - 1);
            let k = r.below(W as u64 + 2) as u32;
            WExpr::Lshr(Box::new(a), k)
        }
        8 => {
            let a = rand_word(r, depth - 1);
            let k = r.below(W as u64 + 2) as u32;
            WExpr::Ashr(Box::new(a), k)
        }
        9 => {
            let a = rand_word(r, depth - 1);
            let k = 1 + r.below(W as u64) as u8;
            WExpr::Mask(Box::new(a), k)
        }
        10 => {
            let c = rand_pred(r, depth - 1);
            let a = rand_word(r, depth - 1);
            let b = rand_word(r, depth - 1);
            WExpr::Ite(Box::new(c), Box::new(a), Box::new(b))
        }
        _ => bin(r, depth, WExpr::Add),
    }
}

fn bin(r: &mut Lcg, depth: u32, f: fn(Box<WExpr>, Box<WExpr>) -> WExpr) -> WExpr {
    let a = rand_word(r, depth - 1);
    let b = rand_word(r, depth - 1);
    f(Box::new(a), Box::new(b))
}

pub fn rand_pred(r: &mut Lcg, depth: u32) -> PExpr {
    if depth == 0 || r.below(4) == 0 {
        let tag = r.below(4);
        let a = rand_word(r, 0);
        let b = rand_word(r, 0);
        return match tag {
            0 => PExpr::Eq(Box::new(a), Box::new(b)),
            1 => PExpr::Ne(Box::new(a), Box::new(b)),
            2 => PExpr::Ult(Box::new(a), Box::new(b)),
            _ => PExpr::Ule(Box::new(a), Box::new(b)),
        };
    }
    let tag = r.below(6);
    match tag {
        0 => pbin(r, depth, PExpr::And),
        1 => pbin(r, depth, PExpr::Or),
        2 => pbin(r, depth, PExpr::Xor),
        3 => {
            let a = rand_pred(r, depth - 1);
            PExpr::Not(Box::new(a))
        }
        4 => pbin(r, depth, PExpr::Iff),
        _ => {
            let a = rand_word(r, depth - 1);
            let b = rand_word(r, depth - 1);
            PExpr::Eq(Box::new(a), Box::new(b))
        }
    }
}

fn pbin(r: &mut Lcg, depth: u32, f: fn(Box<PExpr>, Box<PExpr>) -> PExpr) -> PExpr {
    let a = rand_pred(r, depth - 1);
    let b = rand_pred(r, depth - 1);
    f(Box::new(a), Box::new(b))
}

/// A generated case: its name, the engine's verdict, and the IR both backends compile.
pub struct Case {
    pub name: String,
    pub ir: PExpr,
    pub ours: smt::Verdict,
}

/// Run one predicate through the engine in its own fresh arena.
///
/// One arena per case, not one shared arena: sharing it exhausted the node budget after
/// about a dozen queries and every later query came back `Unknown`, which the harness then
/// reported as the engine being weak when the *harness* had run the arena dry. That is the
/// "summary outrunning its evidence" shape this crate keeps finding, and it was found by
/// the harness failing, not by reading.
pub fn engine_verdict(ir: &PExpr) -> smt::Verdict {
    smt::with_fresh(|| {
        let vars: Vec<Var> = PARAMS.iter().map(|_| smt::var(W)).collect();
        smt::prove(to_pred(ir, &vars))
    })
}

/// Identities that are true by construction, one or more per operator.
///
/// The random sweep is mostly refutable formulas and it compares only proved/refuted, so a
/// wrong-but-plausible blasting arm can survive it: if the engine blasted `sub` as `add`, a
/// random `a - b == a + b` is still refuted, so both sides agree. This corpus is the other
/// half -- true identities each backend must *prove* -- so a wrong arm turns a proved
/// identity into a refuted one and the disagreement is visible.
pub fn identity_corpus() -> Vec<(&'static str, PExpr)> {
    use PExpr::*;
    use WExpr::*;
    let p = |i: usize| Box::new(Param(i));
    let c = |k: u64| Box::new(Const(k));
    let w = |e: WExpr| Box::new(e);
    let pp = |e: PExpr| Box::new(e);
    vec![
        ("add_comm", Eq(w(Add(p(0), p(1))), w(Add(p(1), p(0))))),
        ("add_assoc",
         Eq(w(Add(w(Add(p(0), p(1))), p(2))), w(Add(p(0), w(Add(p(1), p(2))))))),
        ("sub_self", Eq(w(Sub(p(0), p(0))), c(0))),
        ("add_sub_cancel", Eq(w(Sub(w(Add(p(0), p(1))), p(1))), p(0))),
        ("sub_zero", Eq(w(Sub(p(0), c(0))), p(0))),
        ("mul_comm", Eq(w(Mul(p(0), p(1))), w(Mul(p(1), p(0))))),
        ("mul_zero", Eq(w(Mul(p(0), c(0))), c(0))),
        ("mul_one", Eq(w(Mul(p(0), c(1))), p(0))),
        ("band_comm", Eq(w(Band(p(0), p(1))), w(Band(p(1), p(0))))),
        ("band_self", Eq(w(Band(p(0), p(0))), p(0))),
        ("bor_self", Eq(w(Bor(p(0), p(0))), p(0))),
        ("bxor_self", Eq(w(Bxor(p(0), p(0))), c(0))),
        ("band_all_ones", Eq(w(Band(p(0), c(0xff))), p(0))),
        ("bor_zero", Eq(w(Bor(p(0), c(0))), p(0))),
        // De Morgan as an equivalence. A bare `Not(And(..))` is *not* a tautology (it fails
        // at `a=0,b=1,c=2`), which the first corpus got wrong; the engine correctly refuted
        // it and the harness blamed the engine. The law needs both sides.
        ("demorgan",
         Iff(
            pp(Not(pp(And(pp(Ult(p(0), p(1))), pp(Ult(p(1), p(2))))))),
            pp(Or(pp(Not(pp(Ult(p(0), p(1))))), pp(Not(pp(Ult(p(1), p(2))))))),
         )),
        ("shl_zero", Eq(w(Shl(p(0), 0)), p(0))),
        ("lshr_zero", Eq(w(Lshr(p(0), 0)), p(0))),
        ("ashr_zero", Eq(w(Ashr(p(0), 0)), p(0))),
        ("shl_eight", Eq(w(Shl(p(0), 8)), c(0))),
        ("lshr_eight", Eq(w(Lshr(p(0), 8)), c(0))),
        ("lshr_seven_80", Eq(w(Lshr(c(0x80), 7)), c(0x01))),
        ("ashr_sign_80", Eq(w(Ashr(c(0x80), 7)), c(0xff))),
        ("ashr_top_0x40", Eq(w(Ashr(c(0x40), 7)), c(0x00))),
        ("shl_one_80", Eq(w(Shl(c(0x80), 1)), c(0x00))),
        ("ult_irrefl", Not(pp(Ult(p(0), p(0))))),
        ("ule_refl", Ule(p(0), p(0))),
        ("ult_antisym", Not(pp(And(pp(Ult(p(0), p(1))), pp(Ult(p(1), p(0))))))),
        ("ult_total_ish", Or(pp(Ult(p(0), p(1))), pp(Ule(p(1), p(0))))),
        ("mask_4_upper_clear", Eq(w(Mask(p(0), 4)), w(Band(p(0), c(0x0f))))),
        ("mask_8_identity", Eq(w(Mask(p(0), 8)), p(0))),
        // `ite` selects the branch the guard picks -- as an *implication*, not an
        // equivalence. `guard <=> ite(guard,a,b)==a` is false at `a==b`, the second corpus
        // mistake the engine correctly refuted.
        ("ite_guard",
         Or(
            pp(Not(pp(Ult(p(0), p(1))))),
            pp(Eq(w(Ite(pp(Ult(p(0), p(1))), p(0), p(1))), p(0))),
         )),
        ("add_band_distrib_lo",
         Eq(w(Band(w(Add(p(0), p(1))), c(1))), w(Band(w(Bxor(p(0), p(1))), c(1))))),
    ]
}

/// A deliberately false identity, to prove a harness can report a disagreement.
///
/// If every case agreed, "agreement" would be indistinguishable from a harness that never
/// asks a real question. `a - b == b - a` is false at `a != b`, so both sides must refute
/// it; each harness fails its run if either side *proves* it.
pub fn negative_control() -> PExpr {
    use PExpr::*;
    use WExpr::*;
    Eq(
        Box::new(Sub(Box::new(Param(0)), Box::new(Param(1)))),
        Box::new(Sub(Box::new(Param(1)), Box::new(Param(0)))),
    )
}

/// Build the full case list: corpus, negative control, then `n` random predicates.
pub fn build_cases(n: u32) -> Vec<Case> {
    let mut cases = Vec::new();
    for (name, ir) in identity_corpus() {
        let ours = engine_verdict(&ir);
        cases.push(Case { name: name.to_string(), ir, ours });
    }
    let control = negative_control();
    let ours = engine_verdict(&control);
    cases.push(Case { name: "NEGATIVE_CONTROL_sub_comm".to_string(), ir: control, ours });

    let mut r = Lcg(0x5eed_1234_9abc_def0);
    for i in 0..n {
        let ir = rand_pred(&mut r, 3);
        let ours = engine_verdict(&ir);
        cases.push(Case { name: format!("rand_{i}"), ir, ours });
    }
    cases
}

/// The identity-corpus check every harness shares: a true identity the engine *refutes* is
/// a soundness failure; one it leaves `Unknown` is the engine being conservative, which is
/// allowed and only reported. Collapsing the two is what let a mutated engine pass.
pub struct IdentityTally {
    pub refuted: usize,
    pub undecided: usize,
}

pub fn tally_identities(cases: &[Case], label: &str) -> IdentityTally {
    let mut t = IdentityTally { refuted: 0, undecided: 0 };
    for case in cases {
        let is_identity = !case.name.starts_with("rand_") && !case.name.starts_with("NEGATIVE");
        if !is_identity {
            continue;
        }
        match case.ours {
            smt::Verdict::Valid => {}
            smt::Verdict::Unknown => {
                t.undecided += 1;
                eprintln!(
                    "[{label}] IDENTITY UNDECIDED {} (engine conservative; not a soundness bug)",
                    case.name
                );
            }
            _ => {
                t.refuted += 1;
                eprintln!(
                    "[{label}] IDENTITY REFUTED {} ours={:?} -- a true identity the engine rejected",
                    case.name, case.ours
                );
            }
        }
    }
    t
}

/// The three-way outcome of one backend's verdict on one case, compared with the engine's.
///
/// The soundness matrix matters: only the engine's `Unknown` is "no claim". Every other
/// engine verdict is a definite claim the backend must not contradict, and the first version
/// of this comparison lumped all "engine did not prove it" together -- so a real blast bug
/// produced `mismatch=0` and was caught only by the curated corpus. See `tally_backend`.
pub struct BackendTally {
    pub agree: usize,
    pub mismatch: usize,
    pub missing: usize,
}

/// Compare one backend's per-case verdicts against the engine's, filling a [`BackendTally`].
///
/// `proved` is the backend's verdict: `Some(true)` it proved the case, `Some(false)` it
/// refuted it, `None` it produced no verdict (which is a failure, not a pass).
pub fn tally_backend(
    cases: &[Case],
    proved: impl Fn(&Case) -> Option<bool>,
    label: &str,
) -> BackendTally {
    let mut t = BackendTally { agree: 0, mismatch: 0, missing: 0 };
    for case in cases {
        match proved(case) {
            Some(true) => match case.ours {
                smt::Verdict::Valid => t.agree += 1,
                smt::Verdict::Unknown => {
                    // The engine made no claim; the backend proving it is the engine being
                    // conservative, which is allowed.
                    t.agree += 1;
                    if !case.name.starts_with("rand_") {
                        eprintln!(
                            "[{label}] NOTE {}: engine=Unknown backend=PROVED (engine incomplete)",
                            case.name
                        );
                    }
                }
                _ => {
                    // Engine said "refuted", backend says "always true": a definite
                    // disagreement, the soundness bug the random sweep exists to find.
                    t.mismatch += 1;
                    eprintln!(
                        "[{label}] MISMATCH {}: engine={:?} backend=PROVED (engine refuted a truth)",
                        case.name, case.ours
                    );
                }
            },
            Some(false) => {
                if case.ours.is_proved() {
                    t.mismatch += 1;
                    eprintln!(
                        "[{label}] MISMATCH {}: engine=Valid backend=REFUTED",
                        case.name
                    );
                } else {
                    t.agree += 1;
                }
            }
            None => {
                t.missing += 1;
                eprintln!("[{label}] MISSING {}: backend produced no verdict", case.name);
            }
        }
    }
    t
}

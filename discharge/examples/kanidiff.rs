// Differential oracle: the engine checked against an independent verifier.
//
// `z3diff` checks the *exporter* -- it prints a query and asks z3 to agree about that
// text. This harness checks the *engine*: it takes predicates the engine proved, compiles
// each one into a real Rust function, and asks Kani (AWS's model checker, over CBMC) to
// verify the same property of the compiled code. Kani never sees a symbolic term or an
// SMT-LIB string; it reasons about MIR. So agreement here is agreement between two
// independently built decision procedures, which is a strictly stronger claim than
// agreeing with a printer.
//
// Kani is an *oracle*, not a dependency: it is invoked as `cargo kani` in a subprocess,
// and the crate still builds with zero dependencies. If Kani is absent the harness says
// so and exits non-zero -- an oracle that did not run is not evidence, which is the same
// rule `z3diff` and `scripts/gate.sh` follow.
//
// What this can and cannot see. The engine's verdicts here are about `u8` values, and
// Kani's are about the same `u8` values, so a *semantic* blasting bug (a wrong arm in
// `blast`, a dropped bit, an off-by-one in a shift) shows up as a disagreement. What it
// cannot see is a bug in the parts of the engine that never reach the compiled function:
// the arena, staleness, the width checks. Those have their own tests. Stating the boundary
// is the point; a harness that claims to check "everything" checks nothing in particular.
//
// One property of the design matters more than the rest. The predicate and the Rust text
// are *not* generated independently -- they are two interpretations of one shared IR tree
// (see [`WExpr`] and [`PExpr`]). Generating them separately would compare unrelated
// formulas and every disagreement would be noise. The IR exists so that "the same
// property" is structural, not hoped for.

use discharge::smt::{self, Pred, Var, Verdict};
use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

struct Lcg(u64);
impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0 >> 33
    }
    fn below(&mut self, n: u64) -> u64 {
        if n == 0 { 0 } else { self.next() % n }
    }
}

/// Width of every word in the IR. Everything is `u8` so that both sides stay well-sorted:
/// the engine refuses mixed-width comparisons, and a case it refuses makes no claim for
/// Kani to confirm. Fixing the width is what keeps every generated case *checkable*.
const W: u8 = 8;
/// Parameters every case is built over. Three reaches every binary operator and `ite`.
const PARAMS: [&str; 3] = ["a", "b", "c"];

/// Word expressions. One tree, interpreted twice: [`to_word`] into the engine, [`rust_word`]
/// into Rust source.
enum WExpr {
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
    /// Narrow to `k` bits then widen back to 8: a mask, expressed through the one
    /// width-changing operation. The pairing is deliberate -- a bare narrowing would leave
    /// a width-`k` term that every comparison refuses, so the case would be `Unknown`
    /// rather than checked, and the narrowing branch would never be exercised.
    Mask(Box<WExpr>, u8),
    Ite(Box<PExpr>, Box<WExpr>, Box<WExpr>),
}

/// Predicate expressions.
enum PExpr {
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
fn to_word(e: &WExpr, vars: &[Var]) -> Var {
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
fn to_pred(e: &PExpr, vars: &[Var]) -> Pred {
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

/// Interpret a word tree as a Rust expression of type `u8`.
///
/// The translation is the whole content of the harness, so it is written to be auditable
/// by eye: `Add` is `wrapping_add` because the engine's `Add` wraps, and `Mask` is `&
/// ((1<<k)-1)` because the engine's narrowing `truncate` keeps the low bits. A mistake
/// *here* shows up as a mismatch, which is the right outcome -- the harness reports its
/// own bug rather than silently vouching for the engine.
///
/// Shifts go through the emitted helpers `shl_eng`/`lshr_eng`/`ashr_eng`, and the reason
/// is worth stating because it is a *real* divergence that the first version of this
/// harness tripped over. The engine defines a shift by `k >= width` to be 0 (or the sign
/// bit, for an arithmetic shift) -- the SMT-LIB `bvshl`/`bvlshr`/`bvashr` rule, and a
/// behaviour its own tests pin. Rust does not: `x << 8` on a `u8` is an arithmetic-overflow
/// *error* at compile time, and at run time it panics. So the two are not the same function
/// at `k == 8`, and emitting `x << k` would either fail to compile or, worse, check a
/// different operation. The helpers spell the engine's rule out in Rust so the comparison
/// is about the blast, not about Rust's shift definedness. For `k < 8` they are exactly
/// `<<`/`>>`/arithmetic `>>`.
fn rust_word(e: &WExpr) -> String {
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
fn rust_pred(e: &PExpr) -> String {
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

fn rand_word(r: &mut Lcg, depth: u32) -> WExpr {
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

/// Build a binary word node, recursing for the two operands in a fixed order.
fn bin(r: &mut Lcg, depth: u32, f: fn(Box<WExpr>, Box<WExpr>) -> WExpr) -> WExpr {
    let a = rand_word(r, depth - 1);
    let b = rand_word(r, depth - 1);
    f(Box::new(a), Box::new(b))
}

fn rand_pred(r: &mut Lcg, depth: u32) -> PExpr {
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

/// Build a binary predicate node, recursing for the two operands in a fixed order.
fn pbin(r: &mut Lcg, depth: u32, f: fn(Box<PExpr>, Box<PExpr>) -> PExpr) -> PExpr {
    let a = rand_pred(r, depth - 1);
    let b = rand_pred(r, depth - 1);
    f(Box::new(a), Box::new(b))
}

/// A generated case: its name, the engine's verdict, and the Rust text Kani will check.
struct Case {
    name: String,
    rust: String,
    ours: Verdict,
}

/// Identities that are true by construction, one or more per operator.
///
/// The random sweep is mostly refutable formulas, and it compares only proved/refuted.
/// That means a wrong-but-plausible blasting arm can survive it: if the engine blasted
/// `sub` as `add`, a random `a - b == a + b` is still refuted, so both sides agree. This
/// corpus is the other half -- true identities whose Rust counterpart Kani must *prove* --
/// so a wrong arm turns a proved identity into a refuted one and the disagreement is
/// visible. Each entry is `(name, ir)`; both sides are derived from the IR.
fn identity_corpus() -> Vec<(&'static str, PExpr)> {
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
        // De Morgan, as an equivalence. A bare `Not(And(...))` is *not* a tautology (it
        // fails at `a=0,b=1,c=2`), which the first version of this corpus got wrong: the
        // engine returned a counterexample and the harness called it "not proved". The
        // law needs both sides.
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
        // equivalence. `guard <=> ite(guard,a,b)==a` is false at `a==b` (guard false, yet
        // the else-branch equals `a`), which is the second mistake the first corpus made.
        ("ite_guard",
         Or(
            pp(Not(pp(Ult(p(0), p(1))))),
            pp(Eq(w(Ite(pp(Ult(p(0), p(1))), p(0), p(1))), p(0))),
         )),
        ("add_band_distrib_lo",
         Eq(w(Band(w(Add(p(0), p(1))), c(1))), w(Band(w(Bxor(p(0), p(1))), c(1))))),
    ]
}

/// A deliberately false identity, to prove the harness can report a disagreement.
///
/// If every case agreed, "agreement" would be indistinguishable from a harness that never
/// asks a real question. `a - b == b - a` is false at `a != b`, so both the engine and Kani
/// must refute it; `main` asserts exactly that.
fn negative_control() -> PExpr {
    use PExpr::*;
    use WExpr::*;
    Eq(
        Box::new(Sub(Box::new(Param(0)), Box::new(Param(1)))),
        Box::new(Sub(Box::new(Param(1)), Box::new(Param(0)))),
    )
}

/// Write a crate whose `#[kani::proof]` harnesses assert each case's Rust text.
fn write_crate(dir: &Path, cases: &[Case]) -> std::io::Result<()> {
    fs::create_dir_all(dir.join("src"))?;
    // `[workspace]` detaches the generated crate from any enclosing workspace, so
    // `cargo kani` runs on this crate and not on the one we are being run from.
    fs::write(
        dir.join("Cargo.toml"),
        "[package]\nname = \"kani_oracle_cases\"\nversion = \"0.0.0\"\nedition = \"2021\"\n\n\
         [workspace]\n",
    )?;
    let mut lib = String::from(
        "// Generated by examples/kanidiff.rs. Each harness is one predicate the engine\n\
         // proved; Kani must prove the same property of the compiled code.\n\
         #![allow(unused_variables, unused_parens)]\n\n\
         // The engine's shift rule: a shift by `k >= 8` is 0 (or the sign bit, for an\n\
         // arithmetic shift). Rust's `<<`/`>>` are not defined there, so spelling the\n\
         // engine's rule out is the only way to compare the same function.\n\
         fn shl_eng(x: u8, k: u32) -> u8 { if k >= 8 { 0 } else { x << k } }\n\
         fn lshr_eng(x: u8, k: u32) -> u8 { if k >= 8 { 0 } else { x >> k } }\n\
         fn ashr_eng(x: u8, k: u32) -> u8 { if k >= 8 { if x >= 0x80 { 0xff } else { 0 } } else { ((x as i8) >> k) as u8 } }\n\n",
    );
    for (i, case) in cases.iter().enumerate() {
        lib.push_str(&format!(
            "#[kani::proof]\nfn case_{i}() {{\n    let a: u8 = kani::any();\n    let b: u8 = kani::any();\n    let c: u8 = kani::any();\n    assert!({});\n}}\n\n",
            case.rust
        ));
    }
    fs::write(dir.join("src").join("lib.rs"), lib)?;
    Ok(())
}

/// Whether `cargo kani` is usable at all.
fn kani_available() -> bool {
    Command::new("cargo")
        .args(["kani", "--version"])
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
}

/// The per-harness verdicts Kani printed, keyed by `case_N`.
///
/// Parsed from `--output-format terse`, whose shape is `Checking harness case_7...`
/// followed by `VERIFICATION:- SUCCESSFUL|FAILED`. A harness with no verdict is *not*
/// treated as success: an absent verdict is a harness that did not run, and `main` fails
/// the sweep if any is missing.
fn run_kani(dir: &Path) -> std::io::Result<BTreeMap<String, bool>> {
    let out = Command::new("cargo")
        .args(["kani", "--output-format", "terse"])
        .current_dir(dir)
        .output()?;
    // Kani writes to stdout, but the pairing is run over both streams joined in a fixed
    // order so a stray diagnostic on stderr cannot desynchronise it.
    let mut text = String::from_utf8_lossy(&out.stdout).into_owned();
    text.push('\n');
    text.push_str(&String::from_utf8_lossy(&out.stderr));
    let mut verdicts = BTreeMap::new();
    let mut current: Option<String> = None;
    for line in text.lines() {
        let t = line.trim();
        if let Some(rest) = t.strip_prefix("Checking harness ") {
            current = Some(rest.trim_end_matches("...").trim().to_string());
        } else if let Some(rest) = t.strip_prefix("VERIFICATION:-") {
            if let Some(name) = current.take() {
                let r = rest.trim();
                if r.contains("SUCCESSFUL") {
                    verdicts.insert(name, true);
                } else if r.contains("FAILED") {
                    verdicts.insert(name, false);
                }
            }
        }
    }
    Ok(verdicts)
}

fn main() {
    if !kani_available() {
        eprintln!(
            "kanidiff: `cargo kani` is not available, so the oracle cannot run.\n\
             Install it (`cargo install --locked kani-verifier && cargo kani setup`) and re-run.\n\
             An oracle that did not run is not evidence about the engine."
        );
        std::process::exit(2);
    }

    let cases_n: u32 = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(24);

    // Every engine query gets its *own* fresh arena. Sharing one arena across all cases
    // was the first version's bug: after roughly a dozen queries the node budget was spent
    // and every later query came back `Unknown`, which the harness then reported as
    // `not_proved=27`. That was not the engine being weak, it was the harness exhausting a
    // fixed arena and blaming the engine -- the exact "summary outrunning its evidence"
    // shape this crate keeps finding. `with_fresh` resets the arena, so one call per case.
    let mut cases: Vec<Case> = Vec::new();
    for (name, ir) in identity_corpus() {
        let (ours, rust) = smt::with_fresh(|| {
            let vars: Vec<Var> = PARAMS.iter().map(|_| smt::var(W)).collect();
            (smt::prove(to_pred(&ir, &vars)), rust_pred(&ir))
        });
        cases.push(Case { name: name.to_string(), rust, ours });
    }
    let control = negative_control();
    let (control_ours, control_rust) = smt::with_fresh(|| {
        let vars: Vec<Var> = PARAMS.iter().map(|_| smt::var(W)).collect();
        (smt::prove(to_pred(&control, &vars)), rust_pred(&control))
    });
    cases.push(Case {
        name: "NEGATIVE_CONTROL_sub_comm".to_string(),
        rust: control_rust,
        ours: control_ours,
    });

    let mut r = Lcg(0x5eed_1234_9abc_def0);
    let rand_irs: Vec<PExpr> = (0..cases_n).map(|_| rand_pred(&mut r, 3)).collect();
    for (i, ir) in rand_irs.into_iter().enumerate() {
        let (ours, rust) = smt::with_fresh(|| {
            let vars: Vec<Var> = PARAMS.iter().map(|_| smt::var(W)).collect();
            (smt::prove(to_pred(&ir, &vars)), rust_pred(&ir))
        });
        cases.push(Case { name: format!("rand_{i}"), rust, ours });
    }

    // The identity corpus is true by construction, so the engine's verdict on it is a
    // check in its own right -- but the two ways of not proving it mean different things
    // and must not be collapsed (the same lesson `z3diff` learned about parse errors vs an
    // absent oracle).
    //
    //   * `Unknown` is the engine being *conservative*: it declined to decide. That is
    //     allowed -- a proof procedure may give up -- and is not a soundness failure. It is
    //     counted and printed, not failed on. `mul_comm` lands here: an 8x8 BDD multiplier
    //     is exactly the size wall the README documents, and Kani proves the same identity,
    //     so the engine is incomplete, not wrong.
    //   * `Counterexample`/`Unsat` is the engine *refuting* a tautology. That is a
    //     soundness failure and fails the run. (The first version of this corpus reported
    //     two of these and they were the corpus's fault, not the engine's -- see the
    //     `demorgan` and `ite_guard` comments -- which is why a refutation is worth looking
    //     at rather than assuming.)
    let mut refuted_identity = 0usize;
    let mut undecided_identity = 0usize;
    for case in &cases {
        let is_identity = !case.name.starts_with("rand_") && !case.name.starts_with("NEGATIVE");
        if !is_identity {
            continue;
        }
        match case.ours {
            Verdict::Valid => {}
            Verdict::Unknown => {
                undecided_identity += 1;
                eprintln!("IDENTITY UNDECIDED {} (engine conservative; not a soundness bug)", case.name);
            }
            _ => {
                refuted_identity += 1;
                eprintln!(
                    "IDENTITY REFUTED {} ours={:?} -- a true identity the engine rejected",
                    case.name, case.ours
                );
            }
        }
    }
    let proved_by_engine = cases.iter().filter(|c| c.ours.is_proved()).count();

    let dir: PathBuf = std::env::temp_dir().join("discharge_kanidiff");
    let _ = fs::remove_dir_all(&dir);
    if let Err(e) = write_crate(&dir, &cases) {
        eprintln!("kanidiff: could not write the case crate at {}: {e}", dir.display());
        std::process::exit(1);
    }
    let verdicts = match run_kani(&dir) {
        Ok(v) => v,
        Err(e) => {
            eprintln!("kanidiff: running `cargo kani` failed: {e}");
            std::process::exit(1);
        }
    };

    let mut agree = 0usize;
    let mut mismatch = 0usize;
    let mut missing = 0usize;
    for (i, case) in cases.iter().enumerate() {
        // The soundness matrix. Only `Unknown` is "no claim"; every other engine verdict is
        // a definite claim that Kani must not contradict. The first version of this harness
        // lumped all "engine did not prove it" together and counted engine-refuted + Kani-
        // proved as agreement -- which meant a real blast bug (a `Sub` that dropped its
        // `+1`) produced `mismatch=0` on the random sweep and was caught only by the
        // curated corpus. The mutation test is what exposed it: a harness that reports
        // "no disagreement" on a broken engine is worse than no harness, because it gets
        // quoted.
        match verdicts.get(&format!("case_{i}")) {
            Some(true) => match case.ours {
                Verdict::Valid => agree += 1,
                Verdict::Unknown => {
                    // The engine made no claim; Kani proving it is the engine being
                    // conservative, which is allowed.
                    agree += 1;
                    if !case.name.starts_with("rand_") {
                        eprintln!(
                            "NOTE {}: engine=Unknown kani=SUCCESSFUL (engine incomplete) rust={}",
                            case.name, case.rust
                        );
                    }
                }
                _ => {
                    // Engine said "refuted", Kani says "always true": a definite
                    // disagreement. This is the soundness bug the random sweep is for.
                    mismatch += 1;
                    eprintln!(
                        "MISMATCH {}: engine={:?} kani=SUCCESSFUL (engine refuted a truth) rust={}",
                        case.name, case.ours, case.rust
                    );
                }
            },
            Some(false) => {
                if case.ours.is_proved() {
                    mismatch += 1;
                    eprintln!(
                        "MISMATCH {}: engine=Valid but kani=FAILED rust={}",
                        case.name, case.rust
                    );
                } else {
                    agree += 1;
                }
            }
            None => {
                missing += 1;
                eprintln!("MISSING {}: kani produced no verdict for case_{i}", case.name);
            }
        }
    }

    // The control: the engine must have refuted it and Kani must have failed it. If either
    // "proved" it, the harness is not asking a real question and the agreement above would
    // be worthless.
    let control_index = cases.iter().position(|c| c.name.starts_with("NEGATIVE_CONTROL"));
    let control_ok = match control_index {
        Some(i) => {
            let kani_proved = verdicts.get(&format!("case_{i}")).copied().unwrap_or(true);
            !cases[i].ours.is_proved() && !kani_proved
        }
        None => false,
    };
    println!(
        "cases={} proved_by_engine={} agree={} mismatch={} missing={} refuted_identity={} undecided_identity={} control_ok={}",
        cases.len(),
        proved_by_engine,
        agree,
        mismatch,
        missing,
        refuted_identity,
        undecided_identity,
        control_ok
    );

    // A mismatch is a soundness disagreement and fails the run. A refuted identity means
    // the engine rejected something true, which is the same thing. A missing verdict means
    // a harness did not run, so the comparison it was supposed to make did not happen. An
    // *undecided* identity is the engine being conservative and does not fail the run; it
    // is printed so the incompleteness stays visible.
    if mismatch > 0 || missing > 0 || refuted_identity > 0 || !control_ok {
        eprintln!(
            "kanidiff FAILED: mismatch={mismatch} missing={missing} \
             refuted_identity={refuted_identity} control_ok={control_ok}"
        );
        std::process::exit(1);
    }
}

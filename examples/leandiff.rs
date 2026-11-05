// Differential oracle: the engine checked against Lean 4's `bv_decide`.
//
// `kanidiff` checks the engine against a bounded model checker, `verusdiff` against an SMT
// backend, and `z3diff` against a printer. This harness checks it against a *proof kernel*.
// `bv_decide` decides a bitvector goal by bit-blasting it to CNF, running a SAT solver, and
// then replaying the solver's refutation as a Lean proof term which the kernel type-checks.
// The verdict that comes back is therefore not "a solver said so" -- it is a machine-checked
// theorem about the same 8-bit words this crate blasts. That is the strongest form of
// independent agreement available here, and it is why Lean was added alongside Kani and
// Verus rather than instead of them.
//
// Lean is an *oracle*, not a dependency: it is invoked as `lean` in a subprocess and the
// crate still builds with zero dependencies. If Lean is absent the harness says so and exits
// 2 -- an oracle that did not run is not evidence, the rule `z3diff`, `kanidiff` and
// `verusdiff` all follow. `LEAN_BIN` names the binary when it is not on `PATH` (elan puts it
// in `~/.elan/bin`, which is not always exported).
//
// The cases come from `examples/support/mod.rs`, shared with the other harnesses, so
// "the engine agrees with Lean" and "the engine agrees with Kani" are claims about the
// *same* formulas rather than two harness-specific corpora. See that module for why.

mod support;

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use support::{Case, build_cases, lean_pred, tally_backend, tally_identities};

/// The header every generated file needs. The linter is off because a case need not mention
/// all three parameters (`shl_eight` mentions only `a`), and an unused binder is a warning
/// here, not a finding.
const PRELUDE: &str = "import Std.Tactic.BVDecide\n\
                       set_option linter.unusedVariables false\n\n";

/// The tactic each theorem is closed with.
///
/// `bv_decide` alone is not enough, and the gap is not hypothetical: it bit-blasts *free*
/// variables, so a goal with no variables left -- `(101 == 152) = true`, or `c < c`, where
/// the random generator produced a reflexivity -- is outside the fragment it supports and
/// reports "None of the hypotheses are in the supported BitVec fragment". Those goals are
/// still perfectly decidable, just not by bit-blasting, so a second tactic is needed.
///
/// `native_decide` rather than `decide`, for a measured reason. `first | bv_decide | decide`
/// is the obvious spelling and it does not work: `first` commits to the *first* tactic that
/// produces a proof *or an error*, and `bv_decide` reporting a counterexample counts as an
/// error, so `decide` then runs on every refuted goal -- including the wide arithmetic ones,
/// where it hits the heartbeat limit and the case is reported as unverifiable rather than
/// refuted. `native_decide` compiles the decision to native code instead of reducing in the
/// kernel, so it finishes those in well under a second.
///
/// The trade is stated plainly because it is real: `native_decide` is Lean's trusted-native
/// escape hatch, so the fallback verdicts are trusted rather than kernel-checked. `bv_decide`
/// is tried first precisely so that this applies to as few cases as possible -- in the
/// default 64-case sweep it is the out-of-fragment handful, not the arithmetic. Neither
/// tactic can be *wrong*: both reject a false goal, which the negative control confirms.
const TACTIC: &str = "first | bv_decide | native_decide";

/// Write the case file and return the line number each theorem landed on.
///
/// The line numbers are the whole coupling to the output: Lean reports an error as
/// `file.lean:LINE:COL: error: ...`, so the line is how a verdict is attributed back to a
/// case. They are computed by construction rather than searched for, so a case named
/// `case_1` can never be confused with `case_10` the way a substring match would.
fn write_file(dir: &Path, cases: &[Case]) -> std::io::Result<(PathBuf, BTreeMap<usize, String>)> {
    fs::create_dir_all(dir)?;
    let mut text = String::from(PRELUDE);
    let mut by_line = BTreeMap::new();
    for (i, case) in cases.iter().enumerate() {
        // `∀` rather than a named binder list: every case is a closed universal statement
        // over the same three words, which is exactly what `prove()` claims about a term
        // built from `PARAMS`.
        let line_no = text.lines().count() + 1;
        by_line.insert(line_no, case.name.clone());
        text.push_str(&format!(
            "theorem case_{i} : ∀ (a b c : BitVec 8), ({}) = true := by {TACTIC}\n",
            lean_pred(&case.ir)
        ));
    }
    let path = dir.join("cases.lean");
    fs::write(&path, text)?;
    Ok((path, by_line))
}

/// The Lean binary to use: `LEAN_BIN` if set, else `lean` from `PATH`.
fn lean_bin() -> String {
    std::env::var("LEAN_BIN").unwrap_or_else(|_| "lean".to_string())
}

fn lean_available(bin: &str) -> bool {
    Command::new(bin)
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
}

/// A verdict for one case, or the reason there is none.
enum Verdict {
    Proved,
    Refuted,
    /// Lean reported something that is not a counterexample -- a parse error, an unknown
    /// tactic, a `bv_decide` failure. That is the harness or the backend failing, not a
    /// claim about the engine, and it must not be read as "proved".
    Hard(String),
}

/// Run Lean and attribute each verdict to the case on its line.
///
/// The default is `Proved`, because a theorem Lean accepts produces no output at all. That
/// default is only safe because any *other* diagnostic on a case line becomes `Hard`, and
/// `main` refuses to report agreement if any case is `Hard` -- so a file Lean rejected
/// wholesale can never be mistaken for a file it verified.
fn run_lean(
    path: &Path,
    by_line: &BTreeMap<usize, String>,
) -> std::io::Result<BTreeMap<String, Verdict>> {
    let out = Command::new(lean_bin()).arg(path).output()?;
    let mut text = String::from_utf8_lossy(&out.stdout).into_owned();
    text.push('\n');
    text.push_str(&String::from_utf8_lossy(&out.stderr));

    let mut verdicts: BTreeMap<String, Verdict> =
        by_line.values().map(|n| (n.clone(), Verdict::Proved)).collect();

    // Lean diagnostics are multi-line: `file:line:col: error: <first line>` then indented
    // continuation lines. The *classification* depends on a continuation -- `decide`
    // reports "Tactic `decide` proved that the proposition" on the first line and "is
    // false" two lines later -- so the whole block has to be collected before it can be
    // judged. Reading only the first line is what made an earlier revision call every
    // `decide` refutation "hard", i.e. unverifiable, when it had in fact decided the case.
    let mut current: Option<(usize, String)> = None;
    let finish = |cur: Option<(usize, String)>, verdicts: &mut BTreeMap<String, Verdict>| {
        if let Some((line_no, message)) = cur {
            if let Some(name) = by_line.get(&line_no) {
                let message = message.trim().to_string();
                // Two wordings, one meaning. `bv_decide` says "The prover found a
                // counterexample"; `decide` says the proposition "is false". Both are a
                // refutation, and both come from kernel-checked tactics.
                let refuted =
                    message.contains("counterexample") || message.contains("is false");
                let v = if refuted { Verdict::Refuted } else { Verdict::Hard(message) };
                verdicts.insert(name.clone(), v);
            }
        }
    };

    for line in text.lines() {
        match diagnostic_header(line) {
            Some((line_no, message)) => {
                finish(current.take(), &mut verdicts);
                current = Some((line_no, message));
            }
            None => {
                if let Some((_, message)) = current.as_mut() {
                    if !line.trim().is_empty() {
                        message.push('\n');
                        message.push_str(line);
                    }
                }
            }
        }
    }
    finish(current.take(), &mut verdicts);
    Ok(verdicts)
}

/// Parse a `file:line:col: error: message` header, returning the line and the first line of
/// the message.
///
/// The line is the *second-to-last* colon-separated field before `error:`. Taking the last
/// one instead is a bug that was live in this harness: it read the column as the line, so
/// every verdict was attributed to the wrong case and 47 spurious "mismatches" appeared
/// against a correct engine.
fn diagnostic_header(line: &str) -> Option<(usize, String)> {
    let idx = line.find(": error: ")?;
    let head = &line[..idx];
    let mut fields = head.rsplit(':');
    let _column = fields.next();
    let line_no = fields.next().and_then(|s| s.parse::<usize>().ok())?;
    Some((line_no, line[idx + ": error: ".len()..].to_string()))
}

fn main() {
    let bin = lean_bin();
    if !lean_available(&bin) {
        eprintln!(
            "leandiff: `{bin}` is not available, so the oracle cannot run.\n\
             Install Lean 4 (`curl -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y`)\n\
             and set LEAN_BIN if it is not on PATH. An oracle that did not run is not\n\
             evidence about the engine."
        );
        std::process::exit(2);
    }

    let cases_n: u32 = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(64);
    let cases = build_cases(cases_n);

    let tally = tally_identities(&cases, "leandiff");
    let proved_by_engine = cases.iter().filter(|c| c.ours.is_proved()).count();

    let dir: PathBuf = std::env::temp_dir().join("discharge_leandiff");
    let _ = fs::remove_dir_all(&dir);
    let (path, by_line) = match write_file(&dir, &cases) {
        Ok(v) => v,
        Err(e) => {
            eprintln!("leandiff: could not write the case file at {}: {e}", dir.display());
            std::process::exit(1);
        }
    };
    let verdicts = match run_lean(&path, &by_line) {
        Ok(v) => v,
        Err(e) => {
            eprintln!("leandiff: running `{bin}` failed: {e}");
            std::process::exit(1);
        }
    };

    // A `Hard` verdict is reported and fatal: the point of the oracle is that Lean either
    // checked the goal or exhibited a counterexample, and anything else means it did not
    // speak to the case.
    let mut hard = 0usize;
    for (name, v) in &verdicts {
        if let Verdict::Hard(message) = v {
            hard += 1;
            eprintln!("[leandiff] HARD {name}: {message}");
        }
    }

    let t = tally_backend(
        &cases,
        |case| match verdicts.get(&case.name) {
            Some(Verdict::Proved) => Some(true),
            Some(Verdict::Refuted) => Some(false),
            _ => None,
        },
        "leandiff",
    );

    // The control: the engine must have refuted it and Lean must have found a
    // counterexample. If either "proved" it, the harness is not asking a real question and
    // the agreement above would be worthless.
    let control_ok = {
        let name = "NEGATIVE_CONTROL_sub_comm";
        let ours_refuted = cases
            .iter()
            .find(|c| c.name == name)
            .map(|c| !c.ours.is_proved())
            .unwrap_or(false);
        let lean_refuted = matches!(verdicts.get(name), Some(Verdict::Refuted));
        ours_refuted && lean_refuted
    };
    println!(
        "cases={} proved_by_engine={} agree={} mismatch={} missing={} hard={} refuted_identity={} undecided_identity={} control_ok={}",
        cases.len(), proved_by_engine, t.agree, t.mismatch, t.missing, hard,
        tally.refuted, tally.undecided, control_ok
    );

    if t.mismatch > 0 || t.missing > 0 || hard > 0 || tally.refuted > 0 || !control_ok {
        eprintln!(
            "leandiff FAILED: mismatch={} missing={} hard={} refuted_identity={} control_ok={}",
            t.mismatch, t.missing, hard, tally.refuted, control_ok
        );
        std::process::exit(1);
    }
}

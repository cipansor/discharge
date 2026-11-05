// Differential oracle: the engine checked against Coq's kernel.
//
// The other harnesses ask a *decision procedure* to agree: Kani model-checks, Verus and Lean
// bit-blast. This one asks a *proof assistant* to evaluate the engine's own transcription of
// each case on every point of the 8-bit domain, and checks the result with `vm_compute`. So
// it is an oracle about a different thing -- not "does the engine decide this formula the
// same way" but "does the engine's arithmetic, written out in another logic, evaluate to the
// same truth value everywhere" -- and that is the point of having it. Coq has no machine word
// in its standard library, so the generator in `examples/support/mod.rs` spells every operator
// out over `Z` with explicit masks; the enumeration is the semantics, checked by the kernel.
//
// Coq is an *oracle*, not a dependency: `coqc` runs in a subprocess and the crate still builds
// with zero dependencies. If `coqc` is absent the harness exits 2 -- an oracle that did not run
// is not evidence. `COQC_BIN` names the binary when it is not on `PATH`.
//
// The enumeration makes this the *slowest* oracle by a wide margin: three variables is 16.7M
// points. So unlike the others, this harness takes a *subset* of the corpus by default --
// see `SELECTED` -- and the selection is stated rather than silently truncated.

mod support;

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use support::{
    Case, PARAMS, build_cases, coq_preamble, coq_pred, params_used, tally_backend, tally_identities,
};

/// The corpus names this oracle checks, in the default run.
///
/// The full sweep is not run here for a reason that is about the *oracle*, not the engine:
/// enumeration is 256^vars, so a three-variable case is 16.7M evaluations and a multiplier
/// case over three variables takes minutes where the same case is milliseconds for Lean.
/// Every name here is chosen to exercise a different operator's transcription -- including
/// all three shift rules and the sign-bit branch of `ashr_eng`, which is where a hand-written
/// `Z` encoding is most likely to be subtly wrong -- and the negative control is always
/// included so the run can still fail.
const SELECTED: &[&str] = &[
    "add_comm",
    "add_assoc",
    "sub_self",
    "add_sub_cancel",
    "mul_comm",
    "mul_one",
    "band_comm",
    "bor_self",
    "bxor_self",
    "demorgan",
    "shl_zero",
    "lshr_zero",
    "ashr_zero",
    "shl_eight",
    "lshr_eight",
    "lshr_seven_80",
    "ashr_sign_80",
    "ashr_top_0x40",
    "shl_one_80",
    "ult_irrefl",
    "ule_refl",
    "ult_antisym",
    "mask_4_upper_clear",
    "mask_8_identity",
    "ite_guard",
    "add_band_distrib_lo",
];

/// Write the `.v` file and return the line number each `Print` landed on.
///
/// The verdict is read back from `Print`, not from `Qed`: every case becomes a `Definition`
/// of type `bool` whose body is `Eval vm_compute in <predicate over the enumerated domain>`,
/// and `Print` then emits `case_N = true : bool` or `case_N = false : bool`. That avoids
/// relying on `Qed` succeeding, which it only does for *true* goals, and it gives a verdict
/// for the refuted cases too -- which is what makes a mismatch detectable at all.
fn write_file(dir: &Path, cases: &[Case]) -> std::io::Result<(PathBuf, BTreeMap<usize, String>)> {
    fs::create_dir_all(dir)?;
    let mut text = String::from(coq_preamble());
    text.push('\n');
    for (i, case) in cases.iter().enumerate() {
        // Enumerate only the variables the case reads. `forall256` is nested once per used
        // parameter, each binding the parameter's *name* so the body can refer to it, and an
        // unused one is simply not bound -- `mask_8_identity` mentions only `a`, so it costs
        // 256 evaluations instead of 16.7M and reaches the same verdict. The nesting order
        // does not matter, only that every name the body uses is bound.
        let used = params_used(&case.ir);
        let mut body = coq_pred(&case.ir);
        for &i in used.iter().rev() {
            body = format!("forall256 (fun {} => {body})", PARAMS[i]);
        }
        text.push_str(&format!(
            "Definition case_{i} : bool := Eval vm_compute in ({body}).\n"
        ));
    }
    text.push('\n');
    // The `Print` lines come after every definition, so the file is one block of
    // definitions then one block of reports; the line of each report is what a verdict is
    // attributed to.
    let mut by_line = BTreeMap::new();
    for (i, case) in cases.iter().enumerate() {
        let line_no = text.lines().count() + 1;
        by_line.insert(line_no, case.name.clone());
        text.push_str(&format!("Print case_{i}.\n"));
    }
    let path = dir.join("cases.v");
    fs::write(&path, text)?;
    Ok((path, by_line))
}

/// The `coqc` binary to use: `COQC_BIN` if set, else `coqc` from `PATH`.
fn coqc_bin() -> String {
    std::env::var("COQC_BIN").unwrap_or_else(|_| "coqc".to_string())
}

fn coq_available(bin: &str) -> bool {
    Command::new(bin)
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
}

fn main() {
    let bin = coqc_bin();
    if !coq_available(&bin) {
        eprintln!(
            "coqdiff: `{bin}` is not available, so the oracle cannot run.\n\
             Install Coq (`apt-get install coq`, or opam) and set COQC_BIN if it is not on\n\
             PATH. An oracle that did not run is not evidence about the engine."
        );
        std::process::exit(2);
    }

    let all = build_cases(0);
    let cases: Vec<Case> = all
        .into_iter()
        .filter(|c| SELECTED.contains(&c.name.as_str()) || c.name.starts_with("NEGATIVE"))
        .collect();
    if cases.is_empty() {
        eprintln!("coqdiff: none of the selected corpus names exist -- SELECTED is stale");
        std::process::exit(1);
    }

    let tally = tally_identities(&cases, "coqdiff");
    let proved_by_engine = cases.iter().filter(|c| c.ours.is_proved()).count();

    let dir: PathBuf = std::env::temp_dir().join("discharge_coqdiff");
    let _ = fs::remove_dir_all(&dir);
    let (path, by_line) = match write_file(&dir, &cases) {
        Ok(v) => v,
        Err(e) => {
            eprintln!("coqdiff: could not write the case file at {}: {e}", dir.display());
            std::process::exit(1);
        }
    };

    // `coqc` with no `-Q`/`-R` writes `cases.vo` next to the source; the run is in a temp
    // dir, so that is where it lands and nothing litters the repository.
    let out = match Command::new(&bin).arg(&path).output() {
        Ok(o) => o,
        Err(e) => {
            eprintln!("coqdiff: running `{bin}` failed: {e}");
            std::process::exit(1);
        }
    };
    let mut text = String::from_utf8_lossy(&out.stdout).into_owned();
    text.push('\n');
    text.push_str(&String::from_utf8_lossy(&out.stderr));

    // `case_7 = true` / `case_7 = false`, on the `Print` line. A `Print` that produced no
    // line at all is a missing verdict, not a pass -- the same rule the other harnesses use.
    let mut verdicts: BTreeMap<String, bool> = BTreeMap::new();
    for line in text.lines() {
        let Some((lhs, rhs)) = line.trim().split_once(" = ") else { continue };
        let Some(idx) = lhs.strip_prefix("case_") else { continue };
        let Ok(i) = idx.parse::<usize>() else { continue };
        let rhs = rhs.trim();
        if rhs.starts_with("true") {
            if let Some(name) = by_line.values().nth(i) {
                verdicts.insert(name.clone(), true);
            }
        } else if rhs.starts_with("false") {
            if let Some(name) = by_line.values().nth(i) {
                verdicts.insert(name.clone(), false);
            }
        }
    }

    // A `coqc` that failed to *compile* the file is not a set of verdicts, so the exit
    // status is checked before any of them are believed.
    if !out.status.success() {
        eprintln!("coqdiff: `{bin}` exited with {}, so no verdict is trustworthy:", out.status);
        for line in text.lines().filter(|l| l.contains("Error")) {
            eprintln!("  {line}");
        }
        std::process::exit(1);
    }

    let t = tally_backend(&cases, |case| verdicts.get(&case.name).copied(), "coqdiff");

    let control_ok = {
        let name = "NEGATIVE_CONTROL_sub_comm";
        let ours_refuted = cases
            .iter()
            .find(|c| c.name == name)
            .map(|c| !c.ours.is_proved())
            .unwrap_or(false);
        let coq_refuted = verdicts.get(name) == Some(&false);
        ours_refuted && coq_refuted
    };
    println!(
        "cases={} proved_by_engine={} agree={} mismatch={} missing={} refuted_identity={} undecided_identity={} control_ok={}",
        cases.len(), proved_by_engine, t.agree, t.mismatch, t.missing,
        tally.refuted, tally.undecided, control_ok
    );

    if t.mismatch > 0 || t.missing > 0 || tally.refuted > 0 || !control_ok {
        eprintln!(
            "coqdiff FAILED: mismatch={} missing={} refuted_identity={} control_ok={}",
            t.mismatch, t.missing, tally.refuted, control_ok
        );
        std::process::exit(1);
    }
}

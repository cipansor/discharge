//! The comparison fixtures' gate, as a driver rather than a scoreboard scrape.
//!
//! `tools/comparison/run.sh` used to assert the *coverage* line
//! (`decided 0 of 1`) for each injected bug. That line counts only
//! `FnOutcome::Verified`, so `Failed`, `Incomplete` and `Skipped` all leave it at
//! zero -- which means a fixture whose contract became *unreadable* would still
//! read `decided 0 of 1` and the gate would call it a caught defect while having
//! no counterexample at all. That is the "teeth have to isolate the guard they
//! claim to test" rule violated by the gate that enforces it: a rejection test
//! that cannot tell a refutation from a lost proof is not a rejection test.
//!
//! So the assertion here is on the per-function [`FnOutcome`], not on a count:
//!
//!   * the positive fixture must be `Verified` for every contracted function;
//!   * each bug fixture must be `Failed` with the *expected obligation kind* --
//!     the panic for the swapped `sat_add`, the postcondition for the wrong-arm
//!     `clamp`, the loop invariant for the wrong-body `sum_to`;
//!   * `Incomplete` and `Skipped` are refusals of the *fixture*, not evidence
//!     about the defect, so they fail the run and say which one they were;
//!   * the degenerate implementations (whole-function contracts mean they must
//!     be refused) are checked the same way.
//!
//! `Failed` with the wrong kind is also a failure: a fixture that trips the
//! wrong obligation is not testing what it claims, which is exactly the trap the
//! old `n <= 8` Coq theorem fell into.
//!
//! Exit status: 0 every claim held, 1 a claim did not hold, 2 no usable
//! `DISCHARGE_RUSTC` (reported and skipped by the caller, like the other gates).
//!
//! Run it with a nightly named:
//!
//! ```console
//! $ DISCHARGE_RUSTC=$(rustup which --toolchain nightly rustc) \
//!     cargo run --features std --example comparison_check
//! ```

use std::path::{Path, PathBuf};

use discharge::mir::spec;
use discharge::mir::verify::{self, FnOutcome};

/// What one fixture must produce.
enum Want {
    /// Every contracted function is fully verified.
    Verified,
    /// The named function fails, and its obligation kind starts with this text.
    ///
    /// A prefix rather than an equality because a panic's kind carries rustc's
    /// own message (`panic: attempt to compute \`{} + {}\`, which would
    /// overflow`), which is rustc's wording to change, not this gate's to pin.
    Failed(&'static str),
}

/// One fixture: its path, and the claim it is evidence for.
struct Fixture {
    path: &'static str,
    /// The function the claim is about. `None` means every contracted function.
    function: Option<String>,
    want: Want,
    /// What the fixture is, for the failure message.
    why: &'static str,
}

const ROOT: &str = "examples/comparison";

/// The fixtures, as data, so the driver and the shell script cannot disagree
/// about which files are checked or what each one must do.
fn fixtures() -> Vec<Fixture> {
    vec![
        Fixture {
            path: "target.rs",
            function: None,
            want: Want::Verified,
            why: "the positive fixture: the same three functions every tool proves",
        },
        Fixture {
            path: "bugs/target.rs",
            function: Some("sat_add".to_string()),
            want: Want::Failed("panic"),
            why: "swapped branches, so the guarded `+` is the one that can overflow",
        },
        Fixture {
            path: "bugs/clamp.rs",
            function: Some("clamp".to_string()),
            want: Want::Failed("postcondition"),
            why: "returns `hi` below the range, so the contract's first disjunct is false",
        },
        Fixture {
            path: "bugs/loop.rs",
            function: Some("sum_to".to_string()),
            want: Want::Failed("loop invariant"),
            why: "the loop body adds two, so the invariant is not preserved",
        },
    ]
}

fn main() {
    let rustc = match std::env::var("DISCHARGE_RUSTC") {
        Ok(r) if !r.trim().is_empty() => r,
        _ => {
            eprintln!("comparison_check: set DISCHARGE_RUSTC to a nightly `rustc`");
            std::process::exit(2);
        }
    };

    let mut failures: Vec<String> = Vec::new();
    let mut checked = 0usize;

    for f in fixtures() {
        let path = PathBuf::from(ROOT).join(f.path);
        checked += 1;
        match check_one(&rustc, &path, &f) {
            Ok(line) => println!("ok   {:<20} {line}", f.path),
            Err(why) => {
                println!("FAIL {:<20} {why}", f.path);
                failures.push(format!("{}: {why}", f.path));
            }
        }
    }

    for (name, src) in degenerate() {
        checked += 1;
        let tmp = write_temp(&name, &src);
        let f = Fixture {
            path: "",
            function: Some(name.clone()),
            want: Want::Failed("postcondition"),
            why: "degenerate implementation the whole-function contract must refuse",
        };
        match check_one(&rustc, &tmp, &f) {
            Ok(line) => println!("ok   {:<20} {line}", format!("degenerate/{name}")),
            Err(why) => {
                println!("FAIL {:<20} {why}", format!("degenerate/{name}"));
                failures.push(format!("degenerate/{name}: {why}"));
            }
        }
        let _ = std::fs::remove_file(&tmp);
    }

    println!("\nchecked {checked} fixture(s)");
    if failures.is_empty() {
        println!("every comparison claim held");
    } else {
        println!("\nUNEXPECTED:");
        for f in &failures {
            println!("  {f}");
        }
        std::process::exit(1);
    }
}

/// Run one fixture and check its outcome against `f.want`.
fn check_one(rustc: &str, path: &Path, f: &Fixture) -> Result<String, String> {
    let text = std::fs::read_to_string(path)
        .map_err(|e| format!("cannot read {}: {e}", path.display()))?;
    let specs = spec::extract(&text);
    let mir = verify::emit_mir_with(rustc, path).map_err(|e| format!("could not get MIR: {e}"))?;

    let only: Vec<String> = match &f.function {
        Some(n) => vec![n.clone()],
        None => {
            let mut names: Vec<String> = specs.by_fn.keys().cloned().collect();
            names.extend(specs.by_method.keys().map(|(_, _, m)| m.clone()));
            names.sort();
            names.dedup();
            names
        }
    };
    if only.is_empty() {
        return Err("no contract was found in the fixture".into());
    }

    let report =
        verify::verify_mir_text(&mir, &specs, &only).map_err(|e| format!("driver error: {e}"))?;
    if !report.missing.is_empty() {
        return Err(format!(
            "contracted but absent from the MIR: {:?}",
            report.missing
        ));
    }
    if report.outcomes.is_empty() {
        return Err("the driver produced no outcome (nothing was verified)".into());
    }

    match &f.want {
        Want::Verified => {
            for (name, outcome) in &report.outcomes {
                match outcome {
                    FnOutcome::Verified { .. } => {}
                    // The three refusals are named separately: "skipped" is a
                    // contract that could not be read and "incomplete" is a
                    // budget or an unmodelled construct, and neither is evidence
                    // that the code is right *or* wrong.
                    FnOutcome::Failed { kind, detail } => {
                        return Err(format!(
                            "{name}: expected Verified, got FAILED ({kind} — {detail})"
                        ));
                    }
                    FnOutcome::Incomplete { reasons, .. } => {
                        return Err(format!(
                            "{name}: incomplete, so not verified ({})",
                            reasons.join("; ")
                        ));
                    }
                    FnOutcome::Skipped { reason } => {
                        return Err(format!("{name}: skipped, so never checked ({reason})"));
                    }
                }
            }
            Ok(format!("{} function(s) verified", report.outcomes.len()))
        }
        Want::Failed(prefix) => {
            if report.outcomes.len() != 1 {
                return Err(format!(
                    "expected exactly one outcome for `{}`, got {}",
                    f.function.as_deref().unwrap_or("?"),
                    report.outcomes.len()
                ));
            }
            let (name, outcome) = &report.outcomes[0];
            match outcome {
                FnOutcome::Failed { kind, detail } => {
                    if kind.starts_with(prefix) {
                        Ok(format!("{name}: FAILED — {kind} (witness: {detail})"))
                    } else {
                        Err(format!(
                            "{name}: failed on the WRONG obligation: expected `{prefix}...`, got `{kind}` \
                             -- the fixture is not testing what it claims ({})",
                            f.why
                        ))
                    }
                }
                // The heart of the fix: these used to read `decided 0 of 1` and
                // pass. A skipped fixture is a lost proof, not a refutation.
                FnOutcome::Skipped { reason } => Err(format!(
                    "{name}: SKIPPED, so the contract was never refuted -- the fixture is a lost \
                     proof, not a caught defect ({reason})"
                )),
                FnOutcome::Incomplete { reasons, .. } => Err(format!(
                    "{name}: INCOMPLETE, so no counterexample was found -- the fixture is a lost \
                     proof, not a caught defect ({})",
                    reasons.join("; ")
                )),
                FnOutcome::Verified { .. } => Err(format!(
                    "{name}: VERIFIED, so the defect was not caught at all"
                )),
            }
        }
    }
}

/// The degenerate implementations the whole-function contracts must refuse.
///
/// `u16::MAX` for every input satisfies `ret >= a && ret >= b`; `lo` for every
/// input satisfies `lo <= ret <= hi`. Both passed the bounds-only contracts the
/// first version of this directory shipped, so they are the evidence that the
/// contracts now state the whole function.
fn degenerate() -> Vec<(String, String)> {
    vec![
        (
            "sat_add".to_string(),
            "/// requires: true\n\
             /// ensures: ret >= a\n\
             /// ensures: ret >= b\n\
             /// ensures: a <= 65535u16 - b || ret == 65535u16\n\
             /// ensures: a > 65535u16 - b || ret == a + b\n\
             pub fn sat_add(a: u16, b: u16) -> u16 { 65535u16 }\n"
                .to_string(),
        ),
        (
            "clamp".to_string(),
            "/// requires: lo <= hi\n\
             /// ensures: !(x < lo) || ret == lo\n\
             /// ensures: !(lo <= x && x > hi) || ret == hi\n\
             /// ensures: !(lo <= x && x <= hi) || ret == x\n\
             pub fn clamp(x: u16, lo: u16, hi: u16) -> u16 { lo }\n"
                .to_string(),
        ),
    ]
}

/// Write a scratch fixture beside the comparison directory, so the MIR frontend
/// is handed a real path and the file is removed again by the caller.
fn write_temp(name: &str, src: &str) -> PathBuf {
    let path = std::env::temp_dir().join(format!("discharge_comparison_degenerate_{name}.rs"));
    std::fs::write(&path, src).expect("write scratch fixture");
    path
}

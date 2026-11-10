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
//!   * the positive fixture must carry a contract for *each* function it claims
//!     and be `Verified` for every one of them. The names are pinned here rather
//!     than read from `spec::extract`, because a name read from the contracts
//!     disappears with the contract: deleting one function's contract would
//!     shrink the request list, the remaining functions would pass, and the gate
//!     would report success for a claim it never checked;
//!   * each bug fixture must be `Failed` with the *exact* obligation kind -- the
//!     `+` overflow for the swapped `sat_add`, the postcondition for the
//!     wrong-arm `clamp`, the loop invariant for the wrong-body `sum_to`. The
//!     whole kind, not a `panic` prefix: a prefix accepts *any* panic, so a
//!     divide-by-zero before the addition would satisfy a test about an overflow;
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
    /// Every one of these functions must carry a contract *and* be `Verified`.
    ///
    /// The names are pinned in the source, not read back from `spec::extract`:
    /// names read from the contracts vanish when a contract does, which is the
    /// hole this variant closes.
    Verified(&'static [&'static str]),
    /// The named function fails, and its obligation kind is *exactly* this text.
    ///
    /// Exact rather than a prefix: a `panic` prefix would accept any panic, so a
    /// divide-by-zero before the addition would pass a test about an overflow.
    Failed {
        /// The function the claim is about.
        function: &'static str,
        /// The exact obligation kind the failure must name.
        kind: &'static str,
    },
}

/// One fixture: its path, and the claim it is evidence for.
struct Fixture {
    path: &'static str,
    want: Want,
    /// What the fixture is, for the failure message.
    why: &'static str,
}

const ROOT: &str = "examples/comparison";

/// The exact panic text for the guarded addition in `sat_add`.
///
/// It is rustc's own wording (`src/mir/shape.rs` maps it to `PanicKind::OverflowAdd`),
/// spelled out because the claim is about *this* overflow and not about panics in
/// general.
const OVERFLOW_ADD: &str = "panic: attempt to compute `{} + {}`, which would overflow";

/// The fixtures, as data, so the driver and the shell script cannot disagree
/// about which files are checked or what each one must do.
fn fixtures() -> Vec<Fixture> {
    vec![
        Fixture {
            path: "target.rs",
            want: Want::Verified(&["sat_add", "clamp", "sum_to"]),
            why: "the positive fixture: the same three functions every tool proves",
        },
        Fixture {
            path: "bugs/target.rs",
            want: Want::Failed {
                function: "sat_add",
                kind: OVERFLOW_ADD,
            },
            why: "swapped branches, so the guarded `+` is the one that can overflow",
        },
        Fixture {
            path: "bugs/clamp.rs",
            want: Want::Failed {
                function: "clamp",
                kind: "postcondition",
            },
            why: "returns `hi` below the range, so the contract's first disjunct is false",
        },
        Fixture {
            path: "bugs/loop.rs",
            want: Want::Failed {
                function: "sum_to",
                kind: "loop invariant preserved",
            },
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
        let tmp = write_scratch(&name, &src);
        let why = "degenerate implementation the whole-function contract must refuse";
        let r = check_failed(&rustc, &tmp, &name, "postcondition", why);
        // Remove the scratch file only once its MIR has been emitted, which
        // `check_failed` has done by the time it returns. A concurrent gate uses
        // its own path, so it never sees this removal.
        let _ = std::fs::remove_file(&tmp);
        match r {
            Ok(line) => println!("ok   {:<20} {line}", format!("degenerate/{name}")),
            Err(why) => {
                println!("FAIL {:<20} {why}", format!("degenerate/{name}"));
                failures.push(format!("degenerate/{name}: {why}"));
            }
        }
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
    match &f.want {
        Want::Verified(expected) => check_verified(rustc, path, expected),
        Want::Failed { function, kind } => check_failed(rustc, path, function, kind, f.why),
    }
}

/// Assert that each pinned name carries a contract and is `Verified`.
fn check_verified(rustc: &str, path: &Path, expected: &[&str]) -> Result<String, String> {
    let text = std::fs::read_to_string(path)
        .map_err(|e| format!("cannot read {}: {e}", path.display()))?;
    let specs = spec::extract(&text);
    let mir = verify::emit_mir_with(rustc, path).map_err(|e| format!("could not get MIR: {e}"))?;

    // The contract must exist for each pinned name. Without this the name would
    // still be requested and still be found in the MIR, so it would come back
    // `Verified` for panic freedom alone -- a `Verified` with zero obligations --
    // and the positive claim would go unchecked. Checking the *contract* is what
    // separates "proved the claim" from "proved nothing was left to prove".
    let mut contracted: Vec<String> = specs.by_fn.keys().cloned().collect();
    contracted.extend(specs.by_method.keys().map(|(_, _, m)| m.clone()));
    for want in expected {
        if !contracted.iter().any(|c| names_match(c, want)) {
            return Err(format!(
                "`{want}` carries no contract in the fixture, so the positive claim would go \
                 unchecked (contracts found: {contracted:?})"
            ));
        }
    }

    let wanted: Vec<String> = expected.iter().map(|s| s.to_string()).collect();
    let report =
        verify::verify_mir_text(&mir, &specs, &wanted).map_err(|e| format!("driver error: {e}"))?;
    if !report.missing.is_empty() {
        return Err(format!(
            "contracted but absent from the MIR: {:?}",
            report.missing
        ));
    }
    // One outcome per expected function: fewer means one was not checked, more
    // means the request matched something it should not have.
    if report.outcomes.len() != expected.len() {
        return Err(format!(
            "expected {} outcome(s) for {:?}, got {} ({:?})",
            expected.len(),
            expected,
            report.outcomes.len(),
            report
                .outcomes
                .iter()
                .map(|(n, _)| n.as_str())
                .collect::<Vec<_>>()
        ));
    }
    for want in expected {
        let Some((name, outcome)) = report.outcomes.iter().find(|(n, _)| names_match(n, want))
        else {
            return Err(format!("`{want}` has no outcome in the report"));
        };
        match outcome {
            FnOutcome::Verified { .. } => {}
            // The three refusals are named separately: "skipped" is a contract
            // that could not be read and "incomplete" is a budget or an unmodelled
            // construct, and neither is evidence that the code is right *or* wrong.
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
    Ok(format!("{} function(s) verified", expected.len()))
}

/// Assert that `function` fails with exactly the obligation kind `want_kind`.
fn check_failed(
    rustc: &str,
    path: &Path,
    function: &str,
    want_kind: &str,
    why: &str,
) -> Result<String, String> {
    let text = std::fs::read_to_string(path)
        .map_err(|e| format!("cannot read {}: {e}", path.display()))?;
    let specs = spec::extract(&text);
    let mir = verify::emit_mir_with(rustc, path).map_err(|e| format!("could not get MIR: {e}"))?;

    let only = vec![function.to_string()];
    let report =
        verify::verify_mir_text(&mir, &specs, &only).map_err(|e| format!("driver error: {e}"))?;
    if !report.missing.is_empty() {
        return Err(format!(
            "contracted but absent from the MIR: {:?}",
            report.missing
        ));
    }
    if report.outcomes.len() != 1 {
        return Err(format!(
            "expected exactly one outcome for `{function}`, got {} ({:?})",
            report.outcomes.len(),
            report
                .outcomes
                .iter()
                .map(|(n, _)| n.as_str())
                .collect::<Vec<_>>()
        ));
    }
    let (name, outcome) = &report.outcomes[0];
    match outcome {
        FnOutcome::Failed { kind, detail } => {
            if kind == want_kind {
                Ok(format!("{name}: FAILED — {kind} (witness: {detail})"))
            } else {
                Err(format!(
                    "{name}: failed on the WRONG obligation: expected `{want_kind}`, got `{kind}` \
                     -- the fixture is not testing what it claims ({why})"
                ))
            }
        }
        // These used to read `decided 0 of 1` and pass. A skipped fixture is a
        // lost proof, not a refutation.
        FnOutcome::Skipped { reason } => Err(format!(
            "{name}: SKIPPED, so the contract was never refuted -- the fixture is a lost proof, \
             not a caught defect ({reason})"
        )),
        FnOutcome::Incomplete { reasons, .. } => Err(format!(
            "{name}: INCOMPLETE, so no counterexample was found -- the fixture is a lost proof, \
             not a caught defect ({})",
            reasons.join("; ")
        )),
        FnOutcome::Verified { .. } => Err(format!(
            "{name}: VERIFIED, so the defect was not caught at all"
        )),
    }
}

/// Whether a report key names `want`, by the same rules `verify::select` uses: an
/// exact key, or a bare `::`-tail.
fn names_match(key: &str, want: &str) -> bool {
    key == want || key.rsplit("::").next() == Some(want)
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

/// Write a scratch fixture to a path unique *per call*, and return it.
///
/// Unique per call, not per name: two gates running at once would otherwise share
/// one file, and the first to finish would remove it while the second's `rustc`
/// was still opening it -- a valid gate failing for a scheduling reason. This
/// mirrors `verify::emit_mir_with`, which names its temp MIR per call for the
/// same reason. The caller removes the file once its MIR has been emitted.
fn write_scratch(name: &str, src: &str) -> PathBuf {
    use std::sync::atomic::{AtomicU64, Ordering};
    static SEQ: AtomicU64 = AtomicU64::new(0);
    let seq = SEQ.fetch_add(1, Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!(
        "discharge-comparison-{}-{seq}-{name}.rs",
        std::process::id()
    ));
    std::fs::write(&path, src).expect("write scratch fixture");
    path
}

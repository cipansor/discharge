//! The MIR frontend's coverage scoreboard: how much *realistic* Rust does it decide?
//!
//! This is deliberately **not** a gate. `scripts/gate.sh` asserts verdicts on
//! `examples/mir_targets/actuator.rs`, a regression corpus where every function
//! is expected to be decided. This example measures the opposite: it runs the
//! frontend over `examples/mir_targets/realistic.rs`, a corpus of ordinary Rust
//! that is *not* curated to be decidable, and prints the tally. A roadmap that
//! says "widen real-Rust support" is unfalsifiable; a number that moves from 2 to
//! 12 is not. So the scoreboard is the roadmap's evidence, and it exits 0
//! whatever it finds. The remainder it does not decide are the *next* gaps, and
//! each one names itself in the `detail` column rather than being summarised.
//!
//! Run it with a nightly named, or it says so and stops:
//!
//! ```console
//! $ VERIF_RUSTC=$(rustup which --toolchain nightly rustc) \
//!     cargo run --features std --example mir_coverage
//! function             outcome      detail
//! halve_guarded        verified     2 obl, 1 panic
//! pick_from            skipped      unreadable `requires`: unknown name `c` ...
//! sum_to               verified     5 obl, 2 panic
//! is_nonzero_after     verified     3 obl, 0 panic
//! ...
//! decided 10 of 14
//! ```
//!
//! An unrecognised argument is treated as a path, so a new corpus can be
//! measured without editing this file. A second argument names one function to
//! measure on its own, which is what makes a slow shape attributable: the
//! engine has a size budget, not a time budget, so a shape can take a long time
//! without ever answering `Unknown`, and the per-function elapsed time is the
//! evidence for where that time goes.

use std::path::PathBuf;
use std::time::Instant;

use verif::mir::spec;
use verif::mir::verify::{self, FnOutcome};

const DEFAULT_TARGET: &str = "examples/mir_targets/realistic.rs";

fn main() {
    let mut args = std::env::args().skip(1);
    let target = args.next().unwrap_or_else(|| DEFAULT_TARGET.into());
    let only: Option<String> = args.next();
    let src = PathBuf::from(&target);
    let rustc = std::env::var("VERIF_RUSTC").unwrap_or_else(|_| "rustc".into());

    let (mir, edition) = match verify::emit_mir_with_opts(&rustc, &src, &verify::MirOptions::default())
    {
        Ok(m) => m,
        Err(e) => {
            // "the tool could not run" must never look like "the code is wrong",
            // so this is a distinct message and a distinct exit. The error already
            // names the compiler, the edition that was used and the reason (a
            // missing edition, a compiler error), so it is printed as it stands
            // rather than followed by a hint that would send the reader after the
            // wrong toolchain -- `--emit=mir` is stable, and an edition error is
            // not a toolchain problem.
            eprintln!("mir_coverage: could not get MIR from {}: {e}", src.display());
            std::process::exit(2);
        }
    };

    let source = match std::fs::read_to_string(&src) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("mir_coverage: cannot read {}: {e}", src.display());
            std::process::exit(2);
        }
    };
    let specs = spec::extract(&source);

    // Order by name so the output is diffable between runs. Methods are listed by
    // their bare tail, like free functions, because that is what a reader looks
    // for; two `impl` blocks that share a tail are reported under `Owner::method`
    // by the driver, so they still appear once each.
    let mut names: Vec<String> = specs.by_fn.keys().cloned().collect();
    names.extend(specs.by_method.keys().map(|(_, _, m)| m.clone()));
    names.sort();
    names.dedup();

    println!("# {target} ({edition})");
    println!("{:<22} {:<12} {:>9}  detail", "function", "outcome", "elapsed");
    let mut decided = 0usize;
    // With a filter, hand the *whole* requested name to the driver once. The list
    // above holds bare tails, but a method whose tail is shared is *reported* as
    // `Owner::method`, so a reader who copies a name out of the output must be
    // able to paste it back. Passing it through lets `verify_mir_text` match the
    // report key exactly (one row for one `Owner::method`) while a bare tail still
    // matches every owner that shares it.
    let selected: Vec<String> = match &only {
        Some(want) => vec![want.clone()],
        None => names.clone(),
    };
    for name in &selected {
        let started = Instant::now();
        let Ok(report) = verify::verify_mir_text(&mir, &specs, std::slice::from_ref(name)) else {
            println!("{name:<22} {:<12} {:>9}  driver error", "error", "-");
            continue;
        };
        let elapsed = started.elapsed();
        for (fname, outcome) in &report.outcomes {
            let (label, detail) = describe(outcome);
            if label == "verified" {
                decided += 1;
            }
            // Truncate on a char boundary, not a byte offset: a counterexample
            // can contain a multi-byte character and slicing blind would panic.
            let short: String = detail.chars().take(72).collect();
            println!("{fname:<22} {label:<12} {:>8.2}s  {short}", elapsed.as_secs_f64());
        }
    }
    if only.is_none() {
        // Every free function and every method is one outcome, so the
        // denominator is their sum -- a shared method tail is deduplicated for
        // display but is still two outcomes.
        let total = specs.by_fn.len() + specs.by_method.len();
        println!("\ndecided {decided} of {total}");
    }
}

/// The label and detail for one outcome, so the `match` lives in one place.
fn describe(outcome: &FnOutcome) -> (&'static str, String) {
    match outcome {
        FnOutcome::Verified { obligations, panics_ruled_out } => (
            "verified",
            format!("{obligations} obligation(s), {panics_ruled_out} panic(s) ruled out"),
        ),
        FnOutcome::Failed { kind, detail } => ("FAILED", format!("{kind} — {detail}")),
        FnOutcome::Incomplete { reasons, .. } => ("incomplete", reasons.join("; ")),
        FnOutcome::Skipped { reason } => ("skipped", reason.clone()),
    }
}

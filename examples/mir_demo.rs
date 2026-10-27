//! The frontend's proof-of-work: real Rust functions, verified from their MIR.
//!
//! Run with: `cargo run --features std --example mir_demo`
//!
//! The functions under test live in `examples/mir_targets/actuator.rs`, which
//! does not import `discharge` at all. Contracts are doc comments
//! (`requires:` / `ensures:` lines); the *bodies* are read from the MIR that
//! `rustc` lowers them to. Nothing is re-modelled by hand, which is the whole
//! point — the earlier frontends in this crate proved things about expressions
//! written next to the code, and a human had to keep the two in step.
//!
//! Set `DISCHARGE_RUSTC` to a nightly `rustc`, since `--emit=mir` needs one:
//!
//! ```text
//! DISCHARGE_RUSTC=$(rustup which --toolchain nightly rustc) \
//!   cargo run --features std --example mir_demo
//! ```

use discharge::mir::verify::{self, FnOutcome};

const TARGET: &str = "examples/mir_targets/actuator.rs";

/// What each function is expected to produce.
///
/// `Incomplete` is a first-class expectation, not a failure of the demo. It is
/// what an honest bounded checker returns when the query is beyond its engine,
/// and saying so is the point: `sat_mul` at `u16` needs a 32-bit product, which
/// is the BDD scaling wall this crate documents, so the right answer is "I could
/// not decide" rather than a guess in either direction.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Expect {
    Verified,
    Failed,
    Incomplete,
}

/// The expectations, stated as data so the demo and the test suite share them.
pub fn expectations() -> [(&'static str, Expect); 13] {
    use Expect::*;
    [
        ("clamp", Verified),
        ("rate_limit", Verified),
        ("sat_add", Verified),
        ("sat_sub", Verified),
        ("shift_const", Verified),
        // The guard is the caller's here, and rustc's own `assert(n < 16)` still
        // reports `n == 16` as a panic, so this must fail.
        ("shift_left", Failed),
        ("sat_shift", Verified),
        // The widened product is past the wall; declining is correct here.
        ("sat_mul", Incomplete),
        ("unchecked_add", Failed),
        ("unchecked_sub", Failed),
        ("unchecked_div", Failed),
        ("unchecked_mul", Failed),
        // The guard prevents the overflow, so there is no panic — but the
        // `ensures` is wrong, and a postcondition obligation catches that.
        // This is the case that shows the check is not only about panics.
        ("off_by_one_guard", Failed),
    ]
}

fn main() {
    let only: Vec<String> = expectations().iter().map(|(n, _)| n.to_string()).collect();
    let report = match verify::verify_file(std::path::Path::new(TARGET), &only) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("could not verify: {e}");
            std::process::exit(2);
        }
    };

    println!("=== {TARGET} ===");
    for (name, outcome) in &report.outcomes {
        println!("{name:16} {outcome}");
    }
    if !report.missing.is_empty() {
        println!("\ncontracted but absent from the MIR: {:?}", report.missing);
    }
    println!(
        "\nverified={} failed={} incomplete={}",
        report.verified(),
        report.failed(),
        report.incomplete()
    );

    let mut bad = Vec::new();
    for (name, want) in expectations() {
        let Some((_, outcome)) = report.outcomes.iter().find(|(n, _)| n == name) else {
            bad.push(format!("{name}: not in the report"));
            continue;
        };
        let got = match outcome {
            FnOutcome::Verified { .. } => Expect::Verified,
            FnOutcome::Failed { .. } => Expect::Failed,
            FnOutcome::Incomplete { .. } => Expect::Incomplete,
            FnOutcome::Skipped { .. } => {
                bad.push(format!("{name}: skipped ({outcome})"));
                continue;
            }
        };
        if got != want {
            bad.push(format!("{name}: expected {want:?}, got {got:?} — {outcome}"));
        }
    }

    if bad.is_empty() {
        println!("All expectations met.");
    } else {
        println!("\nUNEXPECTED:");
        for b in &bad {
            println!("  {b}");
        }
        std::process::exit(1);
    }
}

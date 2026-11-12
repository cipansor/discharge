//! The example from `verif-arithmetic`'s `README.md`, compiled and run.
//!
//! The README is the crate's page on crates.io. Pinning its example here means a
//! change that breaks it fails `cargo test` rather than shipping a broken
//! example to every reader. Keep it in step with the first Rust block in
//! `verif-arithmetic/README.md`.

use verif_arithmetic::{checked_add, prove};

#[test]
fn readme_example_holds() {
    // The runtime behaviour...
    assert_eq!(checked_add(200, 55), Some(255));
    assert_eq!(checked_add(u32::MAX, 1), None);

    // ...and the proof that its overflow flag is exact.
    assert!(prove::checked_add_is_total().is_proved());
}

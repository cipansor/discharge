//! The flagship example from `README.md`, compiled and run.
//!
//! The README is the crate's page on crates.io, so an example there that no
//! longer compiles is the documentation lying to every reader who never opens
//! the source. A doc comment would catch it if the README were included as one,
//! but it is a 2600-line document with its own structure, so the example is
//! pinned here instead: this file is the compile check, and the assertion is the
//! behaviour check.
//!
//! Keep this in step with the first Rust block in `README.md`.

use verif::prelude::*;

#[test]
fn readme_flagship_example_proves_a_bound() {
    // ∀ x:u8. (x & 0x0f) < 16          — proved by the embedded SMT engine
    let proved = verif::smt::with_fresh(|| {
        let x = var(8);
        (x & 0x0fu32).lt_val(16).prove().is_proved()
    });
    assert!(proved);
}

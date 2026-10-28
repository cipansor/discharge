//! Bake the nightly sysroot's `lib` directory into the binary's runtime search
//! path.
//!
//! A crate that links rustc internals needs `librustc_driver-*.so` at *runtime*,
//! not just at link time, and cargo does not add the sysroot to the rpath for a
//! `rustc_private` binary. Without this the tool builds and then dies with
//! "cannot open shared object file", which is a confusing way to learn that the
//! toolchain is fine and only the loader path is missing.
//!
//! `RUSTC` is the compiler cargo is building with — a nightly, since that is the
//! only toolchain that can compile `#![feature(rustc_private)]` — so its sysroot
//! is the one holding the matching `librustc_driver`.

use std::process::Command;

fn main() {
    let rustc = std::env::var("RUSTC").unwrap_or_else(|_| "rustc".to_string());
    let Ok(out) = Command::new(&rustc).arg("--print").arg("sysroot").output() else {
        return;
    };
    if !out.status.success() {
        return;
    }
    let sysroot = String::from_utf8_lossy(&out.stdout).trim().to_string();
    let lib = format!("{sysroot}/lib");
    // `-Wl,-rpath,<dir>` is the GNU ld spelling; the tool targets linux here, and
    // on a platform where the flag is unknown the link simply ignores it and the
    // caller falls back to `LD_LIBRARY_PATH` (see `run.sh`).
    println!("cargo:rustc-link-arg=-Wl,-rpath,{lib}");
    println!("cargo:rerun-if-env-changed=RUSTC");
}

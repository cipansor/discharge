//! Bake the nightly sysroot's `lib` directory into the binary's runtime search
//! path, and turn a failed sysroot query into a message that names the real
//! problem.
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
//!
//! The failure this must not hide: `rustc` links `libLLVM`, and the directory
//! cargo puts on the build script's `LD_LIBRARY_PATH` is
//! `<sysroot>/lib/rustlib/<target>/lib` -- not `<sysroot>/lib`, where a bare
//! toolchain keeps `libLLVM`. `libLLVM` reaches the former only from the
//! `llvm-tools-preview` component, which is also the directory rustc passes to
//! the linker as `-L`. So on a `--profile minimal` nightly with only `rustc-dev`
//! both halves break at once: the query below cannot even start (its own `rustc`
//! will not load), and the eventual link fails to find `-lLLVM-*`. Returning
//! quietly on the first emits no rpath and no diagnostic, leaving the linker's
//! error two steps later as the only symptom -- which reads like a broken
//! toolchain rather than a missing component. Failing here, with the fix in the
//! message, is the difference between a five-minute fix and a bisect.

use std::process::Command;

fn main() {
    let rustc = std::env::var("RUSTC").unwrap_or_else(|_| "rustc".to_string());
    let out = Command::new(&rustc)
        .arg("--print")
        .arg("sysroot")
        .output()
        .unwrap_or_else(|e| panic!("could not run `{rustc} --print sysroot`: {e}"));
    if !out.status.success() {
        panic!(
            "`{rustc} --print sysroot` failed ({}): {}\n\
             This usually means the toolchain is missing the `llvm-tools-preview` \
             component, which ships the `libLLVM` that `rustc` needs to start. \
             Install it with: rustup component add llvm-tools-preview --toolchain nightly",
            out.status,
            String::from_utf8_lossy(&out.stderr).trim()
        );
    }
    let sysroot = String::from_utf8_lossy(&out.stdout).trim().to_string();
    let lib = format!("{sysroot}/lib");
    // `-Wl,-rpath,<dir>` is the GNU ld spelling; the tool targets linux here, and
    // on a platform where the flag is unknown the link simply ignores it and the
    // caller falls back to `LD_LIBRARY_PATH` (see `run.sh`).
    println!("cargo:rustc-link-arg=-Wl,-rpath,{lib}");
    println!("cargo:rerun-if-env-changed=RUSTC");
}

export PATH=/workspace/.rust/cargo/bin:$PATH
export RUSTUP_HOME=/workspace/.rust/rustup CARGO_HOME=/workspace/.rust/cargo
unset RUSTC
R=$(rustup which --toolchain nightly rustc)
rc() { printf '#![allow(dead_code,unused)]\nfn s0(%s)->u8{ let _ = %s; 0 }\n' "$1" "$2" > .sweep/tmp/rc.rs; if $R --edition 2021 --crate-type lib --emit=obj -o .sweep/tmp/rc.o .sweep/tmp/rc.rs 2>/dev/null; then printf 'ACCEPT  %-22s [%s]\n' "$2" "$1"; else printf 'REJECT  %-22s [%s]\n' "$2" "$1"; fi; }
rc "y: i8" "y == -128"
rc "y: i8" "y == -(128)"
rc "y: i8" "y == -128i8"
rc "y: i8" "y == -(-128i8)"
rc "y: i8" "y == -128i16"
rc "y: i8" "y == -(128 - 63)"
rc "y: i8" "y == -(0 - 128)"
rc "y: i8" "y == -(-128)"
rc "y: i8" "y == -129"
rc "x: u8" "x == -(200)"
rc "x: u8" "x == -(200 - 100)"

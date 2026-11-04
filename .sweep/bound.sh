export PATH=/workspace/.rust/cargo/bin:$PATH
export RUSTUP_HOME=/workspace/.rust/rustup
export CARGO_HOME=/workspace/.rust/cargo
unset RUSTC
R=$(rustup which --toolchain nightly rustc)
rc() { printf '#![allow(dead_code,unused)]\nfn s0(%s)->u8{ let _ = %s; 0 }\n' "$1" "$2" > .sweep/tmp/rc.rs; if $R --edition 2021 --crate-type lib --emit=obj -o .sweep/tmp/rc.o .sweep/tmp/rc.rs 2>/dev/null; then echo "ACCEPT :: $2   [%s]" "$1"; else echo "REJECT :: $2   [%s]" "$1"; fi; }
rc "y: i8"  "y <= (!127)"
rc "y: i8"  "y <= (!128)"
rc "y: i8"  "y <= (!255)"
rc "x: u8"  "x <= (!127)"
rc "x: u8"  "x <= (!128)"
rc "x: u8"  "x <= (!255)"
rc "x: u8"  "x <= (!256)"
rc "b: i16" "b <= (!128)"
rc "b: i16" "b <= (!255)"
rc "a: u16" "a <= (!255)"
rc "a: u16" "a <= (!256)"
rc "y: i8"  "y <= (!(-1))"

export PATH=/workspace/.rust/cargo/bin:$PATH
export RUSTUP_HOME=/workspace/.rust/rustup
export CARGO_HOME=/workspace/.rust/cargo
unset RUSTC
R=$(rustup which --toolchain nightly rustc)
rc() { printf '#![allow(dead_code,unused)]\nfn s0(%s)->u8{ let _ = %s; 0 }\n' "$1" "$2" > .sweep/tmp/rc.rs; if $R --edition 2021 --crate-type lib --emit=obj -o .sweep/tmp/rc.o .sweep/tmp/rc.rs 2>/dev/null; then printf 'ACCEPT  %-28s [%s]\n' "$2" "$1"; else printf 'REJECT  %-28s [%s]\n' "$2" "$1"; fi; }
echo "--- unsigned u8: does & mask away the out-of-range literal? ---"
rc "x: u8" "x == (200 & 200)"
rc "x: u8" "x == (200 & 0)"
rc "x: u8" "x == (200 & 1)"
rc "x: u8" "x == (100 + 100)"
rc "x: u8" "x == ((100 + 100) & 0)"
rc "x: u8" "x == (5 * 30)"
rc "x: u8" "x == (200 | 0)"
rc "x: u8" "x == (200 ^ 0)"
echo "--- signed i8 ---"
rc "y: i8" "y == (200 & 200)"
rc "y: i8" "y == (200 & 0)"
rc "y: i8" "y == (128 & 0)"
rc "y: i8" "y == (100 + 100)"
rc "y: i8" "y == ((100 + 100) & 0)"
rc "y: i8" "y == (-128 & -128)"
echo "--- which literal / which intermediate is blamed? ---"
rc "x: u8" "x == (0 + 200)"
rc "x: u8" "x == (200 + 0)"
rc "x: u8" "x == ((100 + 100) & 255)"
rc "x: u8" "x == (255 + 255 - 255)"

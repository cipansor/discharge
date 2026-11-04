export PATH=/workspace/.rust/cargo/bin:$PATH
export RUSTUP_HOME=/workspace/.rust/rustup
export CARGO_HOME=/workspace/.rust/cargo
unset RUSTC
R=$(rustup which --toolchain nightly rustc)
export DISCHARGE_RUSTC=$R
BIN=$PWD/target/release/examples/mir_coverage
probe() { printf '#![allow(dead_code)]\n/// requires: true\n/// ensures: %s\npub fn s0(%s)->u8{0}\n' "$2" "$1" > .sweep/tmp/one.rs; printf '%-24s :: %s\n' "$2" "$(timeout 25 $BIN .sweep/tmp/one.rs 2>&1 | grep -m1 ^s0 | sed 's/^s0 *//' | cut -c1-26)"; }
rcheck() { printf '#![allow(dead_code,unused)]\nfn s0(%s)->u8{ let _ = %s; 0 }\n' "$1" "$2" > .sweep/tmp/rc.rs; if $R --edition 2021 --crate-type lib --emit=obj -o .sweep/tmp/rc.o .sweep/tmp/rc.rs 2>.sweep/tmp/err.txt; then echo "   rustc=ACCEPT"; else echo "   rustc=REJECT: $(grep -m1 '^error' .sweep/tmp/err.txt)"; fi; }
echo "=== !128 vs i8 ==="; probe "y: i8" "y <= (!128)"; rcheck "y: i8" "y <= (!128)"
echo "=== !127 vs i8 ==="; probe "y: i8" "y <= (!127)"; rcheck "y: i8" "y <= (!127)"
echo "=== !0 vs i8 ==="; probe "y: i8" "y <= (!0)"; rcheck "y: i8" "y <= (!0)"
echo "=== !129 vs i8 ==="; probe "y: i8" "y <= (!129)"; rcheck "y: i8" "y <= (!129)"
echo "=== !200 vs i8 ==="; probe "y: i8" "y <= (!200)"; rcheck "y: i8" "y <= (!200)"
echo "=== !128 vs u8 ==="; probe "x: u8" "x <= (!128)"; rcheck "x: u8" "x <= (!128)"
echo "=== !255 vs i8 ==="; probe "y: i8" "y <= (!255)"; rcheck "y: i8" "y <= (!255)"
echo "=== !128 vs i16 ==="; probe "b: i16" "b <= (!128)"; rcheck "b: i16" "b <= (!128)"

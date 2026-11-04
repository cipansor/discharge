export DISCHARGE_RUSTC=$(rustup which --toolchain nightly rustc)
BIN=$PWD/target/release/examples/mir_coverage
probe() { printf '#![allow(dead_code)]\n/// requires: true\n/// ensures: %s\npub fn s0(%s)->u8{0}\n' "$2" "$1" > .sweep/tmp/one.rs; printf '%-24s :: %s\n' "$2" "$(timeout 25 $BIN .sweep/tmp/one.rs 2>&1 | grep -m1 ^s0 | sed 's/^s0 *//' | cut -c1-22)"; }
probe "y: i8" "y <= (!128)"
probe "y: i8" "y <= (!!128)"
probe "y: i8" "y <= (!!127)"
probe "y: i8" "y <= (!127)"
probe "x: u8" "x <= (!128)"
probe "b: i16" "b <= (!128)"
probe "x: u8" "x <= (!255)"
probe "y: i8" "y <= (!(64 + 64))"
probe "x: u8" "(x as u16 + !0) == 255"
probe "x: u8" "(!0 + 1) < 1u8"
probe "x: u8" "x == (!0 & 1)"
probe "x: u8" "x / !0 == 0"
probe "x: u8" "!0 == 255"

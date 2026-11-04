export PATH=/workspace/.rust/cargo/bin:$PATH
export RUSTUP_HOME=/workspace/.rust/rustup
export CARGO_HOME=/workspace/.rust/cargo
unset RUSTC
export DISCHARGE_RUSTC=$(rustup which --toolchain nightly rustc)
BIN=$PWD/target/release/examples/mir_coverage
probe() { printf '#![allow(dead_code)]\n/// requires: true\n/// ensures: %s\npub fn s0(%s)->u8{0}\n' "$2" "$1" > .sweep/tmp/one.rs; timeout 25 $BIN .sweep/tmp/one.rs 2>&1 | grep -m1 ^s0 | sed 's/^s0 *//' | cut -c1-44; }
echo "--- accepted forms? ---"
probe "x: u8" "(x & 15) < 16"
probe "x: u8" "(x | 8) < 16"
probe "x: u8" "(x ^ 8) == 8"
probe "x: u8" "(x >> 4) < 16"
probe "x: u8" "(x << 4) < 256"
probe "x: u8" "((x & 15) | 16) < 32"
probe "x: u8" "(x & 15) != 15"
probe "x: i8" "(x >> 4) < 16"
probe "x: u8" "(15 & x) < 16"
probe "x: u8" "x < 16 || x >= 240"
probe "x: u8" "x < 16 && x > 8"
probe "x: u8" "x % 16 < 16"
probe "x: u8" "x / 16 < 16"

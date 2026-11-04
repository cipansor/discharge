export PATH=/workspace/.rust/cargo/bin:$PATH
export RUSTUP_HOME=/workspace/.rust/rustup
export CARGO_HOME=/workspace/.rust/cargo
unset RUSTC
export DISCHARGE_RUSTC=$(rustup which --toolchain nightly rustc)
BIN=$PWD/target/release/examples/mir_coverage
probe() { printf '#![allow(dead_code)]\n/// requires: true\n/// ensures: %s\npub fn s0(%s)->u8{0}\n' "$2" "$1" > .sweep/tmp/one.rs; printf '%-26s :: %s\n' "$2" "$(timeout 25 $BIN .sweep/tmp/one.rs 2>&1 | grep -m1 ^s0 | sed 's/^s0 *//' | cut -c1-30)"; }
echo "--- plain literal 128 vs i8 (should be refused) ---"; probe "y: i8" "y <= 128"
echo "--- plain 129 vs i8 ---"; probe "y: i8" "y <= 129"
echo "--- complement 128 vs i8 ---"; probe "y: i8" "y <= (!128)"
echo "--- complement of a fold 128 vs i8 ---"; probe "y: i8" "y <= (!(64 + 64))"
echo "--- complement 128 via hex ---"; probe "y: i8" "y <= (!0x80)"
echo "--- complement 128 in equality ---"; probe "y: i8" "(!128) == y"
echo "--- double complement 128 ---"; probe "y: i8" "y <= (!!128)"
echo "--- complement 127 vs i8 (valid) ---"; probe "y: i8" "y <= (!127)"
echo "--- shift of 128 vs i8 ---"; probe "y: i8" "y <= (128 >> 0)"
echo "--- complement 128 vs i16 (valid) ---"; probe "b: i16" "b <= (!128)"

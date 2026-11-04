export PATH=/workspace/.rust/cargo/bin:$PATH
export RUSTUP_HOME=/workspace/.rust/rustup
export CARGO_HOME=/workspace/.rust/cargo
unset RUSTC
export DISCHARGE_RUSTC=$(rustup which --toolchain nightly rustc)
BIN=$PWD/target/release/examples/mir_coverage
probe() { printf '#![allow(dead_code)]\n/// requires: true\n/// ensures: %s\npub fn s0(%s)->u8{0}\n' "$2" "$1" > .sweep/tmp/one.rs; printf '%-30s :: %s\n' "$2" "$(timeout 25 $BIN .sweep/tmp/one.rs 2>&1 | grep -m1 ^s0 | sed 's/^s0 *//' | cut -c1-40)"; }
probe "x: u8" "x.count_ones() == 0"
probe "x: u8" "x.count_zeros() == 0"
probe "x: u8" "x.leading_zeros() == 0"
probe "x: u8" "x.trailing_zeros() == 0"
probe "x: u8" "x.is_power_of_two()"
probe "x: u8" "x.rotate_left(3) == 0"
probe "x: u8" "x.rotate_right(3) == 0"
probe "x: u8" "x.next_multiple_of(4) == 0"
probe "x: u8" "x.div_ceil(4) == 0"
probe "x: u8, y: i8" "x.wrapping_add_signed(y) == 0"
probe "x: u8" "x.pow(3) == 0"
probe "x: u8" "x.wrapping_pow(3) == 0"
probe "x: u8" "x.checked_pow(3) == 0"

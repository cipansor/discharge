export PATH=/workspace/.rust/cargo/bin:$PATH
export RUSTUP_HOME=/workspace/.rust/rustup
export CARGO_HOME=/workspace/.rust/cargo
unset RUSTC
export DISCHARGE_RUSTC=$(rustup which --toolchain nightly rustc)
BIN=$PWD/target/release/examples/mir_coverage
# reader verdict
probe() { printf '#![allow(dead_code)]\n/// requires: true\n/// ensures: %s\npub fn s0(%s)->u8{0}\n' "$2" "$1" > .sweep/tmp/one.rs; printf '%-34s :: %s\n' "$2" "$(timeout 25 $BIN .sweep/tmp/one.rs 2>&1 | grep -m1 ^s0 | sed 's/^s0 *//' | cut -c1-30)"; }
# rustc accept/reject for the same expression in a real fn body
rcheck() { printf 'fn s0(%s)->u8{ let _ = %s; 0 }\n' "$1" "$2" > .sweep/tmp/rc.rs; if $DISCHARGE_RUSTC --edition 2021 --crate-type lib -o /dev/null .sweep/tmp/rc.rs 2>/dev/null; then echo "rustc=ACCEPT"; else echo "rustc=REJECT"; fi; }
echo "--- unary neg of untyped constant vs narrow partner ---"
probe "y: i8" "(-255) < y"; rcheck "y: i8" "(-255) < y"
probe "y: i8" "(-200) <= y"; rcheck "y: i8" "(-200) <= y"
probe "y: i8" "(-128) == y"; rcheck "y: i8" "(-128) == y"
probe "y: i8" "(-129) < y"; rcheck "y: i8" "(-129) < y"
echo "--- bitwise not of untyped constant ---"
probe "x: u8" "(!255) < x"; rcheck "x: u8" "(!255) < x"
probe "x: u8" "(!1) < x"; rcheck "x: u8" "(!1) < x"
echo "--- fold results vs narrow partner ---"
probe "x: u8" "(255 + 1) <= x"; rcheck "x: u8" "(255 + 1) <= x"
probe "x: u8" "(200 + 100) <= x"; rcheck "x: u8" "(200 + 100) <= x"
probe "y: i8" "(-100 - 100) <= y"; rcheck "y: i8" "(-100 - 100) <= y"
probe "x: u8" "(128 * 2) <= x"; rcheck "x: u8" "(128 * 2) <= x"

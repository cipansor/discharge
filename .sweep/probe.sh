BIN=$PWD/target/release/examples/mir_coverage
probe() { printf '#![allow(dead_code)]\n/// requires: true\n/// ensures: %s\npub fn s0(%s)->u8{0}\n' "$2" "$1" > .sweep/tmp/one.rs; timeout 25 $BIN .sweep/tmp/one.rs 2>&1 | grep -m1 ^s0 | sed 's/^s0 *//'; }
echo "--- symbolic divisor (both operands vars) ---"
probe "x: u8, y: u8"   "(x / y) == 0"
probe "a: u16, b: u16" "(a / b) == 0"
probe "c: u32, d: u32" "(c / d) == 0"
echo "--- symbolic remainder ---"
probe "x: u8, y: u8"   "(x % y) == 0"
probe "a: u16, b: u16" "(a % b) == 0"
probe "c: u32, d: u32" "(c % d) == 0"
echo "--- wrapping_pow widths ---"
probe "x: u8, e: u32"  "(x.wrapping_pow(e)) == 0"
probe "a: u16, e: u32" "(a.wrapping_pow(e)) == 0"
probe "c: u32, e: u32" "(c.wrapping_pow(e)) == 0"

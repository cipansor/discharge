export PATH=/workspace/.rust/cargo/bin:$PATH
export RUSTUP_HOME=/workspace/.rust/rustup
export CARGO_HOME=/workspace/.rust/cargo
unset RUSTC
R=$(rustup which --toolchain nightly rustc)
rcheck() { printf '#![allow(dead_code,unused)]\nfn s0(%s)->u8{ let _ = %s; 0 }\n' "$1" "$2" > .sweep/tmp/rc.rs; if $R --edition 2021 --crate-type lib --emit=obj -o .sweep/tmp/rc.o .sweep/tmp/rc.rs 2>.sweep/tmp/err.txt; then echo "ACCEPT  :: $2"; else echo "REJECT  :: $2"; grep -m1 "^error" .sweep/tmp/err.txt | sed 's/^/         /'; fi; }
rcheck "x: u8" "(255 >> 8) <= x"
rcheck "x: u8" "(255 >> 7) <= x"
rcheck "y: i8" "(255 >> 1) >= y"
rcheck "x: u8" "(!255) < x"
rcheck "x: u8" "(255 + 1) <= x"
rcheck "x: u8" "(128 * 2) <= x"
rcheck "y: i8" "(-100 - 100) <= y"
rcheck "y: i8" "(-128) == y"

export PATH=/workspace/.rust/cargo/bin:$PATH
export RUSTUP_HOME=/workspace/.rust/rustup
export CARGO_HOME=/workspace/.rust/cargo
unset RUSTC
R=$(rustup which --toolchain nightly rustc)
rcheck() { printf '#![allow(dead_code,unused)]\nfn s0(%s)->u8{ let _ = %s; 0 }\n' "$1" "$2" > .sweep/tmp/rc.rs; if $R --edition 2021 --crate-type lib --emit=metadata -o .sweep/tmp/rc.rmeta .sweep/tmp/rc.rs 2>.sweep/tmp/err.txt; then echo "ACCEPT  :: $2"; else echo "REJECT  :: $2"; grep -m1 "^error" .sweep/tmp/err.txt | sed 's/^/         /'; fi; }
rcheck "y: i8" "y == 0"
rcheck "y: i8" "(-128) == y"
rcheck "x: u8" "(!255) < x"
rcheck "x: u8" "(!1) < x"
rcheck "y: i8" "(-255) < y"
rcheck "x: u8" "(255 >> 8) <= x"

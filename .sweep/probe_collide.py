import subprocess, os
BIN=os.environ["SWEEP_BIN"]
SHAPES=[
 ("x == 128", "x: u8"),
 ("x == -128 && x == 128", "x: u8"),
 ("x == 128 && y == 0", "x: u8, y: i8"),
 ("y == -128 && x == 128", "x: u8, y: i8"),
 ("y == -128i8 && x == 128", "x: u8, y: i8"),
 ("x == !128 && x == 127", "x: u8"),
 ("x == !128 && y == 127", "x: u8, y: i8"),
 ("x == 127 && y == 127", "x: u8, y: i8"),
 ("y == 127 && x == !128", "x: u8, y: i8"),
 ("x == 128 && y == 128", "x: u8, y: i8"),
 ("x == 0 && y == 0", "x: u8, y: i8"),
 ("x == (!128) && x == 127", "x: u8"),
 ("x == 255 && y == 0", "x: u8, y: i8"),
 ("y == -128 && y == 127", "y: i8"),
 ("x == !0 && x == 255", "x: u8"),
]
for i,(expr,sig) in enumerate(SHAPES):
    src="#![allow(dead_code)]\n/// requires: true\n/// ensures: %s\npub fn s0(%s)->u8{0}\n"%(expr,sig)
    p=".sweep/tmp/pc%d.rs"%i
    open(p,"w").write(src)
    out=subprocess.run([BIN,p],capture_output=True,text=True).stdout
    line=[l for l in out.splitlines() if l.startswith("s0")]
    st="?"
    if line:
        l=line[0]
        st="verified" if "verified" in l else ("FAILED" if "FAILED" in l else "skipped")
    print("%-38s %-18s -> %s"%(expr,sig,st))

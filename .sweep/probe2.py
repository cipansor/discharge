import subprocess, os
BIN=os.environ["SWEEP_BIN"]
CASES=[
 ("x == !128 && y == 127","x: u8, y: i8"),
 ("y == 127 && x == !128","x: u8, y: i8"),
 ("y == -128 && x == 128","x: u8, y: i8"),
 ("x == 128 && y == -128","x: u8, y: i8"),
 ("x == !127 && x == 128","x: u8"),
 ("x == !(128-63) && x == 190","x: u8"),
 ("x == !0 && x == 255","x: u8"),
]
for i,(e,s) in enumerate(CASES):
    p=".sweep/tmp/r2_%d.rs"%i
    open(p,"w").write("#![allow(dead_code)]\n/// requires: true\n/// ensures: %s\npub fn s0(%s)->u8{0}\n"%(e,s))
    out=subprocess.run([BIN,p],capture_output=True,text=True).stdout
    msg=""
    for l in out.splitlines():
        if l.startswith("s0"):
            msg=l.strip()
    print("%-32s %-14s | %s"%(e,s,msg[:110]))

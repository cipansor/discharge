import subprocess, os
BIN=os.environ["SWEEP_BIN"]; R=os.environ["DISCHARGE_RUSTC"]
def rdr(expr,sig):
    src="#![allow(dead_code)]\n/// requires: true\n/// ensures: %s\npub fn s0(%s)->u8{0}\n"%(expr,sig)
    p=".sweep/tmp/pp.rs"; open(p,"w").write(src)
    out=subprocess.run([BIN,p],capture_output=True,text=True).stdout
    for l in out.splitlines():
        if l.startswith("s0"):
            return "verified" if "verified" in l else ("FAILED" if "FAILED" in l else "skipped")
    return "?"
def rc(expr,sig):
    src="#![allow(dead_code,unused)]\nfn s0(%s){ let _ = %s; }\n"%(sig,expr)
    p=".sweep/tmp/ppr.rs"; open(p,"w").write(src)
    return "ACCEPT" if subprocess.run([R,"--edition","2021","--crate-type","lib","--emit=obj","-o",".sweep/tmp/ppr.o",p],capture_output=True,text=True).returncode==0 else "REJECT"
CASES=[
 ("y == 0","y: i8"),
 ("x == (200 - 200) && y == 0","x: u8, y: i8"),
 ("x == (100 & 128) && y == 0","x: u8, y: i8"),
 ("x == (!0 & 1) && y == 1","x: u8, y: i8"),
 ("x == (2 & 128) && y == 0","x: u8, y: i8"),
 ("x == !128 && y == 127","x: u8, y: i8"),
 ("x == (128 - 63) && y == 65","x: u8, y: i8"),
 ("x == (!128 & 255) && y == 127","x: u8, y: i8"),
]
for e,s in CASES:
    print("%-42s %-16s rustc=%-7s reader=%s"%(e,s,rc(e,s),rdr(e,s)))

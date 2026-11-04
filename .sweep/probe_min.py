import subprocess, os
BIN=os.environ["SWEEP_BIN"]; R=os.environ["DISCHARGE_RUSTC"]
def rdr(expr,sig):
    src="#![allow(dead_code)]\n/// requires: true\n/// ensures: %s\npub fn s0(%s)->u8{0}\n"%(expr,sig)
    p=".sweep/tmp/pm.rs"; open(p,"w").write(src)
    out=subprocess.run([BIN,p],capture_output=True,text=True).stdout
    for l in out.splitlines():
        if l.startswith("s0"):
            return "verified" if "verified" in l else ("FAILED" if "FAILED" in l else "skipped")
    return "?"
def rc(expr,sig):
    src="#![allow(dead_code,unused)]\nfn s0(%s){ let _ = %s; }\n"%(sig,expr)
    p=".sweep/tmp/pmr.rs"; open(p,"w").write(src)
    r=subprocess.run([R,"--edition","2021","--crate-type","lib","--emit=obj","-o",".sweep/tmp/pmr.o",p],capture_output=True,text=True)
    return "ACCEPT" if r.returncode==0 else "REJECT"
CASES=[
 ("y == 128i8","y: i8"),("y == -128i8","y: i8"),("y == 128","y: i8"),("y == -128","y: i8"),
 ("y == i8::MIN","y: i8"),("y == -i8::MIN","y: i8"),("y == -(128i8)","y: i8"),("y == -(-128i8)","y: i8"),
 ("y == -(-128)","y: i8"),("b == 32768i16","b: i16"),("b == -32768i16","b: i16"),
 ("b == 128i16","b: i16"),("b == -128i16","b: i16"),("x == 255","x: u8"),("x == 128","x: u8"),
 ("y == -(127i8)","y: i8"),("y == 127i8","y: i8"),
]
for e,s in CASES:
    print("%-22s %-10s rustc=%-7s reader=%s"%(e,s,rc(e,s),rdr(e,s)))

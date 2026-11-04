import subprocess, os
BIN=os.environ["SWEEP_BIN"]; R=os.environ["DISCHARGE_RUSTC"]
def rdr(e,s):
    p=".sweep/tmp/p3.rs"; open(p,"w").write("#![allow(dead_code)]\n/// requires: true\n/// ensures: %s\npub fn s0(%s)->u8{0}\n"%(e,s))
    out=subprocess.run([BIN,p],capture_output=True,text=True).stdout
    for l in out.splitlines():
        if l.startswith("s0"): return "verified" if "verified" in l else ("FAILED" if "FAILED" in l else "skipped")
    return "?"
def rc(e,s):
    p=".sweep/tmp/p3r.rs"; open(p,"w").write("#![allow(dead_code,unused)]\nfn s0(%s){ let _ = %s; }\n"%(s,e))
    return "ACCEPT" if subprocess.run([R,"--edition","2021","--crate-type","lib","--emit=obj","-o",".sweep/tmp/p3r.o",p],capture_output=True,text=True).returncode==0 else "REJECT"
for e,s in [("y == !128i8","y: i8"),("y == !127i8","y: i8"),("x == !255u8","x: u8"),("y == -(!128i8)","y: i8")]:
    print("%-22s %-8s rustc=%-7s reader=%s"%(e,s,rc(e,s),rdr(e,s)))

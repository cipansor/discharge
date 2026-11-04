import os, subprocess, json
BIN=os.environ["SWEEP_BIN"]; RUSTC=os.environ["DISCHARGE_RUSTC"]
CASES=[
 ("x >> (250 + 10)", "u8"), ("x >> (200 + 100)", "u8"), ("x >> (100 * 3)", "u8"),
 ("x >> (2 << 7)", "u8"), ("x >> (1 << 3)", "u8"), ("x >> (1 + 1)", "u8"),
 ("x >> (2 * 2)", "u8"), ("x >> (8 - 1)", "u8"), ("x >> (16 / 2)", "u8"),
 ("x >> (250 + 10)", "u16"), ("x >> (2 << 7)", "u16"), ("x >> (1 << 3)", "u16"),
 ("x >> 200", "u8"), ("x >> 7", "u8"), ("x >> 8", "u8"),
 ("x >> (2 << 7)", "u64"), ("x >> (1 << 5)", "u64"), ("x >> (1 << 40)", "u64"),
]
def rustc_ok(expr, ty):
    src="#![allow(dead_code,unused_comparisons)]\nfn _c(x: %s){ let _ = %s; }\n"%(ty,expr)
    p=subprocess.run([RUSTC,"--edition","2021","--crate-type","lib","-o",".sweep/tmp/o.rlib","-"],input=src,capture_output=True,text=True)
    return p.returncode==0
def reader(expr, ty):
    src="#![allow(dead_code)]\n/// requires: true\n/// ensures: (%s) == 0\npub fn s0(x: %s)->u8{0}\n"%(expr,ty)
    open(".sweep/tmp/b.rs","w").write(src)
    p=subprocess.run([BIN,".sweep/tmp/b.rs"],capture_output=True,text=True)
    for line in p.stdout.splitlines():
        if line.startswith("s0"):
            return "verified" if "verified" in line else ("failed" if "FAILED" in line else "skipped")
    return "skipped"
for e,ty in CASES:
    ro=rustc_ok(e,ty); rv=reader(e,ty)
    flag=""
    if (not ro) and rv in ("verified","failed"): flag="  <-- WRONG VERDICT"
    print("%-20s %-4s rustc=%-7s reader=%-9s%s"%(e,ty,"ACCEPT" if ro else "REJECT",rv,flag))

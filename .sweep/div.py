import subprocess, os, time
BIN=os.path.abspath("target/release/examples/mir_coverage")
def t(expr, sig, to=12):
    src="#![allow(dead_code)]\n/// requires: true\n/// ensures: %s\npub fn s0(%s)->u8{x}\n"%(expr,sig)
    open(".sweep/tmp/one.rs","w").write(src)
    s=time.time()
    try:
        subprocess.run([BIN,".sweep/tmp/one.rs"],capture_output=True,text=True,timeout=to)
        return time.time()-s
    except subprocess.TimeoutExpired:
        return None
S8="x: u8, y: i8"
S16="x: u8, y: i8, a: u16, b: i16"
S32="x: u8, y: i8, a: u16, b: i16, c: u32, d: i32"
S64="x: u8, y: i8, a: u16, b: i16, c: u32, d: i32, e: u64, f: i64"
for name,sig,p in [("u8",S8,"x"),("u16",S16,"a"),("u32",S32,"c"),("u64",S64,"e")]:
    row=[]
    for k in [2,3,4,5,7,8,9,15,16,255]:
        d=t("(%s / %d) == 0"%(p,k), sig)
        row.append("%d:%s"%(k, "TIMEOUT" if d is None else "%.1f"%d))
    print("%-4s %s"%(name," ".join(row)))

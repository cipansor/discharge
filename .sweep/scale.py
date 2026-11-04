import subprocess, os, time
BIN=os.path.abspath("target/release/examples/mir_coverage")
SIG="x: u8, y: i8, a: u16, b: i16, c: u32, d: i32, e: u64, f: i64"
CONSTS=["255","!0","1","2","128","-1","-128","200","(200 + 100)","(!0 + 1)",
        "(255 >> 1)","(255 / 2)","(255 % 2)","(!0 >> 1)","(128 << 1)","(1 << 7)"]
OPS=["==","!=","<","<=",">",">="]
shapes=[]
for p in ["e","f"]:
    for c in CONSTS:
        for op in OPS:
            shapes.append("(%s) %s %s"%(c,op,p))
def run(n):
    src="#![allow(dead_code)]\n"
    for i,e in enumerate(shapes[:n]):
        src+="/// requires: true\n/// ensures: %s\npub fn s%d(%s)->u8{x}\n"%(e,i,SIG)
    open(".sweep/tmp/one.rs","w").write(src)
    t=time.time()
    try:
        subprocess.run([BIN,".sweep/tmp/one.rs"],capture_output=True,text=True,timeout=400)
        return time.time()-t
    except subprocess.TimeoutExpired:
        return None
for n in [6,12,24,48,96,168]:
    d=run(n)
    print("n=%-4d %s"%(n, ("%.1fs"%d) if d else ">400s"))

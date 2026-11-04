import subprocess, os, re
BIN=os.environ["SWEEP_BIN"]
CONSTS=["255","!0","1","2","128","-1","-128","200","(200 + 100)","(!0 + 1)",
        "(255 >> 1)","(255 / 2)","(255 % 2)","(!0 >> 1)","(128 << 1)","(1 << 7)"]
OPS=["==","!=","<","<=",">",">="]
# Rust types an untyped integer literal (and a fold of them) as i32 when no typed
# operand fixes it. Evaluate each constant at i32.
def i32(expr):
    e=expr.replace("!0","-1").replace("/","//")
    # Rust '/' truncates toward zero; Python '//' floors. Both agree for non-negatives;
    # for negatives adjust.
    try:
        v=eval(e, {"__builtins__":{}}, {})
    except Exception:
        return None
    # emulate i32 wrap
    v &= 0xFFFFFFFF
    if v >= 1<<31: v -= 1<<32
    return v
def truth(c1,op,c2):
    a=i32(c1); b=i32(c2)
    if a is None or b is None: return None
    return {"==":a==b,"!=":a!=b,"<":a<b,"<=":a<=b,">":a>b,">=":a>=b}[op]
def reader(expr):
    src="#![allow(dead_code)]\n/// requires: true\n/// ensures: %s\npub fn s0(x: u8, y: i8)->u8{x}\n"%expr
    open(".sweep/tmp/one.rs","w").write(src)
    try:
        p=subprocess.run([BIN,".sweep/tmp/one.rs"],capture_output=True,text=True,timeout=20)
    except subprocess.TimeoutExpired:
        return "hang"
    for line in p.stdout.splitlines():
        if line.startswith("s0"):
            return "verified" if "verified" in line else ("failed" if "FAILED" in line else "skipped")
    return "skipped"
unsound=[]; miss=[]; checked=0; skipped=0; tot=0
for c1 in CONSTS:
    for c2 in CONSTS:
        for op in OPS:
            tot+=1
            e="(%s) %s (%s)"%(c1,op,c2)
            v=reader(e)
            t=truth(c1,op,c2)
            if v=="hang": unsound.append((e,"HANG")); continue
            if v=="skipped":
                skipped+=1; continue
            want="verified" if t else "failed"
            checked+=1
            if v!=want: unsound.append((e,"reader=%s i32-truth=%s"%(v,want)))
print("total",tot,"decided-checked",checked,"refused",skipped,"SOUNDNESS",len(unsound))
for e,m in unsound[:40]: print("  ",e,"::",m)

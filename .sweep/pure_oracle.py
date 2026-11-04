import subprocess, os, re
BIN=os.environ["SWEEP_BIN"]
CONSTS=["255","!0","1","2","128","-1","-128","200","(200 + 100)","(!0 + 1)",
        "(255 >> 1)","(255 / 2)","(255 % 2)","(!0 >> 1)","(128 << 1)","(1 << 7)"]
OPS=["==","!=","<","<=",">",">="]

def eval_at(expr, w, signed):
    # Evaluate a constant expression at width w, in Rust semantics.
    # Wrap each literal to w bits; treat as signed or unsigned per flag.
    mask=(1<<w)-1
    e=expr
    # replace integer literals with wrapped values
    def repl(m):
        v=int(m.group(0))
        return str(v & mask)
    e=re.sub(r'\d+', repl, e)
    # !0 -> mask (must come after digit wrap so '0' inside is not double-wrapped)
    e=e.replace("!0", str(mask))
    # Rust '/' on unsigned is truncating == Python '//' for non-negatives
    e=e.replace("/", "//")
    # Python eval with Rust-like ops; >> on unsigned is fine, / and % need care
    # implement / and % as unsigned truncating for now
    try:
        val=eval(e, {"__builtins__":{}}, {})
    except Exception as ex:
        return None
    val &= mask
    if signed and (val >> (w-1)) & 1:
        val -= (1<<w)
    return val

def cmp_at(c1, op, c2, w, signed):
    a=eval_at(c1,w,signed); b=eval_at(c2,w,signed)
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

bad=[]; checked=0; skipped=0; total=0
for c1 in CONSTS:
    for c2 in CONSTS:
        for op in OPS:
            total+=1
            e="(%s) %s (%s)"%(c1,op,c2)
            v=reader(e)
            if v=="hang": bad.append((e,"HANG")); continue
            if v=="skipped": skipped+=1; continue
            # width-invariant truth across 8/16/32/64, signed and unsigned
            res=set()
            for w in (8,16,32,64):
                for s in (False,True):
                    r=cmp_at(c1,op,c2,w,s)
                    if r is not None: res.add(r)
            if len(res)!=1:
                # not width-invariant: the reader should have refused
                bad.append((e,"decided %s but truth varies: %s"%(v,res)))
                continue
            truth=res.pop()
            want="verified" if truth else "failed"
            checked+=1
            if v!=want:
                bad.append((e,"reader=%s truth=%s"%(v,want)))
print("total",total,"checked",checked,"skipped",skipped,"MISMATCHES",len(bad))
for e,m in bad[:60]: print("  ",e,"::",m)

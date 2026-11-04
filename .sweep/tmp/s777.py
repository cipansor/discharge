import subprocess, os, random
BIN=os.environ["SWEEP_BIN"]; R=os.environ["DISCHARGE_RUSTC"]
# --- expression tree ---
# ('c',k) literal, ('u',op,e) unary (- or !), ('b',op,l,r) binary
def ev(t,w,signed):
    M=(1<<w)-1
    def sgn(v): return v-(1<<w) if (signed and (v>>(w-1))&1) else v
    k=t[0]
    if k=='c': return (t[1] & M, False)
    if k=='u':
        v,wr=ev(t[2],w,signed)
        if t[1]=='-': return ((-v) & M, wr or v!=0)
        return ((~v) & M, wr)
    op=t[1]; l,wl=ev(t[2],w,signed); r,wr=ev(t[3],w,signed)
    ls,rs=sgn(l),sgn(r)
    if op=='&': return (l&r, wl or wr)
    if op=='|': return (l|r, wl or wr)
    if op=='^': return (l^r, wl or wr)
    if op=='+':
        ex=ls+rs; return (ex & M, wl or wr or not(-(1<<(w-1))<=ex<=(1<<(w-1))-1))
    if op=='-':
        ex=ls-rs; return (ex & M, wl or wr or not(-(1<<(w-1))<=ex<=(1<<(w-1))-1))
    if op=='*':
        ex=ls*rs; return (ex & M, wl or wr or not(-(1<<(w-1))<=ex<=(1<<(w-1))-1))
    if op=='>>':
        amt=rs & (w-1) if False else rs
        if not (0<=rs<w): return (0, True)   # would be rejected
        return ((ls>>rs)&M, wl or wr)
    if op=='<<':
        if not (0<=rs<w): return (0, True)
        ex=ls<<rs; return (ex & M, wl or wr or not(-(1<<(w-1))<=ex<=(1<<(w-1))-1))
    raise Exception(op)
def rd(t):
    k=t[0]
    if k=='c': return str(t[1])
    if k=='u': return "(%s%s)"%(t[1],rd(t[2]))
    return "(%s %s %s)"%(rd(t[2]),t[1],rd(t[3]))
def rustc_ok(expr, sig, form):
    body = "let _ = %s;"%form
    src="#![allow(dead_code,unused)]\nfn s0(%s)->u8{ %s 0 }\n"%(sig,body)
    open(".sweep/tmp/rc.rs","w").write(src)
    p=subprocess.run([R,"--edition","2021","--crate-type","lib","--emit=obj",
                      "-o",".sweep/tmp/rc.o",".sweep/tmp/rc.rs"],capture_output=True,text=True)
    return p.returncode==0
def reader(expr, sig, form):
    src="#![allow(dead_code)]\n/// requires: true\n/// ensures: %s\npub fn s0(%s)->u8{0}\n"%(form,sig)
    open(".sweep/tmp/one.rs","w").write(src)
    try:
        p=subprocess.run([BIN,".sweep/tmp/one.rs"],capture_output=True,text=True,timeout=20)
    except subprocess.TimeoutExpired: return "hang"
    for line in p.stdout.splitlines():
        if line.startswith("s0"):
            return "verified" if "verified" in line else ("failed" if "FAILED" in line else "skipped")
    return "skipped"
random.seed(777)
LITS=[0,1,2,3,5,7,8,15,16,31,63,64,100,127,128,129,200,240,254,255]
BIN_OPS=['+','-','*','&','|','^','>>','<<']
def rand_expr(d):
    r=random.random()
    if d==0 or r<0.45:
        return ('c',random.choice(LITS))
    if r<0.6:
        return ('u',random.choice(['-','!']),rand_expr(d-1))
    return ('b',random.choice(BIN_OPS),rand_expr(d-1),rand_expr(d-1))
TYPES=[("x: u8",8,False),("y: i8",8,True),("a: u16",16,False),("b: i16",16,True)]
CMPS=['==','<=','<']
unsound=[]; discrep=[]; ok=0; skipped=0; tot=0; wrapped_accept=[]
for it in range(1200):
    e=rand_expr(2); estr=rd(e)
    sig,w,signed=random.choice(TYPES)
    var=sig.split(":")[0].strip()
    op=random.choice(CMPS)
    left = random.random()<0.5
    form = "(%s) %s %s"%(estr,op,var) if left else "%s %s (%s)"%(var,op,estr)
    tot+=1
    rok=rustc_ok(estr,sig,form)
    rv=reader(estr,sig,form)
    if rv=="hang": unsound.append((sig,form,"HANG")); continue
    if not rok:
        # rustc rejects: the reader must refuse (skip)
        if rv!="skipped": discrep.append((sig,form,"rustc REJECT but reader=%s"%rv))
        else: skipped+=1
        continue
    # rustc accepts: compute truth exhaustively
    vv,wr=ev(e,w,signed)
    if wr:
        wrapped_accept.append((sig,form)); continue
    def truth(x):
        xs = x-(1<<w) if (signed and (x>>(w-1))&1) else x
        vs = vv-(1<<w) if (signed and (vv>>(w-1))&1) else vv
        if left: a,b=vs,xs
        else: a,b=xs,vs
        return {'==':a==b,'<=':a<=b,'<':a<b}[op]
    allt=all(truth(x) for x in range(1<<w))
    if rv=="verified":
        if not allt: unsound.append((sig,form,"VERIFIED non-tautology"))
        else: ok+=1
    elif rv=="failed":
        if allt: discrep.append((sig,form,"FAILED but tautology"))
        else: ok+=1
    else:
        skipped+=1
print("total",tot,"ok",ok,"refused",skipped)
print("UNSOUND:",len(unsound))
for s,f,m in unsound[:40]: print("  [%s] %s :: %s"%(s,f,m))
print("DISCREPANCY:",len(discrep))
for s,f,m in discrep[:40]: print("  [%s] %s :: %s"%(s,f,m))
print("wrapped-but-rustc-accepted (eval ambiguity):",len(wrapped_accept))
for s,f in wrapped_accept[:10]: print("  [%s] %s"%(s,f))

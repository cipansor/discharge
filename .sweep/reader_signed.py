import subprocess, os, random
BIN=os.environ["SWEEP_BIN"]
# Two typed operands, signedness chosen by the signature. Enumerate the full domain.
def to_s(v, w):
    if v >> (w-1) & 1: return v - (1<<w)
    return v
def ev(t, env, w, signed):
    k=t[0]; M=(1<<w)-1
    if k=='v': return env[t[1]] & M
    if k=='c':
        v=t[1] & M
        return v
    op=t[1]; l=ev(t[2],env,w,signed); r=ev(t[3],env,w,signed)
    if signed:
        ls=to_s(l,w); rs=to_s(r,w)
    else:
        ls=l; rs=r
    if op=='&': return l & r
    if op=='|': return l | r
    if op=='^': return l ^ r
    if op=='+': return (l+r)&M
    if op=='-': return (l-r)&M
    if op=='*': return (l*r)&M
    if op=='>>':
        amt = rs % w
        if signed: return (ls >> amt) & M
        return l >> amt
    if op=='<<':
        amt = rs % w
        return (l << amt) & M
    raise Exception(op)
def rd(t, names):
    k=t[0]
    if k=='v': return names[t[1]]
    if k=='c': return str(t[1])
    return "(%s %s %s)"%(rd(t[2],names),t[1],rd(t[3],names))
def has_var(t):
    if t[0]=='v': return True
    if t[0]=='c': return False
    return has_var(t[2]) or has_var(t[3])
def truth(pt, env, w, signed):
    k=pt[0]
    if k=='cmp':
        # Rust types a comparison with no typed operand as i32; the literal's type
        # is inferred from a typed operand only when one is present.
        typed = has_var(pt[2]) or has_var(pt[3])
        ew, es = (w, signed) if typed else (32, True)
        op=pt[1]; l=ev(pt[2],env,ew,es); r=ev(pt[3],env,ew,es)
        if es:
            l=to_s(l,ew); r=to_s(r,ew)
        return {'==':l==r,'!=':l!=r,'<':l<r,'<=':l<=r,'>':l>r,'>=':l>=r}[op]
    if k=='and': return truth(pt[1],env,w,signed) and truth(pt[2],env,w,signed)
    if k=='or':  return truth(pt[1],env,w,signed) or truth(pt[2],env,w,signed)
    raise Exception(k)
def rdp(pt,names):
    k=pt[0]
    if k=='cmp': return "%s %s %s"%(rd(pt[2],names),pt[1],rd(pt[3],names))
    if k=='and': return "(%s && %s)"%(rdp(pt[1],names),rdp(pt[2],names))
    if k=='or':  return "(%s || %s)"%(rdp(pt[1],names),rdp(pt[2],names))
    raise Exception(k)
def reader(formula, sig):
    src="#![allow(dead_code)]\n/// requires: true\n/// ensures: %s\npub fn s0(%s)->u8{0}\n"%(formula,sig)
    open(".sweep/tmp/one.rs","w").write(src)
    try:
        p=subprocess.run([BIN,".sweep/tmp/one.rs"],capture_output=True,text=True,timeout=25)
    except subprocess.TimeoutExpired:
        return "hang"
    for line in p.stdout.splitlines():
        if line.startswith("s0"):
            return "verified" if "verified" in line else ("failed" if "FAILED" in line else "skipped")
    return "skipped"
random.seed(11)
OPS=['&','|','^','+','-','*','>>','<<']
CONSTS=[0,1,2,3,7,8,15,16,31,63,100,127,128,200,240,254,255]
CMPS=['==','!=','<','<=','>','>=']
def rand_expr(depth, nvars):
    if depth==0 or random.random()<0.4:
        if random.random()<0.55: return ('v', random.randrange(nvars))
        return ('c', random.choice(CONSTS))
    return ('b',random.choice(OPS),rand_expr(depth-1,nvars),rand_expr(depth-1,nvars))
def rand_pred(depth, nvars):
    r=random.random()
    if depth>0 and r<0.18: return ('and',rand_pred(depth-1,nvars),rand_pred(depth-1,nvars))
    if depth>0 and r<0.36: return ('or',rand_pred(depth-1,nvars),rand_pred(depth-1,nvars))
    return ('cmp',random.choice(CMPS),rand_expr(2,nvars),rand_expr(2,nvars))
CASES=[("x: i8, y: i8",8,True,2),("x: u8, y: u8",8,False,2),
       ("x: i8",8,True,1),("x: i16",16,True,1)]
unsound=[]; miss=[]; ok=0; skipped=0; hangs=0; tot=0
for sig,w,signed,nvars in CASES:
    names=["x","y"][:nvars]
    for i in range(700):
        pt=rand_pred(2,nvars); f=rdp(pt,names); tot+=1
        v=reader(f,sig)
        if v=="hang": hangs+=1; unsound.append((sig,f,"HANG")); continue
        if v=="skipped": skipped+=1; continue
        alltrue=True; hasfalse=False
        for combo in range((1<<w)**nvars):
            env={}
            for j in range(nvars):
                env[j]=(combo >> (w*j)) & ((1<<w)-1)
            if truth(pt,env,w,signed): pass
            else: hasfalse=True; alltrue=False
        if v=="verified":
            if not alltrue: unsound.append((sig,f,"VERIFIED non-tautology"))
            else: ok+=1
        else:
            if not hasfalse: miss.append((sig,f,"FAILED tautology"))
            else: ok+=1
print("total",tot,"ok",ok,"skipped",skipped,"hangs",hangs)
print("UNSOUND:",len(unsound))
for s,f,m in unsound[:30]: print("  [%s] %s :: %s"%(s,f,m))
print("WRONG-REFUTATION:",len(miss))
for s,f,m in miss[:30]: print("  [%s] %s :: %s"%(s,f,m))

import subprocess, os, time, itertools, random
BIN=os.environ["SWEEP_BIN"]
MASK=0xFF
# Expression tree: ('v',) is the variable x; ('c',k) a constant; ('b',op,l,r) a binop.
def ev(t, x):
    k=t[0]
    if k=='v': return x & MASK
    if k=='c': return t[1] & MASK
    op=t[1]; l=ev(t[2],x); r=ev(t[3],x)
    if op=='&': return l & r
    if op=='|': return l | r
    if op=='^': return l ^ r
    if op=='+': return (l+r)&MASK
    if op=='-': return (l-r)&MASK
    if op=='*': return (l*r)&MASK
    if op=='>>': return l >> (r & 7)
    if op=='<<': return (l << (r & 7)) & MASK
    raise Exception(op)
def rd(t):
    k=t[0]
    if k=='v': return "x"
    if k=='c': return str(t[1])
    return "(%s %s %s)"%(rd(t[2]),t[1],rd(t[3]))
def cmp_truth(pt, x):
    k=pt[0]
    if k=='cmp':
        op=pt[1]; l=ev(pt[2],x); r=ev(pt[3],x)
        return {'==':l==r,'!=':l!=r,'<':l<r,'<=':l<=r,'>':l>r,'>=':l>=r}[op]
    if k=='and': return cmp_truth(pt[1],x) and cmp_truth(pt[2],x)
    if k=='or':  return cmp_truth(pt[1],x) or cmp_truth(pt[2],x)
    if k=='not': return not cmp_truth(pt[1],x)
    raise Exception(k)
def rdp(pt):
    k=pt[0]
    if k=='cmp': return "%s %s %s"%(rd(pt[2]),pt[1],rd(pt[3]))
    if k=='and': return "(%s && %s)"%(rdp(pt[1]),rdp(pt[2]))
    if k=='or':  return "(%s || %s)"%(rdp(pt[1]),rdp(pt[2]))
    if k=='not': return "(!(%s))"%(rdp(pt[1]))
    raise Exception(k)
def reader(formula):
    src="#![allow(dead_code)]\n/// requires: true\n/// ensures: %s\npub fn s0(x: u8)->u8{0}\n"%formula
    open(".sweep/tmp/one.rs","w").write(src)
    try:
        p=subprocess.run([BIN,".sweep/tmp/one.rs"],capture_output=True,text=True,timeout=20)
    except subprocess.TimeoutExpired:
        return "hang"
    for line in p.stdout.splitlines():
        if line.startswith("s0"):
            return "verified" if "verified" in line else ("failed" if "FAILED" in line else "skipped")
    return "skipped"

random.seed(7)
OPS=['&','|','^','+','-','*','>>','<<']
CONSTS=[0,1,2,3,7,8,15,16,31,63,127,128,240,254,255]
def rand_expr(depth):
    if depth==0 or random.random()<0.35:
        return ('v',) if random.random()<0.55 else ('c',random.choice(CONSTS))
    return ('b',random.choice(OPS),rand_expr(depth-1),rand_expr(depth-1))
CMPS=['==','!=','<','<=','>','>=']
def rand_pred(depth):
    r=random.random()
    if depth>0 and r<0.2: return ('and',rand_pred(depth-1),rand_pred(depth-1))
    if depth>0 and r<0.4: return ('or',rand_pred(depth-1),rand_pred(depth-1))
    return ('cmp',random.choice(CMPS),rand_expr(2),rand_expr(2))

unsound=[]; miss=[]; ok=0; skipped=0; hangs=0; tot=0
for i in range(3000):
    pt=rand_pred(2)
    f=rdp(pt)
    tot+=1
    v=reader(f)
    if v=="hang": hangs+=1; unsound.append((f,"HANG")); continue
    if v=="skipped": skipped+=1; continue
    truth=set()
    for x in range(256):
        truth.add(cmp_truth(pt,x))
    all_true = (truth=={True})
    has_false = (False in truth)
    if v=="verified":
        # verified is only sound when the formula holds for every x
        if not all_true: unsound.append((f,"VERIFIED but truth=%s"%truth))
        else: ok+=1
    elif v=="failed":
        # a refutation is only sound when a counterexample really exists
        if not has_false: miss.append((f,"FAILED but tautology"))
        else: ok+=1
print("total",tot,"ok",ok,"skipped",skipped,"hangs",hangs)
print("UNSOUND (verified a non-tautology):",len(unsound))
for f,m in unsound[:40]: print("  ",f,"::",m)
print("WRONG-REFUTATION (failed a tautology):",len(miss))
for f,m in miss[:40]: print("  ",f,"::",m)

import subprocess, os, random
BIN=os.environ["SWEEP_BIN"]
M=0xFF
def ev(t,x):
    k=t[0]
    if k=='v': return x&M
    if k=='c': return t[1]&M
    op=t[1]; l=ev(t[2],x); r=ev(t[3],x)
    return {'&':l&r,'|':l|r,'^':l^r,'+':(l+r)&M,'-':(l-r)&M,'*':(l*r)&M,
            '>>':l>>(r&7),'<<':(l<<(r&7))&M}[op]
def rd(t):
    k=t[0]
    if k=='v': return "x"
    if k=='c': return str(t[1])
    return "(%s %s %s)"%(rd(t[2]),t[1],rd(t[3]))
def tv(pt,x):
    k=pt[0]
    if k=='cmp':
        l=ev(pt[2],x); r=ev(pt[3],x)
        return {'==':l==r,'!=':l!=r,'<':l<r,'<=':l<=r,'>':l>r,'>=':l>=r}[pt[1]]
    if k=='and': return tv(pt[1],x) and tv(pt[2],x)
    if k=='or':  return tv(pt[1],x) or tv(pt[2],x)
def rdp(pt):
    k=pt[0]
    if k=='cmp': return "%s %s %s"%(rd(pt[2]),pt[1],rd(pt[3]))
    if k=='and': return "(%s && %s)"%(rdp(pt[1]),rdp(pt[2]))
    if k=='or':  return "(%s || %s)"%(rdp(pt[1]),rdp(pt[2]))
def reader(req,ens):
    src=("#![allow(dead_code)]\n/// requires: %s\n/// ensures: %s\n"
         "pub fn s0(x: u8)->u8{0}\n"%(req,ens))
    open(".sweep/tmp/one.rs","w").write(src)
    try:
        p=subprocess.run([BIN,".sweep/tmp/one.rs"],capture_output=True,text=True,timeout=20)
    except subprocess.TimeoutExpired: return "hang"
    for line in p.stdout.splitlines():
        if line.startswith("s0"):
            return "verified" if "verified" in line else ("failed" if "FAILED" in line else "skipped")
    return "skipped"
random.seed(23)
OPS=['&','|','^','+','-','*','>>','<<']
CONSTS=[0,1,2,3,7,8,15,16,31,63,127,128,240,254,255]
CMPS=['==','!=','<','<=','>','>=']
def rexpr(d):
    if d==0 or random.random()<0.4:
        return ('v',) if random.random()<0.55 else ('c',random.choice(CONSTS))
    return ('b',random.choice(OPS),rexpr(d-1),rexpr(d-1))
def rpred(d):
    r=random.random()
    if d>0 and r<0.2: return ('and',rpred(d-1),rpred(d-1))
    if d>0 and r<0.4: return ('or',rpred(d-1),rpred(d-1))
    return ('cmp',random.choice(CMPS),rexpr(2),rexpr(2))
unsound=[];miss=[];ok=0;vacuous=0;skipped=0;hangs=0;tot=0
for i in range(2500):
    P=rpred(2); Q=rpred(2); tot+=1
    v=reader(rdp(P),rdp(Q))
    if v=="hang": hangs+=1; unsound.append((rdp(P),rdp(Q),"HANG")); continue
    if v=="skipped": skipped+=1; continue
    sat = any(tv(P,x) for x in range(256))
    valid = all((not tv(P,x)) or tv(Q,x) for x in range(256))
    cex = any(tv(P,x) and not tv(Q,x) for x in range(256))
    if v=="verified":
        # Sound only if the precondition is reachable AND P => Q.
        if not sat: unsound.append((rdp(P),rdp(Q),"VERIFIED with unreachable precondition"))
        elif not valid: unsound.append((rdp(P),rdp(Q),"VERIFIED non-implication"))
        else: ok+=1
    elif v=="failed":
        # Two correct reasons to fail: a real counterexample, or a vacuous
        # precondition (the documented "unreachable precondition is not a proof").
        if cex: ok+=1
        elif not sat: vacuous+=1
        else: miss.append((rdp(P),rdp(Q),"FAILED but sat precondition and P=>Q"))
    else: ok+=1
print("total",tot,"ok",ok,"vacuous-refusals",vacuous,"skipped",skipped,"hangs",hangs)
print("UNSOUND:",len(unsound))
for a,b,m in unsound[:30]: print("  req %s / ens %s :: %s"%(a,b,m))
print("WRONG-REFUTATION (sat premise, implication holds, but failed):",len(miss))
for a,b,m in miss[:30]: print("  req %s / ens %s :: %s"%(a,b,m))

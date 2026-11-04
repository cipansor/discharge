import subprocess, os, json, time
RUSTC=os.environ["DISCHARGE_RUSTC"]; BIN=os.environ["SWEEP_BIN"]
SIGS={
 "w8":"x: u8, y: i8",
 "w16":"x: u8, y: i8, a: u16, b: i16",
 "w32":"x: u8, y: i8, a: u16, b: i16, c: u32, d: i32",
 "w64":"x: u8, y: i8, a: u16, b: i16, c: u32, d: i32, e: u64, f: i64",
}
CONSTS=["255","!0","1","2","128","-1","-128","200","(200 + 100)","(!0 + 1)",
        "(255 >> 1)","(255 / 2)","(255 % 2)","(!0 >> 1)","(128 << 1)","(1 << 7)"]
OPS=["==","!=","<","<=",">",">="]
shapes=[]
for c1 in CONSTS:
    for c2 in CONSTS:
        for op in OPS:
            shapes.append(("pure","(%s) %s (%s)"%(c1,op,c2)))
PART={"w8":["x","y"],"w16":["x","y","a","b"],"w32":["x","y","a","b"],
      "w64":["x","y","a","b","c","d","e","f"]}
for name in SIGS:
    for p in PART[name]:
        for c in CONSTS:
            for op in OPS:
                shapes.append((name,"(%s) %s %s"%(c,op,p)))
for name in SIGS:
    for p in PART[name]:
        for amt in ["(1 + 1)","(2 * 2)","(8 - 1)","(1 << 3)","(16 / 2)"]:
            shapes.append((name,"(%s >> %s) == 0"%(p,amt)))
            shapes.append((name,"(%s << %s) == 0"%(p,amt)))
        for dv in ["(1 + 1)","(2 * 2)","(8 - 1)","(16 / 2)"]:
            shapes.append((name,"(%s / %s) == 0"%(p,dv)))
            shapes.append((name,"(%s %% %s) == 0"%(p,dv)))
print("shapes",len(shapes))
def rbad(sig,exprs):
    src="#![allow(dead_code,unused_comparisons)]\nfn _c(%s){\n"%sig
    for e in exprs: src+=" let _ = %s;\n"%e
    src+="}\n"
    p=subprocess.run([RUSTC,"--edition","2021","--crate-type","lib","--error-format=json","-o",".sweep/tmp/o.rlib","-"],input=src,capture_output=True,text=True)
    bad=set()
    for line in p.stderr.splitlines():
        try: d=json.loads(line)
        except: continue
        if d.get("level")!="error": continue
        for sp in d.get("spans",[]):
            if sp.get("is_primary") and sp.get("file_name")=="<anon>":
                i=sp["line_start"]-3
                if 0<=i<len(exprs): bad.add(i)
    return bad
def one(sig,expr,idx):
    src="#![allow(dead_code)]\n/// requires: true\n/// ensures: %s\npub fn s%d(%s)->u8{x}\n"%(expr,idx,sig)
    open(".sweep/tmp/one.rs","w").write(src)
    t0=time.time()
    try:
        p=subprocess.run([BIN,".sweep/tmp/one.rs"],capture_output=True,text=True,timeout=20)
    except subprocess.TimeoutExpired:
        return ("hang",time.time()-t0)
    v="skipped"
    for line in p.stdout.splitlines():
        if line.startswith("s%d"%idx):
            v="verified" if "verified" in line else ("failed" if "FAILED" in line else "skipped")
    return (v,time.time()-t0)
sound=[]; miss=0; hangs=[]; tot=0; slow=[]
for name in SIGS:
    sub=[(n,e) for (n,e) in shapes if n==name]
    exprs=[e for (_,e) in sub]
    bad=rbad(SIGS[name],exprs)
    for i,e in enumerate(exprs):
        tot+=1
        v,dt=one(SIGS[name],e,i)
        if v=="hang":
            hangs.append((name,e)); print("  HANG %s %s"%(name,e),flush=True)
        else:
            if dt>5: slow.append((name,e,dt))
            if i in bad and v=="verified": sound.append((name,e))
            elif i not in bad and v=="skipped": miss+=1
print("SOUNDNESS bugs:",len(sound))
for n,s in sound[:100]: print("  %s %s"%(n,s))
print("HANGS:",len(hangs))
for n,s in hangs: print("  %s %s"%(n,s))
print("COMPLETENESS misses:",miss,"of",tot)
print("SLOW (5-20s):",len(slow))
for n,s,d in slow[:40]: print("  %.1fs %s %s"%(d,n,s))
open(".sweep/tmp/sound_const2.txt","w").write("\n".join("%s %s"%(n,s) for n,s in sound))
open(".sweep/tmp/hangs_const2.txt","w").write("\n".join("%s %s"%(n,s) for n,s in hangs))

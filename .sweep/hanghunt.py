import subprocess, os, time
BIN=os.environ["SWEEP_BIN"]
SIGS={
 "u8":"x: u8","u16":"a: u16","u32":"c: u32","u64":"e: u64",
 "i8":"y: i8","i16":"b: i16","i32":"d: i32","i64":"f: i64",
}
CONSTS=[0,1,2,3,4,5,6,7,8,9,10,15,16,17,31,32,33,63,64,100,127,128,200,254,255]
OPS=["+","-","*","/","%","&","|","^","<<",">>"]
def one(sig,expr,idx,to):
    src="#![allow(dead_code)]\n/// requires: true\n/// ensures: %s\npub fn s%d(%s)->u8{0}\n"%(expr,idx,sig)
    open(".sweep/tmp/one.rs","w").write(src)
    t0=time.time()
    try:
        p=subprocess.run([BIN,".sweep/tmp/one.rs"],capture_output=True,text=True,timeout=to)
    except subprocess.TimeoutExpired:
        return ("hang",time.time()-t0)
    return ("ok",time.time()-t0)
hangs=[]; slow=[]; tot=0
for name,sig in SIGS.items():
    for c in CONSTS:
        for op in OPS:
            for form in ["(%s %s %s) == 0","(%s %s %s) == 0"]:
                pass
            e="(%s %s %s) == 0"%(sig.split(":")[0].strip(),op,c)
            tot+=1
            v,dt=one(sig,e,0,20)
            if v=="hang":
                hangs.append((name,e)); print(" HANG %s %s"%(name,e),flush=True)
            elif dt>5:
                slow.append((name,e,dt)); print("  slow %.1fs %s %s"%(dt,name,e),flush=True)
print("total",tot,"HANGS",len(hangs),"slow",len(slow))
for n,e in hangs: print("  HANG",n,e)
for n,e,d in slow: print("  %.1fs %s %s"%(d,n,e))

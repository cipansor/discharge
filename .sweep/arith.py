import subprocess, os, json, time
RUSTC=os.environ["DISCHARGE_RUSTC"]; BIN=os.environ["SWEEP_BIN"]
SIGS={
 "w8":"x: u8, y: i8",
 "w16":"x: u8, y: i8, a: u16, b: i16",
 "w32":"x: u8, y: i8, a: u16, b: i16, c: u32, d: i32",
 "w64":"x: u8, y: i8, a: u16, b: i16, c: u32, d: i32, e: u64, f: i64",
}
PART={"w8":["x","y"],"w16":["x","y","a","b"],"w32":["x","y","a","b","c","d"],
      "w64":["x","y","a","b","c","d","e","f"]}
CONSTS=["255","1","2","128","200","(200 + 100)","(!0 + 1)","(255 >> 1)","(255 / 2)",
        "(255 % 2)","(128 << 1)","(1 << 7)","(8 - 1)","(2 * 2)","(16 / 2)","(1 + 1)"]
AOPS=["+","-","*","&","|","^"]
shapes=[]
for name in SIGS:
    for p in PART[name]:
        for c in CONSTS:
            for op in AOPS:
                # constant expression as left and as right operand
                shapes.append((name,"((%s) %s %s) == 0"%(c,op,p)))
                shapes.append((name,"(%s %s (%s)) == 0"%(p,op,c)))
print("arith shapes",len(shapes))
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
    try:
        p=subprocess.run([BIN,".sweep/tmp/one.rs"],capture_output=True,text=True,timeout=20)
    except subprocess.TimeoutExpired:
        return "hang"
    for line in p.stdout.splitlines():
        if line.startswith("s%d"%idx):
            return "verified" if "verified" in line else ("failed" if "FAILED" in line else "skipped")
    return "skipped"
sound=[]; hangs=[]; miss=0; tot=0; dec=0
for name in SIGS:
    sub=[e for (n,e) in shapes if n==name]
    bad=rbad(SIGS[name],sub)
    for i,e in enumerate(sub):
        tot+=1
        v=one(SIGS[name],e,i)
        if v=="hang": hangs.append((name,e)); print(" HANG %s %s"%(name,e),flush=True)
        elif v=="verified":
            dec+=1
            if i in bad: sound.append((name,e)); print(" SOUND %s %s"%(name,e),flush=True)
        elif v=="skipped": miss+=1
print("total",tot,"verified",dec,"SOUNDNESS",len(sound),"HANGS",len(hangs),"skipped",miss)
open(".sweep/tmp/sound_arith.txt","w").write("\n".join("%s %s"%(n,s) for n,s in sound))

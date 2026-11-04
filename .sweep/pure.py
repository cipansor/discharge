import subprocess, os, json, time
RUSTC=os.environ["DISCHARGE_RUSTC"]; BIN=os.environ["SWEEP_BIN"]
SIG="x: u8, y: i8"
CONSTS=["255","!0","1","2","128","-1","-128","200","(200 + 100)","(!0 + 1)",
        "(255 >> 1)","(255 / 2)","(255 % 2)","(!0 >> 1)","(128 << 1)","(1 << 7)"]
OPS=["==","!=","<","<=",">",">="]
shapes=[]
for c1 in CONSTS:
    for c2 in CONSTS:
        for op in OPS:
            shapes.append("(%s) %s (%s)"%(c1,op,c2))
print("pure shapes",len(shapes))
def rbad(exprs):
    src="#![allow(dead_code,unused_comparisons)]\nfn _c(%s){\n"%SIG
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
def one(expr,idx):
    src="#![allow(dead_code)]\n/// requires: true\n/// ensures: %s\npub fn s%d(%s)->u8{x}\n"%(expr,idx,SIG)
    open(".sweep/tmp/one.rs","w").write(src)
    try:
        p=subprocess.run([BIN,".sweep/tmp/one.rs"],capture_output=True,text=True,timeout=20)
    except subprocess.TimeoutExpired:
        return "hang"
    for line in p.stdout.splitlines():
        if line.startswith("s%d"%idx):
            return "verified" if "verified" in line else ("failed" if "FAILED" in line else "skipped")
    return "skipped"
bad=rbad(shapes)
sound=[]; hangs=[]; miss=0; decided=0
for i,e in enumerate(shapes):
    v=one(e,i)
    if v=="hang": hangs.append(e); print(" HANG",e,flush=True)
    elif v=="verified":
        decided+=1
        if i in bad: sound.append(e); print(" SOUND",e,flush=True)
    elif v=="skipped": miss+=1
print("total",len(shapes),"verified",decided,"SOUNDNESS",len(sound),"HANGS",len(hangs),"skipped",miss)
print("rustc-rejected count:",len(bad))

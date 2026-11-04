import subprocess, os
BIN=os.path.abspath("target/release/examples/mir_coverage")
SIG="x: u8, y: i8, a: u16, b: i16, c: u32, d: i32, e: u64, f: i64"
CONSTS=["255","!0","1","2","128","-1","-128","200","(200 + 100)","(!0 + 1)",
        "(255 >> 1)","(255 / 2)","(255 % 2)","(!0 >> 1)","(128 << 1)","(1 << 7)"]
OPS=["==","!=","<","<=",">",">="]
PART=["x","y","a","b","c","d","e","f"]
sub=[]
for p in PART:
    for c in CONSTS:
        for op in OPS:
            sub.append("(%s) %s %s"%(c,op,p))
for p in PART:
    for amt in ["(1 + 1)","(2 * 2)","(8 - 1)","(1 << 3)","(16 / 2)"]:
        sub.append("(%s >> %s) == 0"%(p,amt))
        sub.append("(%s << %s) == 0"%(p,amt))
    for dv in ["(1 + 1)","(2 * 2)","(8 - 1)","(16 / 2)"]:
        sub.append("(%s / %s) == 0"%(p,dv))
        sub.append("(%s %% %s) == 0"%(p,dv))
print("sub len",len(sub),"start600:",sub[600])
def run(chunk,to=30):
    src="#![allow(dead_code)]\n"
    for i,e in enumerate(chunk):
        src+="/// requires: true\n/// ensures: %s\npub fn s%d(%s)->u8{x}\n"%(e,i,SIG)
    open(".sweep/tmp/one.rs","w").write(src)
    try:
        subprocess.run([BIN,".sweep/tmp/one.rs"],capture_output=True,text=True,timeout=to)
        return True
    except subprocess.TimeoutExpired:
        return False
chunk=sub[600:900]
print("batch len",len(chunk))
while len(chunk)>1:
    h=len(chunk)//2
    if not run(chunk[:h]): chunk=chunk[:h]
    elif not run(chunk[h:]): chunk=chunk[h:]
    else:
        print("neither half hangs alone (true batch effect), size",len(chunk)); break
print("minimal hanging set:",chunk)

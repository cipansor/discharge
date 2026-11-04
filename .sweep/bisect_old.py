import subprocess, os
BIN=os.path.abspath("target/release/examples/mir_coverage")
SIG="x: u8, y: i8, a: u16, b: i16, c: u32, d: i32, e: u64, f: i64"
CONSTS=["255","!0","1","2","128","-1","-128","200","(200 + 100)","(!0 + 1)",
        "(255 >> 1)","(255 / 2)","(255 % 2)","(!0 >> 1)","(128 << 1)","(1 << 7)"]
OPS=["==","!=","<","<=",">",">="]
PART=["x","y","a","b","c","d","e","f"]
shapes=[]
for p in PART:
    for c in CONSTS:
        for op in OPS:
            shapes.append("(%s) %s %s"%(c,op,p))
def run(chunk):
    src="#![allow(dead_code)]\n"
    for i,e in enumerate(chunk):
        src+="/// requires: true\n/// ensures: %s\npub fn s%d(%s)->u8{x}\n"%(e,i,SIG)
    open(".sweep/tmp/one.rs","w").write(src)
    try:
        subprocess.run([BIN,".sweep/tmp/one.rs"],capture_output=True,text=True,timeout=20)
        return True
    except subprocess.TimeoutExpired:
        return False
# start from shape 600 (the observed hang batch start)
chunk=shapes[600:]
print("start chunk size",len(chunk),"first:",chunk[0])
while len(chunk)>1:
    half=len(chunk)//2
    if not run(chunk[:half]):
        chunk=chunk[:half]; print("hang in first half, size",len(chunk))
    elif not run(chunk[half:]):
        chunk=chunk[half:]; print("hang in second half, size",len(chunk))
    else:
        print("neither half hangs alone (batch effect), size",len(chunk)); break
print("minimal:",chunk)

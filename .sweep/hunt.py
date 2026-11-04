import subprocess, os
BIN=os.path.abspath("target/release/examples/mir_coverage")
SIGS={
 "w8":"x: u8, y: i8",
 "w16":"x: u8, y: i8, a: u16, b: i16",
 "w32":"x: u8, y: i8, a: u16, b: i16, c: u32, d: i32",
 "w64":"x: u8, y: i8, a: u16, b: i16, c: u32, d: i32, e: u64, f: i64",
}
CONSTS=["255","!0","1","2","128","-1","-128","200","(200 + 100)","(!0 + 1)",
        "(255 >> 1)","(255 / 2)","(255 % 2)","(!0 >> 1)","(128 << 1)","(1 << 7)"]
OPS=["==","!=","<","<=",">",">="]
PART={"w8":["x","y"],"w16":["x","y","a","b"],"w32":["x","y","a","b"],
      "w64":["x","y","a","b","c","d","e","f"]}
hangs=[]
for name in SIGS:
    for p in PART[name]:
        for c in CONSTS:
            for op in OPS:
                e="(%s) %s %s"%(c,op,p)
                src="#![allow(dead_code)]\n/// requires: true\n/// ensures: %s\npub fn s0(%s)->u8{x}\n"%(e,SIGS[name])
                open(".sweep/tmp/one.rs","w").write(src)
                try:
                    r=subprocess.run([BIN,".sweep/tmp/one.rs"],capture_output=True,text=True,timeout=8)
                except subprocess.TimeoutExpired:
                    hangs.append((name,e)); print("HANG %s %s"%(name,e)); continue
print("total hangs:",len(hangs))

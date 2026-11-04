"""Probe one expression at a time: rustc accept/reject vs the reader's outcome.

Usage: SWEEP_BIN=... DISCHARGE_RUSTC=... python3 probe.py 'EXPR|SIG' ...
An EXPR is checked both as an `ensures:` (reader decides or refuses) and by rustc.
"""
import os, subprocess, sys

BIN = os.environ["SWEEP_BIN"]
RUSTC = os.environ["DISCHARGE_RUSTC"]
D = os.path.dirname(os.path.abspath(__file__))
TMP = os.path.join(D, "tmp")
os.makedirs(TMP, exist_ok=True)


def rustc_ok(expr, sig):
    src = "#![allow(dead_code,unused)]\nfn s0(%s){ let _ = %s; }\n" % (sig, expr)
    p = os.path.join(TMP, "pr.rs")
    open(p, "w").write(src)
    r = subprocess.run(
        [RUSTC, "--edition", "2021", "--crate-type", "lib", "--emit=obj",
         "-o", os.path.join(TMP, "pr.o"), p],
        capture_output=True,
    )
    return r.returncode == 0


def reader(expr, sig, kind="ensures"):
    src = ("#![allow(dead_code)]\n/// requires: true\n/// %s: %s\n"
           "pub fn s0(%s)->u8{0}\n") % (kind, expr, sig)
    p = os.path.join(TMP, "pc.rs")
    open(p, "w").write(src)
    r = subprocess.run([BIN, p], capture_output=True)
    for line in r.stdout.decode().splitlines():
        if line.startswith("s0"):
            parts = line.split(None, 3)
            return parts[1], (parts[3] if len(parts) > 3 else "")
    return "??", (r.stdout.decode() + r.stderr.decode())[:200]


for arg in sys.argv[1:]:
    expr, _, sig = arg.partition("|")
    rc = "ACCEPT" if rustc_ok(expr, sig) else "REJECT"
    out, detail = reader(expr, sig)
    flag = ""
    if rc == "REJECT" and out in ("verified", "FAILED"):
        flag = "  <-- WRONG VERDICT"
    elif rc == "ACCEPT" and out == "skipped":
        flag = "  <-- over-refusal"
    print("%-34s %-14s rustc=%-7s reader=%-9s %s%s"
          % (expr, sig, rc, out, detail[:40], flag))

"""Flag ANY decided verdict (verified OR failed) on a program rustc rejects.

The earlier sweeps counted only `verified` on a rejected shape as a soundness
bug. A `FAILED` verdict on a program that does not compile is just as wrong: it
claims a fact about a program that does not exist. Every wrong verdict found in
the negation/overflow class was of that second kind, which is why the older
sweep never saw them.
"""
import os, subprocess, sys

BIN = os.environ["SWEEP_BIN"]
RUSTC = os.environ["DISCHARGE_RUSTC"]
TMP = os.path.join(os.path.dirname(os.path.abspath(__file__)), "tmp")
os.makedirs(TMP, exist_ok=True)

SIGS = {
    "w8": "y: i8",
    "w16": "y: i8, b: i16",
    "w32": "y: i8, b: i16, d: i32",
    "w64": "y: i8, b: i16, d: i32, f: i64",
}
# Constant expressions with no typed operand of their own: folds, complements,
# shifts (including nested amounts), and negations of constants and bounds.
CONSTS = [
    "0", "1", "2", "3", "7", "127", "128", "200", "255", "256",
    "!0", "!1", "!128", "!255",
    "(1 + 127)", "(100 + 28)", "(64 + 64)", "(2 * 64)", "(3 * 43)", "(128 - 63)",
    "(255 >> 1)", "(1 << 7)", "(2 << 7)", "(3 << 7)", "(64 << 1)", "(127 << 1)",
    "(128 << 1)", "(1 << 8)", "(1 << (2 << 7))", "(5 << 5)", "(200 << 0)",
    "(-1 << 7)", "(-2 << 7)", "(-128)", "(-129)", "(-127)",
    "-i8::MIN", "-i8::MAX", "i8::MIN", "i8::MAX", "-128i8", "-(-128i8)",
    "-(i8::MIN)", "-(128i8)",
]
OPS = ["==", "!=", "<", "<=", ">", ">="]


def rustc_bad(sig, exprs):
    src = "#![allow(dead_code,unused_comparisons)]\nfn _c(%s){\n" % sig
    for e in exprs:
        src += " let _ = %s;\n" % e
    src += "}\n"
    p = subprocess.run(
        [RUSTC, "--edition", "2021", "--crate-type", "lib", "--error-format=json",
         "-o", os.path.join(TMP, "o.rlib"), "-"],
        input=src, capture_output=True, text=True,
    )
    bad = set()
    for line in p.stderr.splitlines():
        try:
            import json
            d = json.loads(line)
        except Exception:
            continue
        if d.get("level") != "error":
            continue
        for sp in d.get("spans", []):
            if sp.get("is_primary") and sp.get("file_name") == "<anon>":
                i = sp["line_start"] - 3
                if 0 <= i < len(exprs):
                    bad.add(i)
    return bad


def reader(sig, exprs):
    src = "#![allow(dead_code)]\n"
    for i, e in enumerate(exprs):
        src += "/// requires: true\n/// ensures: %s\npub fn s%d(%s)->u8{0}\n" % (e, i, sig)
    open(os.path.join(TMP, "b.rs"), "w").write(src)
    p = subprocess.run([BIN, os.path.join(TMP, "b.rs")], capture_output=True, text=True)
    out = {}
    for line in p.stdout.splitlines():
        parts = line.split()
        if not parts or not parts[0].startswith("s"):
            continue
        try:
            i = int(parts[0][1:])
        except ValueError:
            continue
        out[i] = "verified" if "verified" in line else ("failed" if "FAILED" in line else "skipped")
    return out


wrong = []
miss = 0
tot = 0
shapes = []
for name, sig in SIGS.items():
    for c in CONSTS:
        for op in OPS:
            shapes.append((name, "y %s (%s)" % (op, c)))
            shapes.append((name, "(%s) %s y" % (c, op)))
        shapes.append((name, "y == -y"))
for name, sig in SIGS.items():
    sub = [e for (n, e) in shapes if n == name]
    for st in range(0, len(sub), 300):
        ch = sub[st:st + 300]
        bad = rustc_bad(sig, ch)
        verd = reader(sig, ch)
        for i, e in enumerate(ch):
            tot += 1
            v = verd.get(i, "skipped")
            if i in bad and v in ("verified", "failed"):
                wrong.append((name, e, v))
            elif i not in bad and v == "skipped":
                miss += 1
print("WRONG VERDICTS (decided on a rejected program):", len(wrong))
for n, s, v in wrong[:120]:
    print("  %-4s %-34s %s" % (n, s, v))
print("over-refusals (accepted, skipped):", miss, "of", tot)

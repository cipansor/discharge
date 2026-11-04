"""Opaque-fold differential sweep.

Generates constant expressions that contain a bitwise complement (an *untyped*
constant with no width of its own), evaluates each with rustc (accept/reject)
and with the reader, and reports all four quadrants -- including the
*over-refusal* quadrant (`rustc ACCEPT but reader=skipped`) that the primary
sweep does not separate out.
"""
import subprocess, os, random, sys

BIN = os.environ["SWEEP_BIN"]
R = os.environ["DISCHARGE_RUSTC"]

LITS = [0, 1, 2, 3, 5, 7, 8, 15, 16, 31, 63, 64, 100, 127, 128, 129, 200, 240, 254, 255]
BIN_OPS = ['+', '-', '*', '&', '|', '^', '>>', '<<']


def ev(t, w, signed):
    M = (1 << w) - 1

    def sgn(v):
        return v - (1 << w) if (signed and (v >> (w - 1)) & 1) else v

    k = t[0]
    if k == 'c':
        return (t[1] & M, False)
    if k == 'u':
        v, wr = ev(t[2], w, signed)
        if t[1] == '-':
            return ((-v) & M, wr or v != 0)
        return ((~v) & M, wr)
    op = t[1]
    l, wl = ev(t[2], w, signed)
    r, wr = ev(t[3], w, signed)
    ls, rs = sgn(l), sgn(r)
    if op == '&':
        return (l & r, wl or wr)
    if op == '|':
        return (l | r, wl or wr)
    if op == '^':
        return (l ^ r, wl or wr)
    if op == '+':
        ex = ls + rs
        return (ex & M, wl or wr or not (-(1 << (w - 1)) <= ex <= (1 << (w - 1)) - 1))
    if op == '-':
        ex = ls - rs
        return (ex & M, wl or wr or not (-(1 << (w - 1)) <= ex <= (1 << (w - 1)) - 1))
    if op == '*':
        ex = ls * rs
        return (ex & M, wl or wr or not (-(1 << (w - 1)) <= ex <= (1 << (w - 1)) - 1))
    if op == '>>':
        if not (0 <= rs < w):
            return (0, True)
        return ((ls >> rs) & M, wl or wr)
    if op == '<<':
        if not (0 <= rs < w):
            return (0, True)
        ex = ls << rs
        return (ex & M, wl or wr or not (-(1 << (w - 1)) <= ex <= (1 << (w - 1)) - 1))
    raise Exception(op)


def rd(t):
    k = t[0]
    if k == 'c':
        return str(t[1])
    if k == 'u':
        return "(%s%s)" % (t[1], rd(t[2]))
    return "(%s %s %s)" % (rd(t[2]), t[1], rd(t[3]))


def has_bang(t):
    if t[0] == 'c':
        return False
    if t[0] == 'u':
        return t[1] == '!' or has_bang(t[2])
    return has_bang(t[2]) or has_bang(t[3])


def rustc_ok(sig, form):
    src = "#![allow(dead_code,unused)]\nfn s0(%s)->u8{ let _ = %s; 0 }\n" % (sig, form)
    open(".sweep/tmp/rc.rs", "w").write(src)
    p = subprocess.run([R, "--edition", "2021", "--crate-type", "lib", "--emit=obj",
                        "-o", ".sweep/tmp/rc.o", ".sweep/tmp/rc.rs"],
                       capture_output=True, text=True)
    return p.returncode == 0


def reader(sig, form):
    src = "#![allow(dead_code)]\n/// requires: true\n/// ensures: %s\npub fn s0(%s)->u8{0}\n" % (form, sig)
    open(".sweep/tmp/one.rs", "w").write(src)
    try:
        p = subprocess.run([BIN, ".sweep/tmp/one.rs"], capture_output=True, text=True, timeout=20)
    except subprocess.TimeoutExpired:
        return "hang"
    for line in p.stdout.splitlines():
        if line.startswith("s0"):
            return "verified" if "verified" in line else ("failed" if "FAILED" in line else "skipped")
    return "skipped"


TYPES = [("x: u8", 8, False), ("y: i8", 8, True), ("a: u16", 16, False), ("b: i16", 16, True)]
CMPS = ['==', '<=', '<']


def rand_expr(d, bang=False):
    r = random.random()
    if d == 0 or r < 0.40:
        return ('c', random.choice(LITS))
    if r < 0.62:
        op = random.choice(['-', '!'])
        if op == '!' and not bang:
            op = '-'
        return ('u', op, rand_expr(d - 1, bang))
    return ('b', random.choice(BIN_OPS), rand_expr(d - 1, bang), rand_expr(d - 1, bang))


def main():
    seed = int(os.environ.get("SWEEP_SEED", "101"))
    iters = int(os.environ.get("SWEEP_ITERS", "1500"))
    random.seed(seed)
    over_refusal, wrong_verdict, unsound = [], [], []
    ok = refused_ok = 0
    for _ in range(iters):
        e = rand_expr(2, bang=True)
        if not has_bang(e):
            continue
        estr = rd(e)
        sig, w, signed = random.choice(TYPES)
        var = sig.split(":")[0].strip()
        op = random.choice(CMPS)
        left = random.random() < 0.5
        form = "(%s) %s %s" % (estr, op, var) if left else "%s %s (%s)" % (var, op, estr)
        rok = rustc_ok(sig, form)
        rv = reader(sig, form)
        if rv == "hang":
            unsound.append((sig, form, "HANG"))
            continue
        if not rok:
            if rv == "skipped":
                refused_ok += 1
            else:
                wrong_verdict.append((sig, form, "rustc REJECT but reader=%s" % rv))
            continue
        vv, wr = ev(e, w, signed)
        if wr:
            continue

        def truth(x):
            xs = x - (1 << w) if (signed and (x >> (w - 1)) & 1) else x
            vs = vv - (1 << w) if (signed and (vv >> (w - 1)) & 1) else vv
            a, b = (vs, xs) if left else (xs, vs)
            return {'==': a == b, '<=': a <= b, '<': a < b}[op]

        allt = all(truth(x) for x in range(1 << w))
        if rv == "verified":
            if not allt:
                unsound.append((sig, form, "VERIFIED non-tautology"))
            else:
                ok += 1
        elif rv == "failed":
            if allt:
                wrong_verdict.append((sig, form, "FAILED but tautology"))
            else:
                ok += 1
        else:
            over_refusal.append((sig, form))
    print("seed", seed, "iters", iters)
    print("ok", ok, "refused_ok", refused_ok)
    print("UNSOUND:", len(unsound))
    for s, f, m in unsound[:20]:
        print("   [%s] %s :: %s" % (s, f, m))
    print("WRONG_VERDICT:", len(wrong_verdict))
    for s, f, m in wrong_verdict[:20]:
        print("   [%s] %s :: %s" % (s, f, m))
    print("OVER_REFUSAL (rustc ACCEPT but reader=skipped):", len(over_refusal))
    for s, f in over_refusal[:20]:
        print("   [%s] %s" % (s, f))


main()

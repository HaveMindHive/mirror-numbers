# Three runs s / m / lm (tUrUq, 11-26-2026): "you arent doing it in 3 ways, you are doing it in 2 and missing one entirely".
# s = standard n. m = mirror, offset 11: m = 11 - s (3m = 8s, 4m = 7s, 9s = 2m, 10s = 1m, 11s = 0m).
#   past 11: carried (12s = -1m ...) and per 11-block ((2j+1)*11 - s, block_mirror from standard-mirror-line).
# 0 halves into 000,000,000 (0a,0n,0a); signed -1,0,1.  lm = lake mirror (upside down, going down into scale).
# lm forms tried:
#   A    negatives of the carried m line are divisions of the whole: m = -k -> lm = 1/k   (11-22 rule); m >= 0 stays m
#   B    slide-rule mirror K^2/s, K = 11          (lm(11) = 11, lm(22) = 11/2, lm(1) = 121)
#   B2   K = 11/2 (the m fold point): (121/4)/s = 121/(4s)
#   Cout upside down AND backwards (outside standpoint): sign flip of m = s - 11
#   Cin  upside down only (inside standpoint): 1/(11 - s)
#   D    per-block: Din = 1/bm, Dout = -bm, DB = K_j^2/s with K_j = (2j+1)*11/2 (the block's own fold point)
# A fraction a/b is never reduced (that needs a common divisor); numerator and denominator are each read through the build.
#
# READINGS USED on any candidate or its mirrors (and nothing else):
#   u(x)  unit count, u(2k) = 2u(k), u(2k+1) = 2u(k) + u(k+1), u(1..3) = 1,2,3 (zero: 000,000,000 -> u = 0)
#   L(x)  comma level (width 3^L, steps after the walls 3*2^k); zeros = 3^L - u; imbalance imb = u - x
#   u-decile of x inside its octave; u mod 4 (strand class); ladder bottom 2|3 vs 1|2 (window)
#   R picture k,0,k / k,k+1,k (keeps candidates on odd seats); T picture t,t,t / t,t+1,t / t+1,t,t+1 (flagged: carries the 3-mirror)
#   11-block seat: block_mirror(x) and bm - x (the method's fixed offset 11, used as given)
#   sign / facing of m and lm.
# NO n % r on candidates or their mirrors (other than the fixed constants 11 and the T picture's 3), no gcd, no prime list, no factoring.
# sympy isprime / primerange ONLY build the truth list (which prime is next) for training counts and scoring.
import os, sys, importlib.util, numpy as np
from fractions import Fraction as Fr   # only for the self-check cross-multiply
from collections import Counter, defaultdict
from sympy import isprime, primerange

HERE = os.path.dirname(os.path.abspath(__file__))
def load(name):
    spec = importlib.util.spec_from_file_location(name.replace("-", "_"), os.path.join(HERE, name + "_v1.0_11-26-2026.py"))
    m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m
sml = load("standard-mirror-line"); fl = load("facing-number-line"); df = load("dual-forms")
OUT = open(os.path.join(HERE, "three-runs_v1.0_11-26-2026.txt"), "w")
def pr(*a):
    s = " ".join(str(x) for x in a); print(s); OUT.write(s + "\n"); OUT.flush()

N = 4 * 1_000_200 + 8                                    # B2 reads the denominator 4s
u = np.zeros(N + 2, dtype=np.int64); u[1:4] = [1, 2, 3]
for n in range(4, N + 2):
    k = n >> 1; u[n] = 2 * u[k] if n & 1 == 0 else 2 * u[k] + u[k + 1]
dec = np.zeros(N + 2, dtype=np.int64); a = 1
while 2 ** a < N + 2:
    lo, hi = 2 ** a, min(2 ** (a + 1), N + 2)
    dec[lo:hi] = np.argsort(np.argsort(u[lo:hi], kind="stable"), kind="stable") * 10 // (hi - lo); a += 1
idx = np.arange(N + 2)
bl = np.array([int(x).bit_length() for x in idx])
Lv = np.zeros(N + 2, dtype=np.int64)                    # comma level: smallest l with 3*2^(l-1) >= x
for l in range(1, 25): Lv[(Lv == 0) & (3 * 2 ** (l - 1) >= idx) & (idx >= 1)] = l
lad = (idx < 3 * (2 ** np.maximum(bl - 2, 0))).astype(np.int64)  # 1 = ladder bottom 2|3 (power up to wall), 0 = 1|2

def build(x):
    """Build readings of one whole number x >= 0 (0 = 000,000,000 = 0a,0n,0a)."""
    x = abs(int(x))
    if x == 0: return dict(u=0, L=0, zeros=9, imb=0, R="0,0,0", T="0,0,0")
    return dict(u=int(u[x]), L=int(Lv[x]), zeros=3 ** int(Lv[x]) - int(u[x]), imb=int(u[x]) - x,
                R=sml.pic(sml.R(x)), T=sml.pic(sml.T(x)))

def lm_forms(s):
    """Each lm form as (numerator, denominator, sign); denominator 0 = the infinity end."""
    m, bm = 11 - s, sml.block_mirror(s)
    j = s // 11 if s % 11 else s // 11 - 1
    return {"A": (m, 1, 1) if m >= 0 else (1, -m, 1), "B": (121, s, 1), "B2": (121, 4 * s, 1),
            "Cout": (abs(m), 1, 1 if s >= 11 else -1), "Cin": (1, abs(m), 1 if m > 0 else -1),
            "Din": (1, bm, 1), "Dout": (bm, 1, -1), "DB": ((2 * j + 1) ** 2 * 121, 4 * s, 1)}

def val(f):
    """Shown unreduced (reducing needs a common divisor): numerator / denominator as built."""
    a, b, sg = f
    return "inf" if b == 0 else f"{sg * a}" if b == 1 else f"{sg * a}/{b}"

# ---------- self-checks ----------
assert [11 - n for n in (8, 7, 9, 10, 11, 12)] == [3, 4, 2, 1, 0, -1]           # 3m = 8s, 4m = 7s, 9s = 2m, 10s = 1m, 11s = 0m, 12s = -1m
same = lambda f, x: f[0] * x.denominator == f[1] * x.numerator     # cross-multiply, no reduction
assert same(lm_forms(11)["B"], Fr(11)) and same(lm_forms(22)["B"], Fr(11, 2)) and same(lm_forms(1)["B"], Fr(121))
assert val(lm_forms(22)["A"]) == "1/11" and val(lm_forms(12)["A"]) == "1" and val(lm_forms(11)["Cin"]) == "inf"
assert build(0)["zeros"] == 9 and build(0)["u"] == 0
for n in range(1, 600): assert fl.B(n).count("1") == u[n] and len(fl.B(n)) == 3 ** Lv[n]
for n in range(1, 5000):
    a_, b_, _ = df.r_top(n); assert df.value(a_, b_, 2) == n
for s in range(12, 200000):          # A, Cout, Cin all read the same build (|s - 11|); Din, Dout, DB read bm / s
    assert lm_forms(s)["A"][1] == lm_forms(s)["Cin"][1] == lm_forms(s)["Cout"][0] == s - 11
# B2's denominator: u(4s) = 4u(s), the same build read two zoom levels up
assert (u[4 * np.arange(1, 1_000_200)] == 4 * u[np.arange(1, 1_000_200)]).all()

# ---------- 1. the 1..200 triple table ----------
pr("== 1. s, m (carried), bm (per-block), lm forms, with build readings, n = 1..200 (P = prime) ==")
pr("cols: s P | u imb R T | m | bm u(bm) R(bm) | A B B2 Cout Cin Din Dout DB | u(den A)  u(den B2)")
for s in range(1, 201):
    b, f, bm = build(s), lm_forms(s), sml.block_mirror(s)
    lmv = " ".join(f"{k}={val(f[k])}" for k in ("A", "B", "B2", "Cout", "Cin", "Din", "Dout", "DB"))
    pr(f"{s:3d}s {'P' if isprime(s) else ' '} u{b['u']:4d} imb{b['imb']:4d} R {b['R']:<11s} T {b['T']:<10s}| {11-s:4d}m | bm {bm:3d} "
       f"u{build(bm)['u']:4d} R {build(bm)['R']:<11s}| {lmv} | {build(f['A'][1] if f['A'][1] != 1 else f['A'][0])['u']} {int(u[4*s])}")

# ---------- 2. small-range look: prime share by reading of the triple (odd s in 13..200, after the first block) ----------
pr("\n== 2. prime share of odd s by one reading of the lm component, odd s in [13, 200] and [1e5, 1e6) ==")
def share(fn, rng):
    hit, tot = Counter(), Counter()
    for c in rng: k = fn(c); tot[k] += 1; hit[k] += isprime(c) if c < 1000 else (c in Pset)
    return ", ".join(f"{k}:{hit[k]}/{tot[k]}" if tot[k] < 1000 else f"{k}:{hit[k]/tot[k]:.4f}" for k in sorted(tot))
P = list(primerange(3, 1_000_300)); Pset = set(P)
readings = {"u(s-11) mod 4 [A,C]": lambda c: int(u[c - 11] & 3), "ladder(s-11) [A,C]": lambda c: int(lad[c - 11]),
            "u-decile(s-11) [A,C]": lambda c: int(dec[c - 11]), "u(bm) mod 4 [D]": lambda c: int(u[sml.block_mirror(c)] & 3),
            "ladder(bm) [D]": lambda c: int(lad[sml.block_mirror(c)]), "bm - s (11-block seat) [D]": lambda c: sml.block_mirror(c) - c,
            "u-decile(4s) [B2]": lambda c: int(dec[4 * c])}
for name, fn in readings.items():
    pr(f"  {name}\n     small: {share(fn, range(13, 201, 2))}\n     1e5-1e6: {share(fn, range(100001, 1000000, 2))}")

# ---------- 3. seat pointer rules from the triple (no candidate test, the rule names one seat) ----------
pr("\n== 3. seat pointers: does one mirror of p name the next prime q? (p in 5..200 / [1e3,1e6)) ==")
def bm_next(p):
    b = sml.block_mirror(p)
    return b if b > p else sml.block_mirror(p + 11)       # block mirror ahead of p (next block if this one points back)
pointers = {"q = bm(p) ahead": bm_next, "q = 22 - p mirror of the next block edge": lambda p: (p // 11 + 1) * 22 - p,
            "q = p + |m| step (lm A as a step)": lambda p: p + abs(11 - p) if p != 11 else 13}
for name, fn in pointers.items():
    sm = [(p, q) for p, q in zip(P, P[1:]) if 5 <= p <= 200]
    bg = [(p, q) for p, q in zip(P, P[1:]) if 1000 <= p < 1_000_000]
    pr(f"  {name}: small {sum(fn(p) == q for p, q in sm)}/{len(sm)}  big {sum(fn(p) == q for p, q in bg)/len(bg):.4f}"
       f"   small hits: {[p for p, q in sm if fn(p) == q][:20]}")

# ---------- 4. next-prime naming with the triple's readings, per band ----------
pr("\n== 4. next-prime naming accuracy (train on even 500-blocks, test on odd ones) ==")
GMAX = 120
base = lambda c: (int(Lv[c]), int(dec[c]), int(u[c] & 3), int(lad[c]))
def H(x): return (int(dec[x]), int(u[x] & 3), int(lad[x]), int(Lv[x]))
def Tsh(x):
    t = sml.T(x); return 0 if t[0] == t[1] else 1 if t[1] > t[0] else 2
VARS = {
    "s only (halving)":            lambda c: base(c),
    "s + T(s) (baseline B)":       lambda c: base(c) + (Tsh(c),),
    "s + lm A/C: H(s-11)":         lambda c: base(c) + H(c - 11),
    "s + lm B2: H(4s)":            lambda c: base(c) + (int(dec[4 * c]),),
    "s + lm D: H(bm)":             lambda c: base(c) + H(sml.block_mirror(c)),
    "s + lm D: 11-seat bm-s":      lambda c: base(c) + (sml.block_mirror(c) - c,),
    "s + T(s) + lm A/C":           lambda c: base(c) + (Tsh(c),) + H(c - 11),
    "s + T(s) + 11-seat":          lambda c: base(c) + (Tsh(c), sml.block_mirror(c) - c),
    "T(s) only":                   lambda c: (Tsh(c),),
    "T(s) + 11-seat (no s halving)": lambda c: (Tsh(c), sml.block_mirror(c) - c),
    "s + T(s) + 11-seat + H(bm)":  lambda c: base(c) + (Tsh(c), sml.block_mirror(c) - c) + H(sml.block_mirror(c)),
}
bands = [(1000, 10000), (10000, 100000), (100000, 1000000)]
for lo, hi in bands:
    test = [(p, q) for p, q in zip(P, P[1:]) if lo <= p < hi and (p // 500) % 2]
    tr = [(p, q) for p, q in zip(P, P[1:]) if lo <= p < hi and not (p // 500) % 2]
    mode = Counter(q - p for p, q in tr).most_common(1)[0][0]
    byf = {f: Counter(q - p for p, q in tr if Tsh(p) == f).most_common(1)[0][0] for f in (1, 2)}
    line = [f"band [{lo},{hi}) n={len(test)}: mode gap {mode} {sum(q-p == mode for p, q in test)/len(test):.4f}",
            f"facing {sum(q-p == byf[Tsh(p)] for p, q in test)/len(test):.4f}"]
    for name, fv in VARS.items():
        hit, tot = Counter(), Counter()
        for c in range(lo | 1, hi + GMAX, 2):
            if (c // 500) % 2: continue
            f = fv(c); tot[f] += 1; hit[f] += c in Pset
        bs = sum(hit.values()) / sum(tot.values())
        sc = lambda f: (hit[f] + 2 * bs) / (tot[f] + 2)
        ok = 0
        for p, q in test:
            best, bg, surv = -1, 2, 1.0
            for g in range(2, GMAX + 1, 2):
                v = sc(fv(p + g)); w = surv * v
                if w > best: best, bg = w, g
                surv *= 1 - v
            ok += bg == q - p
        line.append(f"{name} {ok/len(test):.4f}")
    pr("\n   ".join(line))

# ---------- 5. generic check: is it 11, or any fixed block mirror? same rule T(s) + seat in an O-block ----------
pr("\n== 5. generic check: T(s) + O-block seat ((2j+1)*O - s) - s, for other fixed offsets O ==")
def bseat(c, O):
    j = c // O if c % O else c // O - 1
    return (2 * j + 1) * O - 2 * c
for lo, hi in bands[1:]:
    test = [(p, q) for p, q in zip(P, P[1:]) if lo <= p < hi and (p // 500) % 2]
    row = []
    for O in (7, 9, 10, 11, 12, 13, 15, 22, 30):
        fv = lambda c: (Tsh(c), bseat(c, O))
        hit, tot = Counter(), Counter()
        for c in range(lo | 1, hi + GMAX, 2):
            if (c // 500) % 2: continue
            f = fv(c); tot[f] += 1; hit[f] += c in Pset
        bs = sum(hit.values()) / sum(tot.values()); ok = 0
        for p, q in test:
            best, bg, surv = -1, 2, 1.0
            for g in range(2, GMAX + 1, 2):
                v = (hit[fv(p + g)] + 2 * bs) / (tot[fv(p + g)] + 2); w = surv * v
                if w > best: best, bg = w, g
                surv *= 1 - v
            ok += bg == q - p
        row.append(f"O={O}: {ok/len(test):.4f}")
    pr(f"  band [{lo},{hi}): " + "  ".join(row))
OUT.close()

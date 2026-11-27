# Build-only next-prime predictor (tUrUq, 11-26-2026).
# READINGS USED (and nothing else) for any candidate c = p+g, centre m = p+g/2, the evens c-1, c+1, and the known prime p:
#   u(n)            unit count, u(2k)=2u(k), u(2k+1)=2u(k)+u(k+1), u(1..3)=1,2,3
#   L(n), 3^L       width / comma level (steps after the walls 3*2^k)
#   zeros = 3^L - u, imbalance imb = u - n, u-decile of n inside its octave (where its count sits among neighbours)
#   centre digit    (lit centre)
#   u mod 4         (the strand class: odd = lit centre strand, 2 mod 4 = wall strand)
#   ladder bottom   2|3 or 1|2 (which window n sits in)
#   R picture       k,0,k (hinge) or k,k+1,k (filled): only used to keep g even (odd candidates)
#   T picture       t,t,t / t,t+1,t / t+1,t,t+1 (VARIANT B only; it carries the 3-mirror, flagged as such)
# NO n % r on candidates, no gcd, no prime list, no isprime on candidates inside the predictor.
# sympy isprime/primerange are used ONLY to make the truth list (which prime is next) for training counts and scoring.
import sys, os, numpy as np
from collections import Counter, defaultdict
from sympy import primerange, isprime
HERE = os.path.dirname(os.path.abspath(__file__))
OUT = open(os.path.join(HERE, "build-only-predictor_v1.0_11-26-2026.txt"), "w")
def pr(*a):
    s = " ".join(str(x) for x in a); print(s); OUT.write(s + "\n"); OUT.flush()

N = 2_300_000
u = np.zeros(N + 2, dtype=np.int64); u[1:4] = [1, 2, 3]
for n in range(4, N + 2):
    k = n >> 1; u[n] = 2 * u[k] if n % 2 == 0 else 2 * u[k] + u[k + 1]   # build recursion (parity = R picture)

# u-decile inside its octave [2^a, 2^(a+1)): where n's unit count sits among its octave neighbours (u/n alone grows with size)
dec = np.zeros(N + 2, dtype=np.int8)
a = 1
while 2 ** a < N + 2:
    lo, hi = 2 ** a, min(2 ** (a + 1), N + 2)
    r = np.argsort(np.argsort(u[lo:hi], kind="stable"), kind="stable"); dec[lo:hi] = r * 10 // (hi - lo); a += 1

def L(n):
    l = 1
    while 3 * 2 ** (l - 1) < n: l += 1
    return l

def ladder_bottom(n):
    k = n // 2
    while k + 1 > 3: k //= 2
    return (k, k + 1)

def T_shape(n):            # his T picture top: which of the three turn pictures (VARIANT B only)
    t, r = divmod(n, 3)
    return "ttt" if r == 0 else "t,t+1,t" if r == 1 else "t+1,t,t+1"

from functools import lru_cache
@lru_cache(maxsize=None)
def feats(n, variant):
    f = (L(n), int(dec[n]), int(u[n] & 3), ladder_bottom(n), (u[n] & 1) == 1)
    if variant == "B": f += (T_shape(n),)
    if variant == "C": f += (int(dec[n - 1]), int(dec[n + 1]))   # the evens either side
    return f

# ---------- self-checks against the imported build ----------
sys.path.insert(0, HERE)
import importlib.util
spec = importlib.util.spec_from_file_location("fl", os.path.join(HERE, "facing-number-line_v1.0_11-26-2026.py"))
fl = importlib.util.module_from_spec(spec); spec.loader.exec_module(fl)
for n in range(1, 600):
    s = fl.B(n); assert s.count("1") == u[n] and len(s) == 3 ** L(n)
assert u[7] + u[11] == 2 * u[9] == 30 and (27 - u[7]) + (27 - u[11]) == 24

# ---------- 1. exact identities ----------
pr("== 1. Exact identities (build readings only) ==")
# D(m,h) = u(m-h) + u(m+h) - 2u(m)
# gap 2 (m = 2k): D = d(k-1) + u(k+1) > 0, d(x) = 2u(x) - u(x+1)  -> never 0
for k in range(3, 200000):
    m = 2 * k; assert u[m - 1] + u[m + 1] - 2 * u[m] == (2 * u[k - 1] - u[k]) + u[k + 1] > 0
# gap 4 (m = 2k+1): D = 2u(k-1) - 3u(k) + u(k+2); D = 0 exactly when m = 8j+5 (j >= 2), plus m = 9 (word 3 = 111)
zero = [m for m in range(5, 400001, 2) if u[m - 2] + u[m + 2] == 2 * u[m]]
assert zero == [9] + [m for m in range(21, 400001, 8)], zero[:10]
pr("gap 2: u(p)+u(q)-2u(m) = d(k-1)+u(k+1) > 0 for every even centre m=2k (k<2e5): never balanced")
pr("gap 4: u(p)+u(q) = 2u(m) exactly when m = 8j+5, j>=2 (21, 29, 37, ...), and m = 9 (checked m < 4e5)")
pr("       9 is the one balance that comes from the word 3 = 111 (the turn root); 13 = 8+5 misses (word region)")
pr("       proof: k = 4j+2 gives u(4j+1)=6u(j)+u(j+1), u(4j+2)=4u(j)+2u(j+1), u(4j+4)=4u(j+1) -> D = 0")
P = list(primerange(5, 2_200_000))
c4 = [(q, (p + q) // 2) for p, q in zip(P, P[1:]) if q - p == 4]
bal = sum(1 for q, m in c4 if u[q - 4] + u[q] == 2 * u[m])
allodd = sum(1 for m in range(21, 2_200_000, 2) if u[m - 2] + u[m + 2] == 2 * u[m]) / len(range(21, 2_200_000, 2))
pr(f"gap-4 prime splits balanced: {bal}/{len(c4)} = {bal/len(c4):.4f}; all odd centres: {allodd:.4f}  (same share: not a prime tell)")
# zeros at a common width: (Z-u(p)) + (Z-u(q)) = 2(Z-u(m)) iff u(p)+u(q) = 2u(m): the same identity
pr("zeros at a common width 3^L: Zp + Zq = 2Zm  <=>  u(p)+u(q) = 2u(m) (width cancels): same law")

# general h: D/u(m) distribution, prime splits vs every odd pair with the same gap and size
pr("\nD/u(m) mean, prime splits vs all odd pairs (same gap, p in [1e5,2e6)):")
for g in (2, 4, 6, 8, 10, 12, 18, 30):
    ps = [(u[p] + u[p + g] - 2 * u[p + g // 2]) / u[p + g // 2] for p, q in zip(P, P[1:]) if q - p == g and p > 1e5]
    al = [(u[a] + u[a + g] - 2 * u[a + g // 2]) / u[a + g // 2] for a in range(100001, 2_000_000, 14)]
    pr(f"  gap {g:2d}: primes {np.mean(ps):+.5f} (n={len(ps)})  all {np.mean(al):+.5f}")

# ---------- 2. predictors ----------
pr("\n== 2. Predict q from p (build readings only) ==")
GMAX = 120
bands = [(1000, 10000), (10000, 100000), (100000, 1000000), (1000000, 2000000)]
Pset = set(P)
def train_s(lo, hi, variant):
    """P(c is the prime | build features of c) counted over odd c in training blocks (block index even)."""
    hit, tot = Counter(), Counter()
    for c in range(lo | 1, hi + GMAX, 2):
        if (c // 500) % 2: continue
        f = feats(c, variant); tot[f] += 1; hit[f] += c in Pset
    base = sum(hit.values()) / sum(tot.values())
    return lambda f: (hit[f] + 2 * base) / (tot[f] + 2)          # light smoothing toward the band mean

def predict(p, s, variant):
    best, bg, surv = -1, 2, 1.0
    for g in range(2, GMAX + 1, 2):                               # even g only: the next odd seat (R picture of p)
        sc = s(feats(p + g, variant)); val = surv * sc
        if val > best: best, bg = val, g
        surv *= 1 - sc
    return bg

def facing(p): return T_shape(p)                                  # p's own T picture: 6k-1 vs 6k+1 facing
res = defaultdict(dict)
for lo, hi in bands:
    test = [(p, q) for p, q in zip(P, P[1:]) if lo <= p < hi and (p // 500) % 2]
    gaps = Counter(q - p for p, q in test)
    res[lo]["n"] = len(test)
    # baseline 1: most common gap for this size (taken from training blocks)
    tr = [(p, q) for p, q in zip(P, P[1:]) if lo <= p < hi and not (p // 500) % 2]
    mode = Counter(q - p for p, q in tr).most_common(1)[0][0]
    res[lo]["mode"] = (mode, sum(q - p == mode for p, q in test) / len(test))
    # baseline 2: best gap per facing of p
    byf = {f: Counter(q - p for p, q in tr if facing(p) == f).most_common(1)[0][0] for f in ("t,t+1,t", "t+1,t,t+1")}
    res[lo]["facing"] = (byf, sum(q - p == byf[facing(p)] for p, q in test) / len(test))
    # his 7|9|11 balance as a rule: first g with u(p)+u(p+g) = 2u(p+g/2), else the mode
    def bal_rule(p):
        for g in range(2, GMAX + 1, 2):
            if u[p] + u[p + g] == 2 * u[p + g // 2]: return g
        return mode
    res[lo]["balance"] = sum(q - p == bal_rule(p) for p, q in test) / len(test)
    for v in ("A", "B", "C"):
        s = train_s(lo, hi, v)
        res[lo][v] = sum(q - p == predict(p, s, v) for p, q in test) / len(test)
    def pkey(p): return (T_shape(p), (p + 1) // 2 % 2 == 0, ladder_bottom(p), int(dec[p]), int(dec[p + 1]), int(u[p] & 3))
    # (p+1)/2 hinge-or-filled = p's own R picture one zoom in (his note: midpoint block even when p = 3 mod 4)
    tab = defaultdict(Counter)
    for p, q in tr: tab[pkey(p)][q - p] += 1
    res[lo]["D"] = sum(q - p == (tab[pkey(p)].most_common(1)[0][0] if tab[pkey(p)] else byf[facing(p)]) for p, q in test) / len(test)
    tab2 = defaultdict(Counter)
    for p, q in tr: tab2[pkey(p)[:2]][q - p] += 1
    res[lo]["D2"] = sum(q - p == tab2[pkey(p)[:2]].most_common(1)[0][0] for p, q in test) / len(test)
    r = res[lo]
    pr(f"band [{lo},{hi}) test primes {r['n']}: mode gap {r['mode'][0]} {r['mode'][1]:.4f} | facing {r['facing'][0]} {r['facing'][1]:.4f}"
       f" | balance rule {r['balance']:.4f} | A (no T) {r['A']:.4f} | B (+T picture) {r['B']:.4f} | C (+evens) {r['C']:.4f}"
       f" | D p-table {r['D']:.4f} | D2 p T+R only {r['D2']:.4f}")

# ---------- 3. what the build features carry: prime share per feature cell (odd c, [1e5, 2e6)) ----------
pr("\n== 3. Prime share of odd c by single build reading, c in [1e5,2e6) ==")
for name, fn in (("u mod 4", lambda c: int(u[c] & 3)), ("ladder bottom", ladder_bottom),
                 ("u-decile", lambda c: int(dec[c])), ("T picture", T_shape),
                 ("u-decile of even c-1", lambda c: int(dec[c - 1])), ("lit centre", lambda c: bool(u[c] & 1))):
    hit, tot = Counter(), Counter()
    for c in range(100001, 2_000_000, 2):
        k = fn(c); tot[k] += 1; hit[k] += c in Pset
    pr(f"  {name}: " + ", ".join(f"{k}: {hit[k]/tot[k]:.4f} (n={tot[k]})" for k in sorted(tot)))

# ---------- 4. the strands: lit-centre and wall-strand seats ----------
lit = [2 ** a + 1 for a in range(3, 21)]; wall = [3 * 2 ** a + 1 for a in range(2, 20)]
pr("\n== 4. Strand seats ==")
pr("  2^a+1 prime:", [n for n in lit if isprime(n)], "  3*2^a+1 prime:", [n for n in wall if isprime(n)])

# ---------- 5. PySR (one job): half gap h from build readings of p ----------
if "--pysr" in sys.argv:
    from pysr import PySRRegressor
    rows = [(p, q) for p, q in zip(P, P[1:]) if 1e5 <= p < 2e6][::40]
    X = np.array([[u[p] / p, L(p), int(u[p] & 3), ladder_bottom(p)[0], u[p + 1] / (p + 1), u[p - 1] / (p - 1),
                   u[(p + 1) // 2] / ((p + 1) // 2)] for p, q in rows], float)
    y = np.array([(q - p) / 2 for p, q in rows], float)
    mdl = PySRRegressor(niterations=30, timeout_in_seconds=150, populations=12, maxsize=15,
                        binary_operators=["+", "-", "*", "/"], output_directory=os.path.join(HERE, "pysr-runs"),
                        run_id="build-only-h", progress=False, verbosity=0, random_state=0, deterministic=True, parallelism="serial")
    mdl.fit(X, y, variable_names=["ur", "L", "u4", "lad", "urp1", "urm1", "urc"])
    pr("\n== 5. PySR h from build readings of p (n=%d, var(h)=%.3f) ==" % (len(y), y.var()))
    pr(mdl.equations_[["complexity", "loss", "equation"]].to_string())
# exact: means of D/u(m) do not move with the centre's 3- or 5-seat (the halving build is blind to the odd mirrors)
aa = np.arange(100001, 2000000, 2); D4 = (u[aa] + u[aa + 4] - 2 * u[aa + 2]) / u[aa + 2]; mm = aa + 2
pr("\nD/u(m), gap 4, all odd m by m's 3-seat:", [round(D4[mm % 3 == r].mean(), 5) for r in range(3)],
   " 5-seat:", [round(D4[mm % 5 == r].mean(), 5) for r in range(5)], "(analysis only, not in the predictor)")
OUT.close()

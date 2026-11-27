# Packed left-outs from his builds (tUrUq, 11-26-2026). Can his builds / mirrors name the "packed" passed places
# (places carrying many DISTINCT blocks) without factoring candidates one by one?
# Reading rule (left-out-selection, unchanged): a read passed place k lays the strands of its blocks; it reaches seat y
# exactly when k and y share a block; name = first place past p no strand reaches. FAIRNESS: every place read <= p
# (asserted); isprime / the answer key below used for scoring and for measuring readings of passed places only.
import importlib.util, os, time
import numpy as np
from sympy import primerange

HERE = os.path.dirname(os.path.abspath(__file__))
def load(f):
    s = importlib.util.spec_from_file_location(f[:8], os.path.join(HERE, f)); m = importlib.util.module_from_spec(s)
    s.loader.exec_module(m); return m
mw = load("missing-wings_v1.0_11-26-2026.py")          # lay_strands: his wing build (open wing w -> seat 2w+1)
sm = load("standard-mirror-line_v1.0_11-26-2026.py")    # block_mirror: per-11-block mirror
sp = load("spine-two-digit-primes_v1.0_11-26-2026.py")  # u(n): spine units; imbalance = u(n) - n
T0 = time.time(); out = []
def pr(*a):
    s = " ".join(map(str, a)); print(s, flush=True); out.append(s)

N = 10 ** 6 + 400
spf = np.zeros(N + 1, dtype=np.int32)
for d in range(2, int(N ** .5) + 1):
    if spf[d] == 0:
        s = spf[d * d::d]; s[s == 0] = d
r_ = np.arange(N + 1, dtype=np.int32); spf[spf == 0] = r_[spf == 0]; spf = spf.tolist()
def blocks(k):
    if k < 4 or spf[k] == k: return ()
    o = []
    while k > 1:
        f = spf[k]; o.append(f)
        while k % f == 0: k //= f
    return o
P = [k for k in range(3, N) if spf[k] == k]
pairs = [(p, q) for p, q in zip(P, P[1:]) if 1000 <= p < 10 ** 6]
BANDS = [(10 ** 3, 10 ** 4), (10 ** 4, 10 ** 5), (10 ** 5, 10 ** 6)]
SEAT = {p: [blocks(y) for y in range(p + 1, q)] for p, q in pairs}

def exact(p, places):
    F = set()
    for k in places:
        assert 4 <= k <= p                                 # fairness: passed places only
        F.update(blocks(k))
    return all(any(f in F for f in b) for b in SEAT[p])  # every gap seat reached -> first open place is q
def score(rule, B):
    res = []
    for a, b in BANDS:
        sub = [pq for pq in pairs if a <= pq[0] < b]
        if a == 10 ** 5: sub = sub[::3]                     # same sampling as left-out-selection
        res.append(sum(exact(p, rule(p, B)) for p, q in sub) / len(sub))
    return res
fmt = lambda x: "/".join(f"{v:.4f}" for v in x)

# ------------------------------------------------ 1. which readings of a passed place track its distinct-block count
pr("== 1. Readings of passed places k in [100000, 140000) vs distinct blocks w(k) (Pearson; Spearman) ==")
hits = mw.lay_strands(70000)                            # strands landing on wing (k-1)/2 for odd k
def rank(a): return np.argsort(np.argsort(a, kind="stable"), kind="stable").astype(float)
K = np.arange(100000, 140000)
w = np.array([len(blocks(int(k))) for k in K], float)
wbig = np.array([sum(f > 31 for f in blocks(int(k))) for k in K], float)
odd = K % 2 == 1
R = {
    "imbalance u-k": np.array([sp.u(int(k)) - k for k in K], float),
    "imbalance per unit (u-k)/k": np.array([(sp.u(int(k)) - k) / k for k in K], float),
    "halving depth (2-adic)": np.array([(int(k) & -int(k)).bit_length() for k in K], float),
    "primorial seat: blocks of 30030 shared": np.array([sum(int(k) % r == 0 for r in (2, 3, 5, 7, 11, 13)) for k in K], float),
    "per-11-block mirror shares a block with k": np.array([np.gcd(int(k), sm.block_mirror(int(k))) > 1 for k in K], float),
    "copies face q (smallest odd centre count, 1 if none)": np.array([next((f for f in blocks(int(k)) if f > 2), 1) for k in K], float),
}
for nm, v in R.items():
    pr(f"  {nm:52s} w: {np.corrcoef(v, w)[0,1]:+.4f}; {np.corrcoef(rank(v), rank(w))[0,1]:+.4f}   blocks>31: {np.corrcoef(v, wbig)[0,1]:+.4f}")
sh = np.array([hits[(k - 1) // 2] for k in K[odd]], float)
pr(f"  {'strand hits on wing (odd k only)':52s} w: {np.corrcoef(sh, w[odd])[0,1]:+.4f}; {np.corrcoef(rank(sh), rank(w[odd]))[0,1]:+.4f}   blocks>31: {np.corrcoef(sh, wbig[odd])[0,1]:+.4f}")
pr("  (faces tau-2 track w by construction; any reading built from divisors is factoring k)")
pr(f"  [{time.time()-T0:.0f}s]")

# ------------------------------------------------ 2. selection rules
_c = {}
def r_last(p, B): return range(p - B, p)
def lim_of(p): n = len(str(p)) - 1; return (p // 10 ** n) * 10 ** n
def r_packed(p, B):                                     # oracle, copied unchanged from left-out-selection
    key = ("o", lim_of(p), B)
    if key not in _c:
        lim = lim_of(p); bins = []
        for r in primerange(2, lim // 2):
            fit = [b for b in bins if b[0] * r <= lim]
            if fit: max(fit, key=lambda b: b[0])[0] *= r
            elif len(bins) < B: bins.append([r])
            else: break
        _c[key] = [b[0] if spf[b[0]] != b[0] else 2 * b[0] for b in bins]
    return _c[key]
OPEN = [2] + [2 * w_ + 1 for w_ in range(1, 70000) if hits[w_] == 0]     # his open seats (no isprime)
assert OPEN[:10] == [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
def r_foldpair(p, B):
    # his build only: open seats from the wing strands, folded end to end (smallest with largest that fits, then
    # the next small block rides along while it still fits). No candidate is factored; places are built, not found.
    key = ("f", lim_of(p), B)
    if key not in _c:
        lim = lim_of(p); seats = [r for r in OPEN if r * 2 <= lim]
        lo, hi, pl = 0, len(seats) - 1, []
        while lo <= hi and len(pl) < B:
            k = seats[hi]; hi -= 1
            while lo <= hi and k * seats[lo] <= lim: k *= seats[lo]; lo += 1
            pl.append(2 * k if spf[k] == k and 2 * k <= lim else k)
        _c[key] = pl
    return _c[key]
def r_foldpair_small(p, B):                             # same fold, but start at the small end: primorial-like seat first
    key = ("s", lim_of(p), B)
    if key not in _c:
        lim = lim_of(p); seats = [r for r in OPEN if r * 2 <= lim]; pl = []; i = 0
        while i < len(seats) and len(pl) < B:
            k = seats[i]; i += 1
            while i < len(seats) and k * seats[i] <= lim: k *= seats[i]; i += 1
            if spf[k] == k:                             # lone block: fold it with the largest open seat that fits
                j = max((j for j in range(i, len(seats)) if k * seats[j] <= lim), default=None)
                if j is not None: k *= seats.pop(j)
                elif 2 * k <= lim: k *= 2
            pl.append(k)
        _c[key] = pl
    return _c[key]
def r_pronic(p, B):                                     # ladder pairs m|m+1 as product places m(m+1) <= p, from the root down
    m = int(p ** .5)
    while m * (m + 1) > p: m -= 1
    return [(m - j) * (m - j + 1) for j in range(B) if m - j >= 2]
def r_pronic_odd(p, B):                                 # odd ladder pairs m|m+2 (both odd), m(m+2) <= p
    m = int(p ** .5) | 1
    while m * (m + 2) > p: m -= 2
    return [(m - 2 * j) * (m - 2 * j + 2) for j in range(B) if m - 2 * j >= 3]
def r_primorial(p, B):                                  # multiples of 30030 (else 2310, 210) at/below p and their mirrors k <-> p - k
    c = 30030 if p >= 30030 * 4 else 2310 if p >= 2310 * 4 else 210
    o = []
    for j in range(p // c, 0, -1):
        o += [j * c]
        if len(o) >= B: break
    return o[:B]
RULES = {"last B window": r_last, "packed oracle": r_packed, "open seats folded, small end first": r_foldpair_small,
         "open seats folded, large end first": r_foldpair, "ladder pairs m(m+1)": r_pronic,
         "primorial-like seat + ladder pairs": lambda p, B: r_foldpair_small(p, 1) + r_pronic(p, B - 1),
         "odd ladder pairs m(m+2)": r_pronic_odd, "primorial seats 30030j": r_primorial}
TAB = {}
pr("\n== 2. Exact naming share 1e3-1e4 / 1e4-1e5 / 1e5-1e6 (every 3rd gap in the top band) ==")
for nm, rule in RULES.items():
    TAB[nm] = {B: score(rule, B) for B in (15, 31, 63, 95)}
    pr(f"  {nm:38s} " + " | ".join(f"B={B}: {fmt(TAB[nm][B])}" for B in (15, 31, 63, 95)))
assert all(sorted(r_foldpair_small(p, B)) == sorted(r_packed(p, B)) for p in (1009, 20011, 100003, 999983) for B in (15, 31, 95))
assert abs(TAB["packed oracle"][15][1] - 0.8902) < 5e-5 and abs(TAB["packed oracle"][31][2] - 0.8442) < 5e-5
pr(f"  [{time.time()-T0:.0f}s]")

# ------------------------------------------------ 3. where the cheap rules fray
pr("\n== 3. Open seats left by the ladder-pair rule (B=31, top band every 9th gap) ==")
from collections import Counter
c = Counter(); n = 0
for p, q in [pq for pq in pairs if pq[0] >= 10 ** 5][::9]:
    F = {f for k in r_pronic(p, 31) for f in blocks(k)}
    for b in SEAT[p]:
        if not any(f in F for f in b):
            n += 1; c[(len(b), "smallest block > 31" if min(b) > 31 else "has block <= 31")] += 1
pr(f"  unreached seats {n}: " + "; ".join(f"{k[0]} blocks, {k[1]}: {v}" for k, v in c.most_common(6)))
pk = r_foldpair_small(999983, 31)
pr(f"  fold small-end B=31 at p=999983: first places {pk[:6]}; largest block laid {max(f for k in pk for f in blocks(k))}")
open(os.path.join(HERE, "packed-from-build_v1.0_11-26-2026.txt"), "w").write("\n".join(out) + "\n")
pr(f"  [{time.time()-T0:.0f}s] done")

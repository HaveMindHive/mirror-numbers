# Left-out selection (tUrUq, 11-26-2026). Which passed places to read for the largest naming gain per place read.
# Builds on left-out-method (LW(L)) and left-out-evens; readings imported, unchanged.
# FAIRNESS: only places <= p are read (their faces / depth / core); isprime only to score.
# Reading rule, same as LW: every face block d of a read left-out k (d | k, 2 <= d <= k/2) lays its strand forward;
# name = first place past p on no strand.
# Reduction used for speed (checked against LW's own strand laying below): a strand of block d from k passes place y
# exactly when d | y, so a read left-out k reaches seat y exactly when k and y share a block (gcd(k, y) > 1);
# a prime place k has no faces and reaches nothing.
import importlib.util, os, time
from collections import Counter
import numpy as np
from sympy import primerange

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("lo", os.path.join(HERE, "left-out-evens_v1.0_11-26-2026.py"))
lo = importlib.util.module_from_spec(spec); spec.loader.exec_module(lo)
T0 = time.time()
N = 10 ** 6 + 400
spf = np.zeros(N + 1, dtype=np.int32)
for d in range(2, int(N ** .5) + 1):
    if spf[d] == 0:
        s = spf[d * d::d]; s[s == 0] = d
r_ = np.arange(N + 1, dtype=np.int32); spf[spf == 0] = r_[spf == 0]
TAU = np.zeros(N + 1, dtype=np.int32)
for d in range(1, N + 1): TAU[d::d] += 1
DEP = np.zeros(N + 1, dtype=np.int32); DEP[1:] = [(k & -k).bit_length() for k in range(1, N + 1)]
SPF_NP = spf.astype(np.int64)
spf = spf.tolist()
def blocks(k):            # distinct prime blocks of place k; empty for a prime place (no faces)
    if k < 4 or spf[k] == k: return ()
    out = []
    while k > 1:
        f = spf[k]; out.append(f)
        while k % f == 0: k //= f
    return out
def faces(k):
    n, t = k, 1
    while n > 1:
        f = spf[n]; e = 0
        while n % f == 0: n //= f; e += 1
        t *= e + 1
    return t - 2
def depth(k): return (k & -k).bit_length()
for k in range(4, 300):
    assert len(lo.even_copy_faces(2 * k)) == max(faces(k), 0) and lo.depth(2 * k)[0] == depth(k)

P = [k for k in range(3, N) if spf[k] == k]
pairs = [(p, q) for p, q in zip(P, P[1:]) if 1000 <= p < 10 ** 6]
BANDS = [(10 ** 3, 10 ** 4), (10 ** 4, 10 ** 5), (10 ** 5, 10 ** 6)]
GAPC = {p: [blocks(y) for y in range(p + 1, q)] for p, q in pairs}    # gap seats (scoring only)

def name(p, places):
    F = set()
    for k in places:
        assert k <= p                                 # fairness
        F.update(blocks(k))
    y = p + 1
    while True:
        b = blocks(y)
        if not b or not any(f in F for f in b): return y
        y += 1

# check the reduction against LW's strand laying (left-out-method lw_brute) on a sample
def lw_brute(p, L):
    struck = set()
    for k in range(max(p - L, 4), p + 1):
        for d in range(2, k // 2 + 1):
            if k % d == 0:
                struck.update(range(k + d, p + 400, d))
    return next(y for y in range(p + 1, p + 400) if y not in struck)
for p, q in pairs[::4001]:
    assert name(p, range(p - 31, p)) == lw_brute(p, 31)

out = []
def pr(*a):
    s = " ".join(str(x) for x in a); print(s, flush=True); out.append(s)

# ---------------------------------------------------------------- selection rules (each returns <= B passed places)
W = 2000                                              # look-back pool for ranked rules
def r_last(p, B): return range(p - B, p)
def r_stride(s): return lambda p, B: [p - s * j for j in range(1, B + 1)]
def r_mirror11(p, B): return [p - 11 * j for j in range(1, B + 1)]
def r_blockmirror11(p, B):                            # per-block mirror (n <-> (2j+1)11 - n) of p in blocks j, j-1 ...
    j, rr = divmod(p, 11); out_ = []
    while len(out_) < B:
        m = 11 * j + (11 - rr if rr else 0)
        if m <= p and m >= 4: out_.append(m)
        j -= 1
    return out_
def r_ranked(arr):
    cache = {}
    def f(p, B):
        if p not in cache:
            ks = np.arange(p - 1, p - W - 1, -1)          # nearest first; stable sort keeps nearest on ties
            cache[p] = ks[np.argsort(-arr[ks], kind="stable")[:63]].tolist()
        return cache[p][:B]
    return f
def r_flank(p, B):                                    # flank place p-1, then the places on its own blocks back from it
    k0 = p - 1; out_ = [k0]
    ds = sorted(d for d in range(2, k0 // 2 + 1) if k0 % d == 0) if k0 < 5000 else None
    if ds is None:
        ds = sorted({d for f in blocks(k0) for d in (f,)} | {k0 // f for f in blocks(k0)})
    m = 1
    while len(out_) < B:
        for d in ds:
            if len(out_) >= B: break
            k = k0 - m * d
            if k not in out_: out_.append(k)
        m += 1
    return out_[:B]
def r_strand(p, B):                                   # nearest passed left-out on each block's strand (blocks not yet laid)
    F = set(); out_ = []
    for r in primerange(2, p):
        if len(out_) >= B: break
        if r in F: continue
        k = r * (p // r)
        if k == r: k = 0
        if k < 4: continue
        out_.append(k); F.update(blocks(k))
    return out_
_pack_cache = {}
def r_packed(p, B):                                   # square-free cores behind p: products of unlaid blocks <= lim <= p
    n = len(str(p)) - 1; lim = (p // 10 ** n) * 10 ** n     # leading-digit floor of p, so every place read is passed
    key = (lim, B)
    if key not in _pack_cache:
        bins = []
        for r in primerange(2, lim // 2):
            fit = [b for b in bins if b[0] * r <= lim]
            if fit: max(fit, key=lambda b: b[0])[0] *= r          # best fit
            elif len(bins) < B: bins.append([r])
            else: break
        _pack_cache[key] = [b[0] if spf[b[0]] != b[0] else 2 * b[0] for b in bins]   # a lone prime place has no faces: read 2r
    return _pack_cache[key]

RULES = {
    "last B (= LW, = p-d small d)": r_last,
    "deepest B (pool 2000)": r_ranked(DEP),
    "most-faced B (pool 2000)": r_ranked(TAU),
    "flank 2(p-1) + its blocks": r_flank,
    "mirror p-11j": r_mirror11,
    "per-11-block mirror": r_blockmirror11,
    "stride 2": r_stride(2), "stride 3": r_stride(3), "stride 6": r_stride(6),
    "nearest on each block's strand": r_strand,
    "packed square-free cores": r_packed,
}
BUD = (7, 15, 31, 63)
STEP = 3                                              # top band: every 3rd gap (22,969 of 68,906); lower bands: all

def score(rule, B, sel=None):
    res = []
    for a, b in BANDS:
        sub = [pq for pq in pairs if a <= pq[0] < b]
        if sel is not None: sub = [pq for pq in sub if sel(pq)]
        elif a == 10 ** 5: sub = sub[::STEP]
        hit = 0
        for p, q in sub:
            y = name(p, rule(p, B)); assert y <= q        # misses fall short of q
            hit += y == q
        res.append(hit / len(sub))
    return res

pr("== Left-out selection: exact naming share by band (1e3-1e4 all / 1e4-1e5 all / 1e5-1e6 every 3rd gap) ==")
pr("reference LW(L), full bands (left-out-method): L=31 0.8172/0.6208/0.5116; L=100 1.0/0.8218/0.6481; L=300 1.0/0.9998/0.8154; R4(31) 0.7832/0.6031/0.4971")
TAB = {}
for nm, rule in RULES.items():
    for B in BUD:
        TAB[(nm, B)] = score(rule, B)
    pr(f"  {nm:32s} " + " | ".join(f"B={B}: " + "/".join(f"{x:.4f}" for x in TAB[(nm, B)]) for B in BUD))
assert abs(TAB[("last B (= LW, = p-d small d)", 31)][1] - 0.6208) < 5e-5   # reproduces LW(31) on the full 1e4-1e5 band
pr(f"  [{time.time()-T0:.0f}s]")

# ---------------------------------------------------------------- greedy offsets, train / test halves
pr("\n== Greedy: fixed offsets d (read place p-d), added one at a time; train = even-index gaps in 1e5-1e6 (sample), test = odd-index ==")
top = [pq for pq in pairs if pq[0] >= 10 ** 5]
train = top[0::2][::12]; test = top[1::2]
D = 400
def covmat(sub):
    M = max(q - p - 1 for p, q in sub)
    ys = np.zeros((len(sub), M), dtype=np.int64); mask = np.zeros((len(sub), M), bool)
    for i, (p, q) in enumerate(sub):
        for j, y in enumerate(range(p + 1, q)): ys[i, j] = y; mask[i, j] = True
    ps = np.array([p for p, q in sub], dtype=np.int64)
    ks = ps[:, None] - np.arange(1, D + 1)[None, :]
    kprime = SPF_NP[ks] == ks
    C = np.zeros((len(sub), M, D), bool)
    for c in range(0, D, 25):
        C[:, :, c:c + 25] = (np.gcd(ks[:, None, c:c + 25], ys[:, :, None]) > 1) & ~kprime[:, None, c:c + 25] & mask[:, :, None]
    return C, mask
C, mask = covmat(train)
unc = mask.copy(); chosen = []
for step in range(63):
    left = unc[:, :, None] & ~C                        # seats still open if d is added
    exact = (~left.any(axis=1)).sum(axis=0)
    seats = (unc[:, :, None] & C).sum(axis=(0, 1))
    sc = exact * 10 ** 6 + seats; sc[[d - 1 for d in chosen]] = -1
    d = int(np.argmax(sc)) + 1; chosen.append(d); unc &= ~C[:, :, d - 1]
pr("  greedy offsets in order:", chosen)
GREEDY = {}
for B in BUD:
    offs = chosen[:B]
    res = []
    for a, b in BANDS:
        sub = [pq for pq in (pairs if a < 10 ** 5 else test) if a <= pq[0] < b][:: (1 if a < 10 ** 5 else 2)]
        res.append(np.mean([name(p, [p - d for d in offs]) == q for p, q in sub]))
    GREEDY[B] = res
    pr(f"  greedy B={B}: " + "/".join(f"{x:.4f}" for x in res) + "  (top band = test half, every 2nd)")
pr(f"  [{time.time()-T0:.0f}s]")

# ---------------------------------------------------------------- what the chosen places are
pr("\n== What the best places are ==")
for B in (15, 31):
    offs = sorted(chosen[:B])
    pr(f"  greedy first {B} offsets sorted: {offs}")
    pr(f"    offsets that are multiples of 11: {[d for d in offs if d % 11 == 0]}; d <= 31: {sum(d <= 31 for d in offs)}")
pp = 500009                                           # an example prime
for B in (15, 31):
    pk = r_packed(pp, B)
    pr(f"  packed cores B={B} (top band): {pk[:8]} ... blocks laid up to {max(max(blocks(k)) for k in pk if blocks(k))}; depth of each <= {max(depth(k) for k in pk)}")
    st = r_strand(pp, B)
    pr(f"  nearest-on-strand B={B} at p={pp}: offsets behind p {[pp - k for k in st][:12]} ...; largest block laid {max(f for k in st for f in blocks(k))}")
# blocks laid per place read, top band, B = 31
for nm in ("last B (= LW, = p-d small d)", "most-faced B (pool 2000)", "deepest B (pool 2000)", "nearest on each block's strand", "packed square-free cores"):
    s = [len({f for k in RULES[nm](p, 31) for f in blocks(k)}) for p, q in top[::200]]
    pr(f"  distinct blocks laid with 31 places, {nm}: mean {np.mean(s):.1f}")

# ---------------------------------------------------------------- oddity: where LW misses, what the open seat is
pr("\n== Where reads fray: the open seat that LW(31) wrongly names (top band, every 3rd) ==")
cnt = Counter(); n = 0
for p, q in top[::3]:
    y = name(p, range(p - 31, p))
    if y != q:
        n += 1; b = blocks(y); cnt[("two blocks" if len(b) == 2 else f"{len(b)} blocks", "both > 31" if min(b) > 31 else "has <= 31")] += 1
        cnt["smallest block over sqrt(p)/2"] += min(b) > (p ** .5) / 2
pr(f"  misses {n}: " + "; ".join(f"{k}: {v}" for k, v in cnt.most_common()))
# the proven point: laying every block r with r*r <= q names q exactly (each place before q carries a block <= its root)
for p, q in top[::997]:
    assert name(p, [r * (p // r) for r in primerange(2, int((2 * p) ** .5) + 1) if r * (p // r) >= 4]) == q
pr("  check: reading the nearest passed left-out on every block r with r*r <= 2p names q exactly (asserted on a sample; the same fact reached by a different route)")
pr(f"  [{time.time()-T0:.0f}s]")
pr("\n== Larger budgets for the two block-led rules (where exact arrives) ==")
for nm in ("packed square-free cores", "nearest on each block's strand", "last B (= LW, = p-d small d)"):
    for B in (95, 127, 191):
        x = score(RULES[nm], B); TAB[(nm, B)] = x
        pr(f"  {nm:32s} B={B}: " + "/".join(f"{v:.4f}" for v in x))
assert TAB[("packed square-free cores", 191)] == [1.0, 1.0, 1.0]
STEP = 1
for B in (63, 95):
    x = score(RULES["packed square-free cores"], B)
    pr(f"  packed square-free cores B={B}, FULL top band (all 68,906 gaps): " + "/".join(f"{v:.4f}" for v in x))
assert score(RULES["packed square-free cores"], 95) == [1.0, 1.0, 1.0]
pk = r_packed(100003, 95); pr(f"  packed B=95 at p=100003 (lim 1e5, thinnest case): blocks up to {max(f for k in pk for f in blocks(k))} laid (sqrt(2p) = {int((2*100003)**.5)})")
pk = r_packed(999983, 191); pr(f"  packed B=191 at p=999983: {len(pk)} places, every block up to {max(f for k in pk for f in blocks(k))} laid (sqrt(2p) = {int((2*999983)**.5)})")
pr(f"  [{time.time()-T0:.0f}s]")
open(os.path.join(HERE, "left-out-selection_v1.0_11-26-2026.txt"), "w").write("\n".join(out) + "\n")

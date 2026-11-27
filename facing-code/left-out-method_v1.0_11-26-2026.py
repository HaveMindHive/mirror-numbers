# Left-out method (tUrUq, 11-26-2026). Even line: place k at 2k (2 is the 1). Even primes = prime places
# (4, 6, 10, 14, 22 ...). Left-outs = composite places: 2k with k = 4, 6, 8, 9, 10 ... (8, 12, 16, 18, 20 ...).
# Readings of a left-out 2k: depth (halvings to the odd core) = 1 + halvings of k; core = odd part of k;
# faces = ways 2k folds into >= 2 equal copies of an even block 2d >= 4 (d | k, 2 <= d <= k/2).
# FAIRNESS for naming the next even prime 2q above 2p: only places <= p (passed) may be read, plus p's own faces.
# isprime / nextprime only to score.
import importlib.util, os
from collections import Counter, defaultdict
import numpy as np
from sympy import isprime, nextprime

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("lo", os.path.join(HERE, "left-out-evens_v1.0_11-26-2026.py"))
lo = importlib.util.module_from_spec(spec); spec.loader.exec_module(lo)   # his left-out readings, unchanged

N = 10 ** 6 + 400                                  # places k (even line to 2N)
tau = np.zeros(N + 1, dtype=np.int32)
for d in range(1, N + 1): tau[d::d] += 1
spf = np.zeros(N + 1, dtype=np.int32)
for d in range(2, int(N ** .5) + 1):
    if spf[d] == 0:
        s = spf[d * d::d]; s[s == 0] = d
r = np.arange(N + 1, dtype=np.int32); spf[spf == 0] = r[spf == 0]
def divisors(k):
    ds = [1]
    while k > 1:
        f = int(spf[k]); e = 0
        while k % f == 0: k //= f; e += 1
        ds = [a * f ** i for a in ds for i in range(e + 1)]
    return ds
def depth(k): return (k & -k).bit_length()        # halvings of 2k = 1 + halvings of k
def core(k): return k // (k & -k)
def faces(k): return int(tau[k]) - 2               # equal even-copy faces of 2k (k composite: >= 1)

# the readings match his left-out code
for k in range(2, 400):
    d, c = lo.depth(2 * k)
    assert d == depth(k) and c == core(k) and len(lo.even_copy_faces(2 * k)) == faces(k)

P = [k for k in range(3, N) if tau[k] == 2]
pairs = [(p, q) for p, q in zip(P, P[1:]) if p >= 5 and p < 10 ** 6]
assert all(nextprime(p) == q for p, q in pairs[:3000])
BANDS = [(5, 10 ** 3), (10 ** 3, 10 ** 4), (10 ** 4, 10 ** 5), (10 ** 5, 10 ** 6)]
def band(p): return next(i for i, (a, b) in enumerate(BANDS) if a <= p < b)
out = []
def pr(*a):
    s = " ".join(str(x) for x in a); print(s); out.append(s)

# ---------------------------------------------------------------- 1. the gap seen from its left-outs
pr("== 1. Gap profile from the left-outs (even primes 2p|2q, p = 5 .. 1e6, n =", len(pairs), ") ==")
pr("places k inside the gap: p+1 .. q-1. Left-out 2k: depth 1 = missing seat (k odd), depth 2+ = 4k left-out (k even)")
deep_at_centre = Counter(); deep_tot = Counter()
fp = defaultdict(list); fq = defaultdict(list)      # faces at offset j from 2p and from 2q
core_prime = Counter(); core_tot = Counter()
faces_by_depth = defaultdict(list)
for p, q in pairs:
    g = q - p; m = (p + q) // 2
    ins = range(p + 1, q)
    kd = max((k for k in ins if k % 2 == 0), key=depth)      # deepest 4k left-out (unique in a run)
    deep_tot[g] += 1; deep_at_centre[g] += kd == m
    for k in ins:
        fp[(g, k - p)].append(faces(k)); fq[(g, q - k)].append(faces(k))
        if k % 2 == 0:
            c = core(k); core_tot["gap"] += 1; core_prime["gap"] += c > 1 and tau[c] == 2
            faces_by_depth[depth(k)].append(faces(k))
for g in (2, 4, 6, 8, 10, 12, 14, 18, 30):
    pr(f"  gap {g:2d} (even gap {2*g:2d}): deepest 4k left-out sits at the centre in {deep_at_centre[g]} of {deep_tot[g]} ({deep_at_centre[g]/deep_tot[g]:.4f})")
for g in (6, 12, 18):
    row = [f"{np.mean(fp[(g, j)]):.2f}" for j in range(1, g)]
    pr(f"  gap {g}: mean faces of left-out at place p+j, j=1..{g-1}: {' '.join(row)}")
# compare with all composite places
allk = np.arange(10 ** 5, 10 ** 6)
comp = allk[tau[allk] > 2]
pr(f"  mean faces of any left-out, places 1e5..1e6: {np.mean(tau[comp] - 2):.3f}; of left-outs at p+1 / q-1 (same band):",
   f"{np.mean([faces(p+1) for p,q in pairs if p>=1e5]):.3f} / {np.mean([faces(q-1) for p,q in pairs if p>=1e5]):.3f}")
ev = allk[allk % 2 == 0]; cs = ev // (ev & -ev)
for dd in (2, 3, 4, 5, 6):
    pr(f"  4k left-outs at depth {dd} inside gaps: {len(faces_by_depth[dd])}, mean faces {np.mean(faces_by_depth[dd]):.3f}")

# the left-out flanks: 2p sits between left-outs 2(p-1), 2(p+1); every face block d of a flank keeps both its
# neighbours off d. Seats beside a 4k left-out whose core carries 3 (k = 0 mod 6): every 2p, p >= 5.
assert all((p - 1) % 6 == 0 or (p + 1) % 6 == 0 for p, q in pairs)

# ---------------------------------------------------------------- 2. naming the next even prime (fair)
pr("\n== 2. Naming 2q from 2p (fair: only places <= p are read) ==")
def lw_name(p, L):
    """Left-out window: lay the strands of every face of the passed places p-L .. p forward; name the first
    place past p on no strand. Block d is laid when a passed place k in the window carries it (d | k, 2d <= k)."""
    lo_k = max(p - L, 4)
    y = p + 1
    while True:
        hit = False
        for d in divisors(y):
            if d < 2 or d == y: continue
            k = d * (p // d)                         # nearest passed place carrying block d
            if k >= lo_k and k >= 2 * d: hit = True; break
        if not hit: return y
        y += 1
# the shortcut above equals laying strands forward from the window (checked on a sample)
def lw_brute(p, L):
    struck = set()
    for k in range(max(p - L, 4), p + 1):
        for d in divisors(k):
            if 2 <= d <= k // 2:
                for y in range(k + d, p + 600, d): struck.add(y)
    return next(y for y in range(p + 1, p + 600) if y not in struck)
for p, q in pairs[::997]:
    for L in (3, 31):
        assert lw_name(p, L) == lw_brute(p, L)

LS = (7, 31, 100, 300)
res = [Counter() for _ in BANDS]
for p, q in pairs:
    r = res[band(p)]; r["n"] += 1
    for L in LS:
        yl = lw_name(p, L); assert yl <= q              # a prime seat carries no face, so no strand lands on it: misses fall short of q (checked to 1e6)
        r[f"LW({L})"] += yl == q
        y = p + 1                                    # small blocks only: strands of d = 2 .. L+1
        while any(d <= L + 1 for d in divisors(y)[1:-1]): y += 1
        r[f"SB({L})"] += y == q
        r[f"gain({L})"] += (yl == q) - (y == q)
        r[f"loss({L})"] += (y == q) and (yl != q)
names = ["facing p mod 6", "depth+facing p mod 12", "p mod 24", "p mod 60 (2,3,5 seats)", "faces of 2(p-1) + p mod 12"]
for bi, (a, b) in enumerate(BANDS):
    sub = [(p, q) for p, q in pairs if a <= p < b]
    keys = [lambda p: p % 6, lambda p: p % 12, lambda p: p % 24, lambda p: p % 60, lambda p: (p % 12, min(faces(p - 1), 30))]
    for nm, kf in zip(names, keys):
        tab = defaultdict(Counter)
        for p, q in sub: tab[kf(p)][q - p] += 1
        best = {k: c.most_common(1)[0][0] for k, c in tab.items()}
        res[bi][nm] = sum(q - p == best[kf(p)] for p, q in sub)
    runs = [(q - p) // 2 - 1 for p, q in sub if (q - p) // 2 - 1 >= 2]
    res[bi]["rand"] = sum(1 / k for k in runs) / len(runs)
assert all(r["facing p mod 6"] == r["depth+facing p mod 12"] for r in res[1:])   # the depth axis adds nothing
R4 = {1: .7832, 2: .6031, 3: .4971}                    # asymmetric-tell R4(31), same pairs
for bi, ((a, b), r) in enumerate(zip(BANDS, res)):
    n = r["n"]
    pr(f"band [{a},{b}) n={n}: random centre {r['rand']:.4f}" + (f" | R4(31) {R4[bi]:.4f}" if bi in R4 else ""))
    pr("   in-band best gap per class (reads p only): " + "; ".join(f"{nm} {r[nm]/n:.4f}" for nm in names))
    pr("   left-out window LW(L) (reads L places behind p, 0 past p): " + "; ".join(f"L={L} {r[f'LW({L})']/n:.4f}" for L in LS))
    pr("   LW over SB, net gaps gained by the large faces of window places: " + "; ".join(f"L={L} +{r[f'gain({L})']} (lost {r[f'loss({L})']})" for L in LS))
    pr("   small blocks only SB(L) (strands of d <= L+1): " + "; ".join(f"L={L} {r[f'SB({L})']/n:.4f}" for L in LS))

# ---------------------------------------------------------------- 3. seeing the prime seats from left-outs
pr("\n== 3. Seeing prime seats: flag both neighbours of a 4k left-out by its blocks ==")
pr("rule S(B): a 4k left-out 2k whose place k carries every block in B flags places k-1, k+1 as prime seats")
for B, nm in (((2,), "2 (any 4k)"), ((2, 3), "2,3"), ((2, 3, 5), "2,3,5"), ((2, 3, 5, 7), "2,3,5,7")):
    M = int(np.prod(B))
    for a, b in BANDS[1:]:
        ks = np.arange(((a // M) + 1) * M, b, M)
        flagged = np.unique(np.concatenate([ks - 1, ks + 1])); flagged = flagged[(flagged >= a) & (flagged < b)]
        hit = int(np.sum(tau[flagged] == 2)); allp = sum(1 for k in range(a, b) if tau[k] == 2)
        pr(f"  S({nm}) band [{a},{b}): flagged {len(flagged)}, prime {hit}: precision {hit/len(flagged):.4f}, recall {hit/allp:.4f}")
# faces of the flank: precision of the seat next to a 4k left-out by its face count (place k even, seat k+1)
pr("  by the flank's face count (seat k+1 beside 4k left-out 2k, band [1e5,1e6)):")
ks = np.arange(10 ** 5, 10 ** 6, 2); fc = tau[ks] - 2; pk = tau[ks + 1] == 2
for lo_, hi_ in ((2, 6), (6, 10), (10, 14), (14, 22), (22, 40), (40, 1000)):
    sel = (fc >= lo_) & (fc < hi_)
    pr(f"    faces {lo_}-{hi_-1}: {int(sel.sum())} flanks, seat prime {np.mean(pk[sel]):.4f}")

# ---------------------------------------------------------------- 4. oddity: 8 is to 4 as 10 is to 5 (tower of lines)
pr("\n== 4. Tower: line a holds place k at 2^a k. 8 = place 2 of line 2, as 4 = place 2 of line 1 ==")
pr("(core prime share rises with depth only because the core is smaller: k / 2^a)")
pr("every left-out 2k with k even is a place of line 2+; its core is its place on its deepest line")
cnt = Counter(); tot = Counter()
for p, q in pairs:
    if p < 10 ** 5: continue
    for k in range(p + 1, q):
        if k % 2: continue
        c = core(k); tot[depth(k)] += 1; cnt[depth(k)] += (c > 1 and tau[c] == 2) or c == 1
for dd in sorted(tot)[:8]:
    pr(f"  4k left-outs in gaps, band [1e5,1e6), deepest line {dd}: {tot[dd]}, core prime (a tower prime) {cnt[dd]/tot[dd]:.4f}")

open(os.path.join(HERE, "left-out-method_v1.0_11-26-2026.txt"), "w").write("\n".join(out) + "\n")

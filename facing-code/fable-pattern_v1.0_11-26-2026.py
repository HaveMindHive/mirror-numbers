# Fable pattern run (tUrUq's mirror method, 11-26-2026). Author of the method: Turaq Rayn-McLean.
# Question: the common RELATIONSHIP of a prime split and each family's own sequence; and how stacking his maps
# closes the RANGE in which the next prime q sits, measured by band as the number of candidate seats that hold
# q in 90% / 99% of splits.
# FAIRNESS: a candidate seat y > p is never tested for divisibility or primality. What may be read:
#   * p itself (its facing on 2, 3, 4 = p mod 12),
#   * passed places k <= p (their blocks), whose strands are LAID forward (his construction),
#   * the primes below the band (their gap record) as the "rule of how the primes change".
# isprime / the prime list is used only to score (where q really is).
# Strands are his construction laid from read places; nothing is tested at the seat.
import math, time, os, sys
from collections import Counter, defaultdict
import numpy as np
from sympy import primerange, primefactors

T0 = time.time()
HERE = os.path.dirname(os.path.abspath(__file__))
OUT = []
def pr(*a):
    s = " ".join(str(x) for x in a); print(s, flush=True); OUT.append(s)

N = 10 ** 6 + 2000
H_MAX = 200                                    # half gaps 1..200 (gap <= 400; largest gap below 1e6 is 114)
BANDS = [(10 ** 3, 10 ** 4), (10 ** 4, 10 ** 5), (10 ** 5, 10 ** 6)]

# ---------------------------------------------------------------- primes and splits
is_p = np.ones(N + 1, dtype=bool); is_p[:2] = False
for d in range(2, int(N ** .5) + 1):
    if is_p[d]: is_p[d * d::d] = False
P = np.flatnonzero(is_p)
SPLITS = [(int(p), int(q)) for p, q in zip(P, P[1:]) if 5 <= p < 10 ** 6]

# ---------------------------------------------------------------- 1. the hand-off law (exact, all splits 5..1e6)
def hand_off(p, q):
    m, h = (p + q) // 2, (q - p) // 2
    return ((m % 2 == 0) != (h % 2 == 0)) and ((m % 3 == 0) != (h % 3 == 0)) and (h % 3 != p % 3)
assert all(hand_off(p, q) for p, q in SPLITS)
# no mirror r >= 5 through both centre and half gap
for p, q in SPLITS[::97]:
    m, h = (p + q) // 2, (q - p) // 2
    assert math.gcd(m, h) == 1
pr("HAND-OFF LAW (exact on all %d splits 5 <= p < 1e6): exactly one of centre m, half gap h is even; exactly one is on the"
   " 3-mirror; gcd(m, h) = 1 (no mirror r through both); h mod 3 != p mod 3 (read from p alone)." % len(SPLITS))

# ---------------------------------------------------------------- 2. families: p mod 12 (facing on 3 x side on 4)
pr("\nFAMILIES (p mod 12 = facing on the 3-mirror x side on the 4-mirror). Allowed half-gap classes h mod 6 and the"
   " observed sequence of the top gaps per band (share of the family's splits).")
fam_allowed = {1: (0, 2, 3, 5), 7: (0, 2, 3, 5), 5: (0, 1, 3, 4), 11: (0, 1, 3, 4)}
for p, q in SPLITS:
    assert ((q - p) // 2) % 6 in fam_allowed[p % 12]
for lo, hi in BANDS:
    for f in (1, 5, 7, 11):
        gaps = Counter(q - p for p, q in SPLITS if lo <= p < hi and p % 12 == f)
        n = sum(gaps.values())
        top = ", ".join(f"{g}:{c / n:.3f}" for g, c in gaps.most_common(6))
        keep = sum(c for g, c in gaps.items() if g % 12 == 0) / n
        pr(f"  band [{lo},{hi}) family p=12k+{f:<2} n={n:6d}  h mod 6 in {fam_allowed[f]}  top gaps {top}  (gap mult of 12, keeps"
           f" facing and side: {keep:.3f})")

# ---------------------------------------------------------------- 3. laid blocks (his construction, from passed places)
# Reading budget B = number of passed places read. Packed cores (small end first): each read place is a product of
# consecutive primes that still fits below p; B places lay the first R(B) primes as blocks. 2 and 3 come from p's seat.
def laid_bound(p, B):
    """largest block laid by B packed passed places below p (0 places -> blocks 2, 3 from p's facing only)."""
    r_list = [int(r) for r in P[:400]]
    i, places = 2, 0          # start after 2, 3
    last = 3
    while places < B and i < len(r_list):
        c = 1
        while i < len(r_list) and c * r_list[i] <= p:
            c *= r_list[i]; last = r_list[i]; i += 1
        if c == 1: break      # next block alone exceeds p
        places += 1
    return last
assert laid_bound(1000, 0) == 3 and laid_bound(1000, 1) == 11            # 5*7*11 = 385 is one passed place below 1000
assert laid_bound(10 ** 6, 1) == 17                                      # 2*3*5*7*11*13*17 = 510510

# per-threshold arrays: reached[y] (y has a block <= R, y > R), hits[y] = number of distinct blocks <= R of y
THRESH = sorted({laid_bound(lo, B) for lo, hi in BANDS for B in (0, 1, 3, 7, 15, 31, 63, 95)})
pr("\nBlock thresholds R used (largest block laid):", THRESH)
HITS = {}
for R in THRESH:
    hits = np.zeros(N + 1, dtype=np.int16)
    for r in P[P <= R]:
        hits[int(r)::int(r)] += 1
    HITS[R] = hits
pr(f"[{time.time() - T0:.1f}s] tables ready")

# ---------------------------------------------------------------- 4. gap weights (his gap-mirror formula #17) and family rule
def M(g):
    w = 1.0
    for r in primefactors(g):
        if r > 2: w *= (r - 1) / (r - 2)
    return w
HS = np.arange(1, H_MAX + 1)
MG = np.array([M(2 * h) for h in HS])

def learned_weights(lo):
    """rule of how the primes change, read from the primes below the band: gap counts per family p mod 12."""
    W = {f: np.zeros(H_MAX) for f in (1, 5, 7, 11)}
    for p, q in SPLITS:
        if p >= lo: break
        if (q - p) // 2 <= H_MAX: W[p % 12][(q - p) // 2 - 1] += 1
    return W

# ---------------------------------------------------------------- 5. the maps, stacked; rank of the true seat
def rank_of_true(scores, alive, h_true):
    """1 + number of alive candidates ranked before the true one (ties broken by smaller h first)."""
    s = scores[h_true - 1]
    before = alive & ((scores > s) | ((scores == s) & (HS < h_true)))
    return 1 + int(before.sum())

def run_band(lo, hi, B, mode, W=None):
    R = laid_bound(lo, B)
    hits = HITS[R]
    ranks = []
    for p, q in SPLITS:
        if p < lo: continue
        if p >= hi: break
        h_true = (q - p) // 2
        if h_true > H_MAX: continue
        ys = p + 2 * HS                       # candidate seats q = p + 2h
        ms = p + HS                           # candidate centres
        alive = (ys % 3 != 0) if B == 0 else (hits[ys] == 0)       # facing on 3 (B=0) or unreached by laid strands
        if mode == "walk":
            scores = -HS.astype(float)
        elif mode == "weights":
            scores = MG * np.exp(-2 * HS / math.log(p))
        elif mode == "family":
            scores = W[p % 12] + 1e-9 * MG * np.exp(-2 * HS / math.log(p))
        elif mode == "centre":               # NEW: divisor-rich centres carry the structure; rank by the centre's laid hits
            scores = MG * np.exp(-2 * HS / math.log(p)) * (1 + hits[ms])
        elif mode == "centre_broke":         # NEW + the broken side: the even half q-1 of q's wing pair, hits read too
            scores = MG * np.exp(-2 * HS / math.log(p)) * (1 + hits[ms]) * (1 + hits[ys - 1])
        else:
            raise ValueError(mode)
        assert alive[h_true - 1]              # q is never struck: misses fall short, never past q
        ranks.append(rank_of_true(scores, alive, h_true))
    ranks = np.array(ranks)
    return len(ranks), int(np.percentile(ranks, 90, method="higher")), int(np.percentile(ranks, 99, method="higher")), ranks.mean(), (ranks == 1).mean(), R

pr("\nRANGE CLOSING. Range = number of candidate seats, in the map's order, that hold q for 90% / 99% of the band's splits"
   " (also mean rank and share named first). B = passed places read (0 = p's own facing only).")
hdr = f"{'map (stacked)':<42}{'B':>4}{'R':>5} | {'[1e3,1e4) 90/99 mean first':>28} | {'[1e4,1e5) 90/99 mean first':>28} | {'[1e5,1e6) 90/99 mean first':>28}"
pr(hdr)
TABLE = {}
def row(label, B, mode):
    cells = []
    for lo, hi in BANDS:
        W = learned_weights(lo) if mode == "family" else None
        n, r90, r99, mean, first, R = run_band(lo, hi, B, mode, W)
        TABLE[(label, B, lo)] = (r90, r99, mean, first)
        cells.append(f"{r90:4d}/{r99:4d} {mean:6.2f} {first:.3f}")
    pr(f"{label:<42}{B:>4}{laid_bound(10**5, B):>5} | " + " | ".join(f"{c:>28}" for c in cells))

# baseline: bare walk over every integer = the gap itself
for lo, hi in BANDS:
    g = np.array([q - p for p, q in SPLITS if lo <= p < hi])
    h = g // 2
    TABLE[("bare", lo)] = (int(np.percentile(g, 90, method="higher")), int(np.percentile(g, 99, method="higher")), g.mean())
    TABLE[("walker", lo)] = (int(np.percentile(h, 90, method="higher")), int(np.percentile(h, 99, method="higher")), h.mean())
pr(f"{'bare walk, every integer (gap itself)':<42}{'-':>4}{'-':>5} | " + " | ".join(f"{TABLE[('bare', lo)][0]:4d}/{TABLE[('bare', lo)][1]:4d} {TABLE[('bare', lo)][2]:6.2f}      " for lo, hi in BANDS))
pr(f"{'mirror at the walker (seats walked = h)':<42}{'-':>4}{'-':>5} | " + " | ".join(f"{TABLE[('walker', lo)][0]:4d}/{TABLE[('walker', lo)][1]:4d} {TABLE[('walker', lo)][2]:6.2f}      " for lo, hi in BANDS))
row("hand-off (2,3 from p), walk up", 0, "walk")
row("+ gap weights M(g) exp(-g/L)", 0, "weights")
row("+ family rule learned below the band", 0, "family")
row("+ NEW centre-rich (laid hits at centre)", 0, "centre")
row("+ NEW centre-rich + broken side (q-1)", 0, "centre_broke")
for B in (1, 3, 7, 15, 31, 63, 95):
    row(f"strands of {B} packed passed places, walk", B, "walk")
    row(f"  same + gap weights", B, "weights")
    row(f"  same + NEW centre-rich + broken side", B, "centre_broke")
pr(f"[{time.time() - T0:.1f}s] range table done")

# ---------------------------------------------------------------- 6. the new idea, checked on its own: centres vs random seats
pr("\nNEW IDEA CHECK: does the centre of a split carry more laid blocks than a seat picked at random in the same gap?")
for lo, hi in BANDS:
    R = laid_bound(lo, 7); hits = HITS[R]
    c_hits, o_hits, n = 0, 0, 0
    for p, q in SPLITS:
        if p < lo: continue
        if p >= hi: break
        if q - p < 4: continue
        m = (p + q) // 2
        others = [y for y in range(p + 1, q) if y != m]
        c_hits += int(hits[m]); o_hits += float(hits[others].mean()); n += 1
    pr(f"  band [{lo},{hi}) blocks <= {R}: mean hits at the centre {c_hits / n:.4f} vs other seats in the gap {o_hits / n:.4f}  (n={n})")

# ---------------------------------------------------------------- 7. the asymmetry as a number: the 4-side swap (his broken side)
pr("\nASYMMETRY (the 4-side): the hand-off allows h even (side kept, q = p mod 4) and h odd (side swapped) alike;"
   " measured share of splits that keep the side, per family and band (0.5 would be even-handed).")
for lo, hi in BANDS:
    cells = []
    for f in (1, 5, 7, 11):
        hs = [((q - p) // 2) % 2 == 0 for p, q in SPLITS if lo <= p < hi and p % 12 == f]
        cells.append(f"12k+{f}: {sum(hs) / len(hs):.4f}")
    allk = [((q - p) // 2) % 2 == 0 for p, q in SPLITS if lo <= p < hi]
    pr(f"  band [{lo},{hi}) side kept  " + "  ".join(cells) + f"  all: {sum(allk) / len(allk):.4f}")
# facing kept (h mult of 3) per band
for lo, hi in BANDS:
    allk = [((q - p) // 2) % 3 == 0 for p, q in SPLITS if lo <= p < hi]
    pr(f"  band [{lo},{hi}) facing kept (gap mult of 6): {sum(allk) / len(allk):.4f}  (two of the four allowed h classes keep it)")

# where it frays: misses of the strand maps are seats made of two large blocks (never past q)
pr("\nWHERE IT FRAYS: in [1e5,1e6) with 31 places read, the seats ranked before q are survivors made only of blocks above R.")
R = laid_bound(10 ** 5, 31); hits = HITS[R]
two_big = Counter()
for p, q in SPLITS[::25]:
    if not (10 ** 5 <= p < 10 ** 6): continue
    for y in range(p + 2, q, 2):
        if y % 3 and hits[y] == 0:
            two_big[len(primefactors(y))] += 1
pr(f"  surviving seats before q (1 in 25 splits sampled), by number of blocks: {dict(sorted(two_big.items()))}  (R={R})")

with open(os.path.join(HERE, "fable-pattern_v1.0_11-26-2026.txt"), "w") as f:
    f.write("\n".join(OUT) + "\n")
pr(f"[{time.time() - T0:.1f}s] saved fable-pattern_v1.0_11-26-2026.txt")

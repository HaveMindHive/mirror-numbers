# Asymmetric tell (tUrUq, 11-26-2026). Gap between consecutive prime seats p|q read as the triple h, m, h
# (half gap, centre, half gap): 7|11 -> 2,9,2; 23|29 -> 3,26,3. Read the left side (m-j) against the right
# side (m+j) as mirror pairs: which blocks land on each missing seat (his strands), turn faces, wing pairs.
# Blocks of an odd seat n = 2w+1: the strands landing on wing w (block d lands when d | n, 3 <= d <= n/3).
# Primes come from laying strands (open wings); isprime/nextprime only for asserts and scoring.
import importlib.util, os, math
from collections import Counter
from sympy import isprime, nextprime

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("mw", os.path.join(HERE, "missing-wings_v1.0_11-26-2026.py"))
mw = importlib.util.module_from_spec(spec); spec.loader.exec_module(mw)

N = 10 ** 6
W = N // 2 + 200
hits = mw.lay_strands(W)                      # his construction, imported unchanged
blocks = [[] for _ in range(W + 1)]           # the block list per wing (same strands, kept by name)
m = 3
while m + (m - 1) // 2 <= W:
    for w in range(m + (m - 1) // 2, W + 1, m): blocks[w].append(m)
    m += 2
def B(n): return blocks[n // 2] if n % 2 else None   # odd seat -> its blocks; even = hinge seat
open_w = [w for w in range(1, W + 1) if hits[w] == 0]
P = [2 * w + 1 for w in open_w]
pairs = [(p, q) for p, q in zip(P, P[1:]) if p >= 5 and q <= N]
assert all(isprime(p) for p in P[:3000]) and all(nextprime(p) == q for p, q in pairs[:3000])

def face(n):  # turn face: equal-copy picture of n (k copies of k = square, cube = k copies of a square face)
    r = round(n ** (1 / 3))
    cube = any(x ** 3 == n for x in (r - 1, r, r + 1))
    sq = math.isqrt(n) ** 2 == n
    return "sq+cube" if sq and cube else "square" if sq else "cube" if cube else "other"
BANDS = [(5, 10 ** 3), (10 ** 3, 10 ** 4), (10 ** 4, 10 ** 5), (10 ** 5, 10 ** 6)]
def band(p): return next(i for i, (a, b) in enumerate(BANDS) if a <= p < b)
out = []
def pr(*a):
    s = " ".join(str(x) for x in a); print(s); out.append(s)

pr("== 1. Mirror pairs across the centre (consecutive primes 5 <= p < q <= 1e6, n =", len(pairs), ") ==")
same_set = shared = mpairs = 0; cen_link = cen_tot = 0; minmax = 0
side = Counter(); fc = Counter(); sqside = Counter(); hinge = Counter(); h_seat_ok = 0
for p, q in pairs:
    h = (q - p) // 2; c = p + h
    # centre seat fixes the half-gap seat
    ok = (h % 2 != c % 2) and ((c % 3 == 0 and h % 3 != 0) or (c % 3 != 0 and h % 3 == 0))
    h_seat_ok += ok
    L = R = 0
    for j in range(1, h):
        a, b = c - j, c + j
        if a % 2:                              # mirrored missing seats (both odd, both inside the gap)
            mpairs += 1
            Ba, Bb = B(a), B(b)
            assert Ba and Bb
            minmax += Ba[0] * Ba[-1] == a and Bb[0] * Bb[-1] == b
            same_set += Ba == Bb
            sh = set(Ba) & set(Bb)
            shared += bool(sh)
            g = math.gcd(c, j)                 # a block crosses the mirror only through the centre
            cen_tot += bool(sh); cen_link += bool(sh) and all(c % d == 0 and j % d == 0 for d in sh)
            L += len(Ba); R += len(Bb)
    side["right busier" if R > L else "left busier" if L > R else "level"] += 1
    fc[(face(c - 1), face(c + 1))] += 1
    for j in range(1, h):
        for n, sd in ((c - j, "L"), (c + j, "R")):
            if face(n) != "other": sqside[face(n) + ("-odd" if n % 2 else "-even") + sd] += 1
    # wing pairs: q's pair (q-1, q) has its even half inside the gap; p's pair (p-1, p) sits outside
    hinge["even centre pairs right" if c % 2 == 0 else "odd centre pairs left"] += 1
pr(f"centre seat fixes the half-gap seat: {h_seat_ok} of {len(pairs)}")
pr(f"mirrored missing seats: {mpairs}; identical block sets: {same_set}; smallest block x largest block = the seat: {minmax} of {mpairs}")
pr(f"mirror pairs sharing at least one block: {shared} ({shared/mpairs:.4f}); shared blocks that are blocks of the centre and of j: {cen_link} of {cen_tot}")
pr("strand totals left side vs right side:", dict(side))
pr("wing-pair lean:", dict(hinge))
pr("odd squares / cubes inside gaps, left of centre vs right:", dict(sqside))
pr("faces beside the centre (m-1, m+1), non-'other' only:", {k: v for k, v in fc.items() if k != ("other", "other")})
assert same_set == 0 and minmax == mpairs and h_seat_ok == len(pairs) and cen_link == cen_tot

pr("\n== 2. Forward naming from p ==")
# R0 walk: lay seats p+1, p+2, ... until the first open seat (short-range construction). Cost q-p numbers.
# R1 mirror at the walker: standing at x, reflect the laid strands through x; p's mirror 2x-p is on a reflected
#     strand iff some block lands on 2x-p. Name q = 2x-p at the first x where p's mirror is open. Laid: x-p.
DS = (3, 7, 13, 23, 31)
res = [Counter() for _ in BANDS]
for p, q in pairs:
    bi = band(p); r = res[bi]; r["n"] += 1; r["walk_cost"] += q - p
    # R1
    x = p + 1
    while hits[(2 * x - p) // 2]: x += 1
    r["R1"] += 2 * x - p == q; r["R1_cost"] += x - p; r["R1_centre"] += x == (p + q) // 2
    # R4(D): blocks known = odd d <= max(D, x-p) (small strands laid behind p plus every strand that must cross
    # the laid window p-(x-p) .. x); stop at the first x where the first clear seat y > x has y <= 2x-p; name y.
    for D in DS:
        x = p
        while True:
            x += 1
            if x == q: y = q; break
            y = x + 1 if x % 2 == 0 else x + 2
            while any(y % d == 0 for d in range(3, max(D, x - p) + 1, 2)): y += 2
            if y <= 2 * x - p: break
        k = f"R4({D})"; r[k] += y == q; r[k + "_cost"] += x - p; r[k + "_centre"] += x == (p + q) // 2
# baseline: guess by p's 6-facing (best gap per facing, fit on the same band)
for bi, (a, b) in enumerate(BANDS):
    sub = [(p, q) for p, q in pairs if a <= p < b]
    best = {f: Counter(q - p for p, q in sub if p % 6 == f).most_common(1)[0][0] for f in (1, 5)}
    res[bi]["facing"] = sum(q - p == best[p % 6] for p, q in sub)
    # random centre in a run of 2+ missing wings: pick one missing wing at random, rate = mean 1/(h-1)
    runs = [(q - p) // 2 - 1 for p, q in sub if (q - p) // 2 - 1 >= 2]
    res[bi]["rand"] = sum(1 / k for k in runs) / len(runs)
for (a, b), r in zip(BANDS, res):
    n = r["n"]
    pr(f"band [{a},{b}) n={n}: facing guess {r['facing']/n:.4f} | random centre (runs 2+) {r['rand']:.4f}")
    pr(f"   R1 mirror at walker: exact {r['R1']/n:.4f}, stops at centre {r['R1_centre']/n:.4f}, laid {r['R1_cost']/r['walk_cost']:.4f} of walk")
    for k in [f"R4({D})" for D in DS]:
        pr(f"   {k} window tell: exact {r[k]/n:.4f}, stops at centre {r[k+'_centre']/n:.4f}, laid {r[k+'_cost']/r['walk_cost']:.4f} of walk")
assert all(r["R1"] == r["n"] for r in res)
open(os.path.join(HERE, "asymmetric-tell_v1.0_11-26-2026.txt"), "w").write("\n".join(out) + "\n")

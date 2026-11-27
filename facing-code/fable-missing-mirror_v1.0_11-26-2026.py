# Fable, second run (tUrUq's correction, 11-26-2026): the missing mirror in the side-flip reading.
# Author of the method: Turaq Rayn-McLean. His cue: "it flips far more often" = flips are being missed; take the
# opposite of every reading. Previous run read the 4-side flip per START family only (keep 0.47 after 6k+1,
# 0.29-0.38 after 6k-1) and treated it as a fact about the family.
# FAIRNESS in the range table: a seat y > p is never tested; only p (its facing), passed places <= p (strands
# laid forward) and primes below the band (the rule of change) are read. isprime scores only.
import math, time, os
from collections import Counter, defaultdict
from fractions import Fraction as Fr
import numpy as np

T0 = time.time()
HERE = os.path.dirname(os.path.abspath(__file__))
OUT = []
def pr(*a):
    s = " ".join(str(x) for x in a); print(s, flush=True); OUT.append(s)

N = 10 ** 6 + 2000
H_MAX = 200
BANDS = [(10 ** 3, 10 ** 4), (10 ** 4, 10 ** 5), (10 ** 5, 10 ** 6)]
is_p = np.ones(N + 1, dtype=bool); is_p[:2] = False
for d in range(2, int(N ** .5) + 1):
    if is_p[d]: is_p[d * d::d] = False
P = np.flatnonzero(is_p)
SPLITS = [(int(p), int(q)) for p, q in zip(P, P[1:]) if 5 <= p < 10 ** 6]
FAM = lambda n: 1 if n % 6 == 1 else -1          # +1 = first off-seat of its 6-block (6k+1), -1 = last (6k-1)

# ---------------------------------------------------------------- 1. the wall frame: (w, s) instead of (h)
# Every seat off 2 and 3 is 6a+1 or 6a+5. A hop p -> q crosses w = b - a walls (multiples of 6 inside the gap)
# and steps s = (r_q - r_p)/4 in {-1, 0, +1} between the two seats of a block. Then h = 3w + 2s.
def wall_frame(p, q):
    a, rp, b, rq = p // 6, p % 6, q // 6, q % 6
    return b - a, (rq - rp) // 4
for p, q in SPLITS:
    w, s = wall_frame(p, q)
    h = (q - p) // 2
    assert h == 3 * w + 2 * s
    assert (w % 2 == 1) == ((q - p) % 4 == 2)        # side flips  <=> odd number of walls crossed
    assert (s != 0) == (q % 3 != p % 3)              # facing flips <=> seat step
    assert w == sum(1 for y in range(p + 1, q) if y % 6 == 0) or q - p > 60
    assert not (p % 6 == 5 and w == 0)               # the last seat of a block cannot hop without a wall
pr("WALL FRAME (exact on all %d splits 5 <= p < 1e6): h = 3w + 2s with w = walls (multiples of 6) crossed, s = seat step"
   " (+1: 6k+1 -> 6k+5, -1: 6k+5 -> 6k+7, 0: same seat). The 4-side flips exactly when w is odd; the 3-facing flips"
   " exactly when s != 0. The two flips are two coordinates of the hop, not of the family." % len(SPLITS))
pr("THE MISSING MIRROR: the old reading counted side flips by START family. w = 0 (no wall) exists only for the first"
   " seat 6k+1 (the cousin hop, gap 4); the last seat 6k-1 must cross a wall. Counted from the END seat, w = 0 exists"
   " only into 6k-1. Neither family owns the flip: the hop does.")

pr("\n(s, w) TABLE per family, shares of the family's hops (band [1e5,1e6)); side kept = w even, facing kept = s = 0.")
lo, hi = BANDS[2]
for f in (1, -1):
    hops = [(wall_frame(p, q)) for p, q in SPLITS if lo <= p < hi and FAM(p) == f]
    n = len(hops); C = Counter(hops)
    cells = []
    for w in range(0, 7):
        cells.append(f"w={w}: " + " ".join(f"s={s:+d} {C[(w, s)] / n:.3f}" for s in (-1, 0, 1) if C[(w, s)]))
    pr(f"  family 6k{f:+d} n={n}: " + " | ".join(cells))
    keep = sum(c for (w, s), c in C.items() if w % 2 == 0) / n
    pr(f"    side kept (w even) {keep:.4f};  w=0 share {C[(0, 1)] / n + C[(0, 0)] / n + C[(0, -1)] / n:.4f};"
       f"  facing kept (s=0) {sum(c for (w, s), c in C.items() if s == 0) / n:.4f}")

# ---------------------------------------------------------------- 2. exact balance: flips out = flips in
pr("\nEXACT BALANCE (the prime walk is one path, so what leaves a class comes back):")
for lo, hi in BANDS + [(5, 10 ** 6)]:
    hops = [(p, q) for p, q in SPLITS if lo <= p < hi]
    s_plus = sum(1 for p, q in hops if wall_frame(p, q)[1] == 1)
    s_minus = sum(1 for p, q in hops if wall_frame(p, q)[1] == -1)
    up = sum(1 for p, q in hops if p % 4 == 1 and q % 4 == 3)
    down = sum(1 for p, q in hops if p % 4 == 3 and q % 4 == 1)
    assert abs(s_plus - s_minus) <= 1 and abs(up - down) <= 1
    T = Counter((p % 12, q % 12) for p, q in hops)
    io = {a: sum(T[(a, b)] for b in (1, 5, 7, 11)) - sum(T[(b, a)] for b in (1, 5, 7, 11)) for a in (1, 5, 7, 11)}
    assert all(abs(v) <= 1 for v in io.values())
    pr(f"  [{lo},{hi}): facing flips 6k+1->6k-1 {s_plus} vs 6k-1->6k+1 {s_minus} (diff {s_plus - s_minus});"
       f"  side flips 1->3 mod 4 {up} vs 3->1 {down} (diff {up - down});  in - out per class mod 12 {io}")
pr("  So each family flips its facing exactly as often as the other (to within 1), and each 4-side flips as often as"
   " the other. The lopsided number was the side flip read by start family only.")

# ---------------------------------------------------------------- 3. direction x family: forward from f vs backward into f
pr("\nDIRECTION x FAMILY: share with the side kept, reading forward from the start seat's family and backward into the"
   " end seat's family (p mod 12 / q mod 12). The per-block mirror 6a+r <-> 6a+6-r keeps every seat's 4-side"
   " (1 = 5 mod 4) and keeps w; it swaps families and direction: 'forward from f' pairs with 'backward into -f'.")
for lo, hi in BANDS:
    hops = [(p, q) for p, q in SPLITS if lo <= p < hi]
    fwd = {f: [((q - p) % 4 == 0) for p, q in hops if p % 12 == f] for f in (1, 5, 7, 11)}
    bwd = {f: [((q - p) % 4 == 0) for p, q in hops if q % 12 == f] for f in (1, 5, 7, 11)}
    pr(f"  band [{lo},{hi})  forward from  " + "  ".join(f"{f:2d}: {sum(v) / len(v):.4f}" for f, v in fwd.items()))
    pr(f"  band [{lo},{hi})  backward into " + "  ".join(f"{f:2d}: {sum(v) / len(v):.4f}" for f, v in bwd.items())
       + "   (pairs: fwd 1 <-> bwd 11, fwd 5 <-> bwd 7, fwd 7 <-> bwd 5, fwd 11 <-> bwd 1)")
# the exact part and the approximate part of that pairing
pr("  Exact part: the facing-flipping hops (s != 0) forward from 6k+1 ARE the hops backward into 6k-1 (same pairs)."
   " Approximate part: same-seat hops 6k+1 -> 6k+1 vs 6k-1 -> 6k-1, by walls w (gap 6w), counts to 1e6:")
C11 = Counter(wall_frame(p, q)[0] for p, q in SPLITS if p % 6 == 1 and q % 6 == 1)
C55 = Counter(wall_frame(p, q)[0] for p, q in SPLITS if p % 6 == 5 and q % 6 == 5)
pr("    " + "  ".join(f"w={w}: {C11[w]} / {C55[w]}" for w in range(1, 9)) + f"  (all w: {sum(C11.values())} / {sum(C55.values())})")

# ---------------------------------------------------------------- 4. the per-block mirror cell by cell: where the counts differ
pr("\nPER-BLOCK MIRROR cell by cell (to 1e6): 6k+1's hop (s=+1, w) has gap 6w+4; its mirror 6k-1's hop (s=-1, w) has gap"
   " 6w-4. Same walls, same side rule, the hop is 8 shorter. Counts N(6w+4) / N(6w-4):")
G = Counter(q - p for p, q in SPLITS)
pr("    " + "  ".join(f"w={w}: {G[6 * w + 4]} / {G[6 * w - 4] if w else 0}" for w in range(0, 8)))
pr("  The side-kept gap (0.47 vs 0.38) is this length difference and nothing else: shorter hops are commoner, and the"
   " mirror hands the shorter hop to 6k-1 for odd w (gap 2, 14, 26: flips) and to 6k+1 for even w (gap 4, 16: keeps).")

# ---------------------------------------------------------------- 5. the rotation frame (the four seats mod 12 as a cycle)
pr("\nROTATION FRAME: seats mod 12 on the cycle 1 -> 5 -> 7 -> 11 -> 1 (steps +4, +2, +4, +2). A hop moves k steps,"
   " k in {0, +1, 2, -1}. For 6k+1 'side kept' = {0, +1}; for 6k-1 'side kept' = {0, -1}: the families counter-rotate."
   " Shares per family and band:")
IDX = {1: 0, 5: 1, 7: 2, 11: 3}
for lo, hi in BANDS:
    cells = []
    for f in (1, -1):
        ks = Counter((IDX[q % 12] - IDX[p % 12]) % 4 for p, q in SPLITS if lo <= p < hi and FAM(p) == f)
        n = sum(ks.values())
        cells.append(f"6k{f:+d}: 0:{ks[0] / n:.3f} +1:{ks[1] / n:.3f} 2:{ks[2] / n:.3f} -1:{ks[3] / n:.3f}")
    pr(f"  band [{lo},{hi})  " + "   ".join(cells))

# ---------------------------------------------------------------- 6. the m line and the lake on the whole split
pr("\nTHE m LINE on the split (carried mirror n -> 11(2j+1) - n, first odd multiple of 11 above q): keeps the gap, so keeps"
   " h, w and both flips; moves the families. Family of the image start seat (11(2j+1) - q) by family of p, to 1e6:")
Cm = Counter()
for p, q in SPLITS:
    O = 11 * (2 * ((q // 11) // 2) + 1)
    if O <= q: O += 22
    ip, iq = O - q, O - p
    assert iq - ip == q - p
    Cm[(FAM(p), ip % 6)] += 1
pr("    " + "  ".join(f"p 6k{f:+d} -> image start mod 6 = {r}: {Cm[(f, r)]}" for f in (1, -1) for r in (0, 1, 2, 3, 4, 5) if Cm[(f, r)]))
pr("  The m line throws the image start onto every seat of the block (the offset 11 is 5 mod 6); it cannot show the side"
   " flip because the flip rides on the gap, which it keeps. Read: not the missing mirror; a frame change only.")

pr("\nTHE LAKE on the split (his slide rule K^2/x with K^2 = pq, so p <-> q and the inside of the gap turns over):"
   " the lake image of the true centre m is 2pq/(p+q), BELOW m by exactly h^2/m (exact identity m - 2pq/(p+q) = h^2/m)."
   " The lake centre is the asymmetric centre: it leans to p's side. Its offset h^2/m, to 1e6:")
for p, q in SPLITS[:3] + SPLITS[1000:1002]:
    m, h = Fr(p + q, 2), Fr(q - p, 2)
    assert m - Fr(2 * p * q, p + q) == h * h / m
    pr(f"    ({p},{q}): centre {m}, lake centre {Fr(2 * p * q, p + q)} = m - {h * h / m}")
# recursive inverse of the hand-off
for p, q in SPLITS[::500]:
    h, m = (q - p) // 2, (p + q) // 2
    assert (m - h, m + h) == (p, q) and (m + h) - (m - h) == 2 * h and (m + h) + (m - h) == 2 * m
pr("  RECURSIVE INVERSE of the hand-off H(p,q) = (h, m): H(h, m) = ((m-h)/2, (m+h)/2) = (p/2, q/2). Twice through the"
   " hand-off returns the split one level down (v): the hand-off is a lake mirror; the 1 x 1 = 2 sits at its centre.")

# ---------------------------------------------------------------- 7. opposites of the centre
pr("\nOPPOSITES OF THE CENTRE (what each pair carries):")
pr("  (a) centre of the gap m  <->  centre of the centres (m_i + m_{i+1})/2. The prime p_{i+1} sits off the centre of"
   " the centres by exactly (g_i - g_{i+1})/4: reading the prime against the two centres reads the CHANGE of gap.")
chg = Counter()
for i in range(1, len(SPLITS)):
    (p0, p1), (_, p2) = SPLITS[i - 1], SPLITS[i]
    g0, g1 = p1 - p0, p2 - p1
    assert Fr(p1) - Fr(p0 + 2 * p1 + p2, 4) == Fr(g0 - g1, 4)
    chg[(FAM(p1), np.sign(g1 - g0))] += 1
for f in (1, -1):
    n = sum(c for (ff, s), c in chg.items() if ff == f)
    pr(f"    next gap after a 6k{f:+d} prime: grows {chg[(f, 1)] / n:.4f}, same {chg[(f, 0)] / n:.4f}, shrinks {chg[(f, -1)] / n:.4f}  (n={n})")
grow = sum(c for (f, s), c in chg.items() if s == 1); shrink = sum(c for (f, s), c in chg.items() if s == -1)
pr(f"    all primes: grows {grow} vs shrinks {shrink} (walking down swaps them; the walk itself has no preferred direction here).")
pr("  (b) centre of the gap  <->  the wall nearest it. Twins: the centre IS the wall (6k+6, both 2 and 3 on m)."
   " Cousins: the centre is the half wall 6k+3 (3 on m, 2 on h). Gap 6 from 6k+1: wall at (5 from p, 1 from q);"
   " from 6k-1: wall at (1, 5). The per-block mirror swaps the two. Offsets (first wall - p, q - last wall) to 1e6:")
Cw = Counter()
for p, q in SPLITS:
    w, s = wall_frame(p, q)
    if w == 0: Cw[("none", FAM(p))] += 1; continue
    first = (p // 6 + 1) * 6; last = (q // 6) * 6
    Cw[((first - p, q - last), FAM(p))] += 1
pr("    " + "  ".join(f"{k}: {v}" for k, v in sorted(Cw.items(), key=lambda kv: str(kv[0]))))
pr("  (c) centre of the gap  <->  centre of the wings. Wing of n = n//2 (2k, 2k+1 share wing k). The wing centre of"
   " (p, q) is (m-1)/2 when h is odd... exact: wings (p-1)/2 and (q-1)/2 have centre (m-1)/2; it is a whole seat exactly"
   " when m is odd, i.e. when h is even (side kept). So: side kept <=> the wing centre is a seat; side flipped <=> the"
   " wing centre falls between two wings (the centre m is even and is itself a wing's even half).")
for p, q in SPLITS[::300]:
    m = (p + q) // 2
    assert ((m - 1) % 2 == 0) == (((q - p) // 2) % 2 == 0)

# ---------------------------------------------------------------- 8. the tell
pr("\nTHE TELL: the reading whose opposite completes it is the side flip. Read from p it belongs to 6k+1 (the hop with no"
   " wall is 6k+1 -> 6k+5); read from q it belongs to 6k-1 (the same hop arrives at 6k+5). In the wall frame it belongs"
   " to neither: side flip = odd walls, facing flip = seat step, and the exact balance is #(+1 steps) = #(-1 steps) (to 1).")

# ---------------------------------------------------------------- 9. range closing, with the wall frame and the opposites
# packed passed places (as before): laid blocks from B places
def laid_bound(p, B):
    r_list = [int(r) for r in P[:400]]
    i, places, last = 2, 0, 3
    while places < B and i < len(r_list):
        c = 1
        while i < len(r_list) and c * r_list[i] <= p:
            c *= r_list[i]; last = r_list[i]; i += 1
        if c == 1: break
        places += 1
    return last
THRESH = sorted({laid_bound(lo, B) for lo, hi in BANDS for B in (0, 1, 3, 7, 15, 31, 63, 95)})
HITS = {}
for R in THRESH:
    hits = np.zeros(N + 1, dtype=np.int16)
    for r in P[P <= R]: hits[int(r)::int(r)] += 1
    HITS[R] = hits
HS = np.arange(1, H_MAX + 1)

def learned(lo, key):
    """rule of change read from primes below the band: counts of h per key(p, prev gap)."""
    W = defaultdict(lambda: np.zeros(H_MAX))
    for i in range(1, len(SPLITS)):
        p, q = SPLITS[i]
        if p >= lo: break
        h = (q - p) // 2
        if h <= H_MAX: W[key(p, SPLITS[i - 1][1] - SPLITS[i - 1][0])][h - 1] += 1
    return W
KEYS = {
    "walk (nearest first)": None,
    "family p mod 12": lambda p, gp: p % 12,
    "family + prev gap": lambda p, gp: (p % 12, min(gp, 30)),
    "family + prev walls": lambda p, gp: (p % 12, min(wall_frame(p - gp, p)[0], 5)),
    "family + prev (w,s)": lambda p, gp: (p % 12, min(wall_frame(p - gp, p)[0], 5), wall_frame(p - gp, p)[1]),
    "both ends: p fam + q fam (h mod 3)": lambda p, gp: (p % 12, (gp // 2) % 3),
}
def run_band(lo, hi, B, key):
    R = laid_bound(lo, B); hits = HITS[R]
    W = learned(lo, key) if key else None
    ranks = []
    for i in range(1, len(SPLITS)):
        p, q = SPLITS[i]
        if p < lo: continue
        if p >= hi: break
        h_true = (q - p) // 2
        if h_true > H_MAX: continue
        ys = p + 2 * HS
        alive = (ys % 3 != 0) if B == 0 else (hits[ys] == 0)
        assert alive[h_true - 1]
        if key is None:
            scores = -HS.astype(float)
        else:
            gp = SPLITS[i - 1][1] - SPLITS[i - 1][0]
            k = key(p, gp)
            scores = W[k] - 1e-6 * HS if k in W else -HS.astype(float)
        s = scores[h_true - 1]
        before = alive & ((scores > s) | ((scores == s) & (HS < h_true)))
        ranks.append(1 + int(before.sum()))
    r = np.array(ranks)
    return int(np.percentile(r, 90, method="higher")), int(np.percentile(r, 99, method="higher")), r.mean(), (r == 1).mean()

pr("\nRANGE CLOSING (seats holding q for 90% / 99% of the band, mean rank, share named first). B = packed passed places"
   " read. Old best was nearest-first. New orderings use the rule of change read below the band, keyed by p's family and"
   " the PREVIOUS hop (walking down from p is fair: it is below p).")
pr(f"{'ordering':<36}{'B':>4} | {'[1e3,1e4)':>24} | {'[1e4,1e5)':>24} | {'[1e5,1e6)':>24}")
TAB = {}
for B in (0, 7, 31, 95):
    for name, key in KEYS.items():
        cells = []
        for lo, hi in BANDS:
            r90, r99, mean, first = run_band(lo, hi, B, key)
            TAB[(name, B, lo)] = (r90, r99, first)
            cells.append(f"{r90:3d}/{r99:3d} {mean:6.2f} {first:.3f}")
        pr(f"{name:<36}{B:>4} | " + " | ".join(f"{c:>24}" for c in cells))
    pr("")
pr(f"[{time.time() - T0:.1f}s] range table done")

# ---------------------------------------------------------------- 10. where it frays
pr("\nWHERE IT FRAYS: the wall frame makes the side flip exact and even-handed, but it is a relabeling of h; it cannot"
   " say which w the next hop takes. The count asymmetry between mirror cells (6w+4 vs 6w-4) is the gap length falloff,"
   " the same fact reached by a different route as the gap frequencies. Previous-hop rules move the first-guess share"
   " by a little and the 90/99 range by 0-1 seat; the range still closes by strands (B), not by ordering.")

with open(os.path.join(HERE, "fable-missing-mirror_v1.0_11-26-2026.txt"), "w") as f:
    f.write("\n".join(OUT) + "\n")
pr(f"[{time.time() - T0:.1f}s] saved fable-missing-mirror_v1.0_11-26-2026.txt")

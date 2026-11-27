# Fable, third run (tUrUq, 11-26-2026): the 5 (then 7) inside the 2,3 structure, and a hierarchy of his rules.
# Author of the method: Turaq Rayn-McLean. His words: "25, is 12,13,12, |12 ... 2x2x3 ... it is showing the 5 at
# its core, so 3 terms ... 18+7 is 25 ... 23 ... 11,12,11 ... looks a whole lot like 1,2,1 ... look at how our 12
# rules effect our 11 rules and maybe we can establish some hierarchy".
# FAIRNESS: a seat y > p is never factored to NAME it; a rule reads p (its residues) and the hop (h, w, s) only.
# isprime scores. "Reading built from divisors of y" is marked as such wherever it appears.
import math, time, os
from collections import Counter, defaultdict
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
def wall_frame(p, q):
    return q // 6 - p // 6, (q % 6 - p % 6) // 4
def pent(P_):            # is P_ a generalized pentagonal number k(3k-1)/2 or k(3k+1)/2 ?
    for k in range(0, int(math.isqrt(P_ * 2 // 3) + 3)):
        if k * (3 * k - 1) // 2 == P_ or k * (3 * k + 1) // 2 == P_: return k
    return None

# ================================================================ 1. FIVE: what 25 shows
pr("1. FIVE. His picture of 25: 12,13,12 |12. Wing 12 = 2x2x3 (three terms), centre 13 = 6|7 (ladder pair), 25 = 18 + 7"
   " = three walls of 6 and the first seat of the fourth block (25 = 6*4 + 1).")
pr("   5-strand composites off 2 and 3, read as (wing, centre, wing) | wing factors | 6-block seat (a, r) | wall count 6a and remainder:")
for n in [25, 35, 55, 65, 85, 95, 115, 125, 145, 155, 175, 185, 205, 215, 235, 245]:
    k = (n - 1) // 2
    f = []; m = k
    for r in (2, 3, 5, 7, 11, 13):
        while m % r == 0: f.append(r); m //= r
    if m > 1: f.append(m)
    pr(f"     {n:4d} = {k},{k + 1},{k}  wing {k} = {'x'.join(map(str, f))} ({len(f)} terms)  seat ({n // 6}, {n % 6})"
       f"  = {6 * (n // 6 - 1)} + {6 + n % 6}  wing mod 5 = {k % 5}  centre mod 5 = {(k + 1) % 5}")
pr("   Reading: a 5-strand number off 2,3 is 30b + 5 (last seat of block 5b) or 30b + 25 (first seat of block 5b + 4):"
   " inside the 2,3 structure the 5 shows as the pair of seats (block 0, last) and (block 4, first) of each 30-run,"
   " the mirror pair 5 <-> 25 under n -> 30 - n. Its wing is 2 mod 5 and its centre 3 mod 5 in every case"
   " (wing = (5m-1)/2 = -1 * 3 = 2 mod 5): that is a divisor reading of y, not used below for naming.")

pr("\n   PENTAGONAL WINGS (exact): wing of y is 12 x P with P generalized pentagonal  <=>  y = (6k -+ 1)^2.")
for p_ in [5, 7, 11, 13, 17, 19, 23, 25, 29, 31, 35, 37, 41, 43, 47, 49]:
    y = p_ * p_; w = (y - 1) // 2
    assert w % 12 == 0 and pent(w // 12) is not None
    pr(f"     {p_:3d}^2 = {y:5d}: wing {w:5d} = 12 x {w // 12:4d}  (k = {pent(w // 12)})")
# converse: 24P+1 for generalized pentagonal P is a square of a 6k+-1 number
for k in range(0, 200):
    for P_ in (k * (3 * k - 1) // 2, k * (3 * k + 1) // 2):
        y = 24 * P_ + 1; r = math.isqrt(y)
        assert r * r == y and r % 6 in (1, 5) or y == 1
# how many odd y have wing 12 x pentagonal and are NOT squares: none (proven in Lean, checked here to 1e6)
cnt = 0
for y in range(1, 10 ** 6, 2):
    if (y - 1) % 24 == 0 and pent((y - 1) // 24) is not None:
        assert math.isqrt(y) ** 2 == y; cnt += 1
pr(f"   checked to 1e6: {cnt} odd y with wing 12 x pentagonal, all of them squares (6k-+1)^2; (6k-1)^2 = 12k(3k-1) + 1,"
   f" (6k+1)^2 = 12k(3k+1) + 1. Same fact by a different route: Euler's pentagonal numbers. Lean: pent_square_minus,"
   f" pent_square_plus.")
pr("   So '12 x pentagonal' is a fair reading that names a square seat without factoring it: 25 (P=1), 49 (P=2), 121 (P=5),"
   " 169 (P=7), 289 (P=12), 361 (P=15). It names squares only, not 35, 55, 77, 91.")

# ---------------------------------------------------------------- 1b. the 5 as a hop rule read from p
pr("\n   THE 5 IN THE HOP FRAME (read from p only). y = p + 2h is a 5-seat  <=>  h = 2p mod 5. Likewise 7: h = 3p mod 7;"
   " 11: h = 5p mod 11; 13: h = 6p mod 13 (the class is ((r+1)/2 - 1) * ... exact: h = -(p * inverse of 2) mod r). Lean:"
   " five_class, seven_class, eleven_class.")
for p, q in SPLITS[::997]:
    for r, c in ((5, 2), (7, 3), (11, 5), (13, 6)):
        for h in range(1, 60):
            assert ((p + 2 * h) % r == 0) == (h % r == (c * p) % r)
pr("   Allowed h classes: 2,3 leave 4 of 6 (per family p mod 12); + 5 leaves 16 of 30; + 7 leaves 96 of 210;"
   " + 11 leaves 960 of 2310. Checked per residue p mod 60 / 420:")
for mod_p, mod_h, rules in ((60, 30, (2, 3, 5)), (420, 105, (2, 3, 5, 7))):
    allowed = set()
    for pr_ in range(mod_p):
        if any(pr_ % r == 0 for r in rules): continue
        ok = tuple(h for h in range(mod_h) if all((pr_ + 2 * h) % r for r in rules))
        allowed.add(len(ok))
    pr(f"     p mod {mod_p} off {rules}: allowed h mod {mod_h} count = {sorted(allowed)} in every class")
    assert len(allowed) == 1

# where the 5 sits ABOVE the hand-off: the hand-off's first seat is a 5-seat
pr("\n   WHERE r SITS ABOVE THE HAND-OFF (2,3): the first off-2,3 seat past p is an r-seat exactly from the seat just"
   " before each of the two r-seats r and 5r of the 6r-run (5: p = 1 -> 5 and 23 -> 25 mod 30; 7: 5 -> 7, 31 -> 35 mod 42):")
def first_off23(p):
    return p + 4 if p % 6 == 1 else p + 2
for r in (5, 7, 11, 13):
    M = 6 * r
    cls = sorted(a for a in range(M) if a % 2 and a % 3 and a % r and first_off23(a) % r == 0)
    pr(f"     r = {r}: hand-off's first seat is an r-seat for p mod {M} in {cls}  ({len(cls)} of {2 * (r - 1)} off classes)")

# ---------------------------------------------------------------- 1c. misses fixed
pr("\n   MISSES OF THE CHEAP MAP (first open seat past p is composite), and what each added rule fixes:")
def first_open(p, rules):
    y = p + 2
    while any(y % r == 0 for r in rules): y += 2
    return y
STACKS = [(2, 3), (2, 3, 5), (2, 3, 5, 7), (2, 3, 5, 7, 11), (2, 3, 5, 7, 11, 13)]
MISS = {}
for rules in STACKS:
    miss = [(p, first_open(p, rules)) for p, q in SPLITS if p > max(rules) and not is_p[first_open(p, rules)]]
    MISS[rules] = miss
    cnts = [sum(1 for p, y in miss if p < L) for L in (10 ** 3, 10 ** 4, 10 ** 5, 10 ** 6)]
    tot = [sum(1 for p, q in SPLITS if max(rules) < p < L) for L in (10 ** 3, 10 ** 4, 10 ** 5, 10 ** 6)]
    pr(f"     rules {rules}: misses to 1e3/1e4/1e5/1e6 = {cnts[0]}/{cnts[1]}/{cnts[2]}/{cnts[3]} of {tot[3]} hops"
       f"  first misses {[y for p, y in miss[:8]]}")
m23 = MISS[(2, 3)]; m235 = MISS[(2, 3, 5)]; m2357 = MISS[(2, 3, 5, 7)]
for L in (10 ** 3, 10 ** 4, 10 ** 5, 10 ** 6):
    a = sum(1 for p, y in m23 if p < L); b = sum(1 for p, y in m23 if p < L and y % 5 == 0)
    c = sum(1 for p, y in m235 if p < L and 5 < p); d = sum(1 for p, y in m235 if p < L and 5 < p and y % 7 == 0)
    pr(f"     to {L}: of the 2,3 misses, the first seat was a 5-seat in {b}/{a} ({b / a:.3f}); of the 2,3,5 misses, a 7-seat in"
       f" {d}/{c} ({d / c:.3f})")
pr("   Reading: the 5 rule fixes the 5-seat misses exactly (every miss whose first seat was 5x something) and no other;"
   " the misses it leaves are 7-, 11-, 13-seats and seats of larger strands. The share fixed falls with size"
   " (the first open seat is a 5-seat in about 1 of 4 of the 2,3 misses at 1e3, fewer higher) because larger"
   " strands take over: this is the strand ladder (B passed places), seen rule by rule.")

# ================================================================ 2. HIERARCHY
pr("\n2. HIERARCHY. Rule groups (his names in quotes):")
pr("   '12 rules' (seat rules, mod 12 = 2,2,3): hand-off (one of m,h even; one on 3), family p mod 12 -> allowed h mod 6,"
   " wall/seat hop h = 3w + 2s, facing x side.")
pr("   '5 rules': h != 2p mod 5 (5-strand), pentagonal wing (squares).  '7 rules': h != 3p mod 7.")
pr("   '11 rules' (frame rules): offset-11 mirror n -> 11(2j+1) - n, per-11-block mirror 11a + r -> 11a + 11 - r,"
   " the 11/15 sporadic pair (u(n) = 2(n-1) only at 2, 11, 15).  Lake: 2pq/(p+q); hand-off twice = (p/2, q/2)."
   " Halving/thirding/turn: a,b,a : s pictures of n; u(n).")

# 2a. COMBINE: seats between p and q closed by how many strand rules
pr("\n   2a. COMBINE (reinforce): off-2,3 seats strictly between p and q, by how many of the strands 5, 7, 11, 13 close them (to 1e6):")
comb = Counter(); comb_pairs = Counter()
for p, q in SPLITS:
    y = first_off23(p)
    while y < q:
        rs = tuple(r for r in (5, 7, 11, 13) if y % r == 0)
        comb[len(rs)] += 1
        if len(rs) >= 2: comb_pairs[rs] += 1
        y = first_off23(y)
tot = sum(comb.values())
pr(f"     seats {tot}: closed by 0 of {{5,7,11,13}} (a larger strand): {comb[0]} ({comb[0] / tot:.3f}); by exactly 1: {comb[1]}"
   f" ({comb[1] / tot:.3f}); by 2 (combine): {comb[2]} ({comb[2] / tot:.3f}); by 3: {comb[3]}")
pr(f"     pairs that combine on one seat: {dict(comb_pairs)}  (35 = 5x7 is the first: p = 31 -> 35, both rules fire; neither"
   f" overturns the other, a seat closed twice is closed once).")

# 2b. CANCEL / ABOVE within the 12 rules: facing flip (s != 0) and side flip (w odd)
pr("\n   2b. The two flips of the 12 rules (facing: s != 0; side: w odd) combine or cancel per hop (to 1e6):")
FL = Counter()
for p, q in SPLITS:
    w, s = wall_frame(p, q); FL[(s != 0, w % 2 == 1)] += 1
n = sum(FL.values())
pr(f"     both kept {FL[(False, False)] / n:.4f}  facing only {FL[(True, False)] / n:.4f}  side only {FL[(False, True)] / n:.4f}"
   f"  both flip {FL[(True, True)] / n:.4f}")
pr("     facing kept and side kept together = gap multiple of 12 (h = 0 mod 6): the hop lands in the same seat mod 12."
   " Per-block mirror 6a+r <-> 6a+6-r sends s -> -s and keeps w: it cancels the facing flip's direction and leaves the"
   " side flip alone (Lean block_mirror_hop, earlier run).")

# 2c. 11 rules vs 12 rules
pr("\n   2c. 11 RULES vs 12 RULES. Offset-11 mirror n -> O - n (O = 11(2j+1)) keeps the gap, so keeps h, w, s: it cannot"
   " overturn any 12 rule (it sits BELOW them as a frame). O is odd, O mod 6 in {1, 3, 5}; the image seat is O - q mod 6."
   " Counts of image start seat mod 6, by O mod 6 (to 1e6):")
Cm = Counter()
for p, q in SPLITS:
    O = 11 * (2 * ((q // 11) // 2) + 1)
    if O <= q: O += 22
    Cm[(O % 6, (O - q) % 6)] += 1
pr("     " + "  ".join(f"O={o} mod 6 -> image start mod 6 = {r}: {Cm[(o, r)]}" for o in (1, 3, 5) for r in range(6) if Cm[(o, r)]))
pr("     An odd O always lands the image on an even seat (odd - odd): the offset-11 mirror leaves the 2,3 seat structure"
   " behind (O = 3 mod 6 puts the image on 2-seats off 3, O = 1 or 5 mod 6 puts one end on a 6-wall). Hierarchy: 12 rules"
   " name seats; 11 rules move the frame; a frame move that keeps h keeps every h-rule's verdict and names nothing new.")
# per-11-block mirror
keep = Counter()
for p, q in SPLITS[:20000]:
    a, r = divmod(p, 11); img = 11 * a + 11 - r
    keep[(img % 2 == 1 and img % 3 != 0, bool(is_p[img]))] += 1
pr(f"     per-11-block mirror of p (first 20000 primes from 5): image off 2,3 and prime {keep[(True, True)]}, off 2,3 not prime"
   f" {keep[(True, False)]}, on a 2- or 3-seat {keep[(False, True)] + keep[(False, False)]}: the image 11a + 11 - r = p + 11 - 2r"
   f" is even for every odd p (proven: block_mirror_even); the 11-block mirror is a frame, not a seat rule.")
# the 11-strand as a seat rule (same shape as 5 and 7)
pr("     The 11 STRAND (h != 5p mod 11) is a seat rule like 5 and 7; it joins the 12 rules in the stack above (misses table).")

# 2d. PRECEDENCE TABLE over residues
pr("\n   2d. PRECEDENCE TABLE (to 1e6). For each hop, the first seat the hand-off (2,3) names; who sits above it:")
PREC = Counter(); BYCLS = defaultdict(Counter)
for p, q in SPLITS:
    y = first_off23(p)
    if y == q: who = "q (hand-off right)"
    elif y % 5 == 0: who = "5 above"
    elif y % 7 == 0: who = "7 above"
    elif y % 11 == 0: who = "11 above"
    elif y % 13 == 0: who = "13 above"
    else: who = "larger strand above"
    PREC[who] += 1; BYCLS[p % 30][who] += 1
n = sum(PREC.values())
for k, v in PREC.most_common(): pr(f"     {k:<22} {v:6d}  {v / n:.4f}")
pr("     by p mod 30 (5 above the hand-off lives in two classes, 1 and 23; the other six classes read alike):")
for c in sorted(BYCLS):
    tot_c = sum(BYCLS[c].values())
    pr(f"       p = {c:2d} mod 30: hand-off right {BYCLS[c]['q (hand-off right)'] / tot_c:.3f}  5 above {BYCLS[c]['5 above'] / tot_c:.3f}"
       f"  7 above {BYCLS[c]['7 above'] / tot_c:.3f}  11 above {BYCLS[c]['11 above'] / tot_c:.3f}  (n={tot_c})")
assert all(BYCLS[c]["5 above"] == 0 for c in BYCLS if c not in (1, 23))
assert all(BYCLS[c]["5 above"] == sum(BYCLS[c].values()) for c in (1, 23))
pr("     Exact: '5 above the hand-off' happens from p = 1 or 23 mod 30 and from no other class (all hops to 1e6; Lean"
   " five_above_handoff, five_not_above). In those two classes the hand-off is never right (its seat is 5 or 25 mod 30), so"
   " there the 5 rule sits above the 12 rule in every hop; in the other 6 classes the 5 rule cannot touch the hand-off's"
   " first seat (it closes later seats only). Shares: 5 above = 2/8 = 1/4 of hops (0.2503); 7 above = (3/4)(1/6) = 0.125"
   " (0.1250); 11 above = (3/4)(5/6)(1/10) = 0.0625 (0.0626); 13 above = (3/4)(5/6)(9/10)(1/12) = 0.0469 (0.0473): each rule r"
   " takes the share 1/(r-1) of what the smaller rules left. Same fact by a different route: primes spread evenly over the"
   " off classes mod 6r. The precedence is read from p's seat in the 6r-run, nothing above p.")
# second level: after 5 is applied, who sits above the 2,3,5 first seat, per p mod 42
PREC2 = Counter(); BY42 = defaultdict(Counter)
for p, q in SPLITS:
    if p <= 7: continue
    y = first_open(p, (2, 3, 5))
    who = "q" if y == q else ("7 above" if y % 7 == 0 else ("11 above" if y % 11 == 0 else "other"))
    PREC2[who] += 1; BY42[p % 42][who] += 1
n = sum(PREC2.values())
pr("     Second level, 2,3,5 first seat: " + "  ".join(f"{k} {v / n:.4f}" for k, v in PREC2.most_common()))
cls7 = sorted(c for c in BY42 if BY42[c]["7 above"])
pr(f"     '7 above the 2,3,5 seat' occurs from p mod 42 in {cls7} (and nowhere else to 1e6): the two 7-classes 5, 31 plus the"
   f" classes 1, 29 whose next seat is a 5-seat followed by a 7-seat (the full condition lives mod 210 = 2x3x5x7).")

# 2e. does the hierarchy ordering close the range?
HS = np.arange(1, H_MAX + 1)
def band_ranks(lo, hi, rules, order):
    ranks = []
    for p, q in SPLITS:
        if p < lo or p < max(rules): continue
        if p >= hi: break
        h_true = (q - p) // 2
        if h_true > H_MAX: continue
        ys = p + 2 * HS
        alive = np.ones(H_MAX, dtype=bool)
        for r in rules: alive &= (ys % r != 0)
        assert alive[h_true - 1]
        scores = order(p, HS)
        s = scores[h_true - 1]
        before = alive & ((scores > s) | ((scores == s) & (HS < h_true)))
        ranks.append(1 + int(before.sum()))
    r = np.array(ranks)
    return int(np.percentile(r, 90, method="higher")), int(np.percentile(r, 99, method="higher")), r.mean(), (r == 1).mean()
ORDERS = {
    "nearest first": lambda p, H: -H.astype(float),
    "side-flip (h odd) first, then nearest": lambda p, H: (H % 2 == 1) * 1000.0 - H,
    "side-keep (h even) first, then nearest": lambda p, H: (H % 2 == 0) * 1000.0 - H,
    "facing-flip (3 not| h) first": lambda p, H: (H % 3 != 0) * 1000.0 - H,
    "walls even first (w even)": lambda p, H: ((((p + 2 * H) // 6 - p // 6) % 2) == 0) * 1000.0 - H,
}
pr("\n   2e. RANGE CLOSING by the rule stack, nearest-first (90% / 99% seats, mean rank, share named first), per band:")
pr(f"     {'stack':<34} | {'[1e3,1e4)':>22} | {'[1e4,1e5)':>22} | {'[1e5,1e6)':>22}")
RES = {}
for rules in STACKS + [(2, 3, 5, 7, 11, 13, 17), (2, 3, 5, 7, 11, 13, 17, 19, 23)]:
    cells = []
    for lo, hi in BANDS:
        r90, r99, mean, first = band_ranks(lo, hi, rules, ORDERS["nearest first"])
        RES[(rules, lo)] = (r90, r99, first)
        cells.append(f"{r90:3d}/{r99:3d} {mean:5.2f} {first:.3f}")
    pr(f"     {str(rules):<34} | " + " | ".join(f"{c:>22}" for c in cells))
pr("     (earlier run, same bands: hand-off only 9/17 top band; 1 packed place = strands to 17: 5/9; 7 places = to 73: 3/5)")
assert RES[((2, 3), 10 ** 5)][:2] == (9, 17)
pr("\n     Orderings on top of the 2,3,5,7 stack (does putting one rule 'above' another beat nearest-first?):")
for name, order in ORDERS.items():
    cells = []
    for lo, hi in BANDS:
        r90, r99, mean, first = band_ranks(lo, hi, (2, 3, 5, 7), order)
        cells.append(f"{r90:3d}/{r99:3d} {mean:5.2f} {first:.3f}")
    pr(f"     {name:<34} | " + " | ".join(f"{c:>22}" for c in cells))
pr("     Reading: the 12-rule flips as an ordering (flip first or keep first) do not beat nearest-first; the stack closes"
   " the range by adding seat rules (5, 7, 11, ...), each exactly the strand of that passed place. Hierarchy for naming:"
   " seat rules (2,3 < 5 < 7 < 11 ...) in size order, nearest first among the open seats; frame rules (11-mirror, lake,"
   " per-block mirror) change the picture and never the verdict.")

# ================================================================ 3. 23 ~ 1,2,1
pr("\n3. 23 = 11,12,11 AND 3 = 1,2,1. Odd n = k,k+1,k has an even centre k+1 exactly when n = 3 mod 4 (Lean even_centre_iff)."
   " Scaled copy: the wing k is itself odd and k = k',k'+1,k' with even centre exactly when n = 7 mod 8; j levels of even"
   " centres exactly when n = -1 mod 2^(j+1) (binary: n ends in j+1 ones). 23 = 10111 -> 11 = 1011 -> 5 = 101 -> 2;"
   " 3 = 11 -> 1.")
for n in range(3, 5000, 2):
    j = 0; m = n
    while m % 2 == 1 and ((m + 1) // 2) % 2 == 0: j += 1; m = (m - 1) // 2
    # j = number of trailing ones minus 1
    t = len(bin(n)) - len(bin(n).rstrip("1"))
    assert j == t - 1
pr("   checked n < 5000: levels of even centre = (trailing ones of n) - 1.")
pr("   TEST (the picture's recursion on primes): a prime p whose wing (p-1)/2 is prime is a 'scaled copy' (k,k+1,k with k"
   " prime). The wing of p = 1 mod 4 is even, so only the even-centre family (3 mod 4) can carry a prime wing (p = 5 the"
   " one odd-centre case: wing 2). Counts to 1e6:")
CH = Counter(); cnt3 = cnt1 = 0; w3 = w1 = 0
for p in P[P < 10 ** 6]:
    p = int(p)
    if p < 5: continue
    if p % 4 == 3:
        cnt3 += 1
        if is_p[(p - 1) // 2]: w3 += 1
    else:
        cnt1 += 1
        if is_p[(p - 1) // 2]: w1 += 1
    d = 0; m = p
    while is_p[m] and m % 4 == 3 and is_p[(m - 1) // 2]: d += 1; m = (m - 1) // 2
    CH[d] += 1
pr(f"     p = 3 mod 4: {w3} of {cnt3} have a prime wing ({w3 / cnt3:.4f});  p = 1 mod 4: {w1} of {cnt1} ({w1 / cnt1:.6f}, only p = 5)")
pr(f"     depth of the copy chain (p -> wing -> wing ...; all prime, even centres): {dict(sorted(CH.items()))}")
chain = []; m = 2
while is_p[m]: chain.append(m); m = 2 * m + 1
pr(f"     the chain through 3's picture: 3 = 1,2,1 is the wing-side copy of 7 = 3,4,3; 23's chain 2, 5, 11, 23, 47 (then 95"
   f" = 5 x 19 breaks): {chain}. Same fact by a different route: safe primes / Cunningham chains.")
pr("   THE OPPOSITE (odd centre, n = 1 mod 4, centre (n+1)/2 prime): 13 = 6,7,6 is prime, 25 = 12,13,12 is not. Counts to 1e6:")
oc = Counter(); first_comp = []
for n in range(5, 10 ** 6, 4):
    c = (n + 1) // 2
    if is_p[c]:
        oc[bool(is_p[n])] += 1
        if not is_p[n] and len(first_comp) < 12: first_comp.append(n)
pr(f"     odd-centre n with prime centre: prime {oc[True]}, composite {oc[False]} (share prime {oc[True] / sum(oc.values()):.4f});"
   f" first composites {first_comp}")
pr("     The even-centre copy is a one-way ladder (n -> wing, exact); the odd-centre 'opposite' pairs a prime centre with"
   " 25, 45, 85 ... as often as with primes, so the centre's primality does not read the seat. Where 23 ~ 1,2,1 holds:"
   " the SHAPE (even centre, odd wings) is exact and recursive by trailing ones; the PRIMALITY of the copy is the"
   " 2p+1 chain, which breaks at 95 for this family.")

pr(f"\n[{time.time() - T0:.1f}s] done")
with open(os.path.join(HERE, "rule-hierarchy_v1.0_11-26-2026.txt"), "w") as f:
    f.write("\n".join(OUT) + "\n")

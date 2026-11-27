# Fable, fourth run (tUrUq, 11-26-2026): "lets see if we can crack the nut now. we see the parts".
# Author of the method: Turaq Rayn-McLean. The two parts of every odd n:
#   (a) halving  k, k+1, k  with k = (n-1)/2: the NEIGHBOURS n-1, n+1 halved (the left-outs' blocks; 55 = 27,28,27 shows 54, 56)
#   (b) turn     n as q copies of n/q (its OWN blocks; 55 = 11,11,11,11,11; a prime = p copies of 1)
# Decimal unit line: 11 is the one of 10s (d x 11 = dd); 55 = five 11s; 11, 101, 1001, 10001 = base+1 mirrors.
# FAIRNESS for naming: a seat y > p is never factored to name it; a reading uses p's residues, h and passed numbers.
# isprime scores only. Imports dual_long_hand (unchanged).
import math, time, os, sys
from collections import Counter, defaultdict
import numpy as np
from sympy import factorint, isprime, primerange
import importlib.util
_spec = importlib.util.spec_from_file_location("dlh", os.path.join(os.path.dirname(os.path.abspath(__file__)), "dual-long-hand_v1.0_11-26-2026.py"))
dlh = importlib.util.module_from_spec(_spec); _spec.loader.exec_module(dlh)

T0 = time.time()
HERE = os.path.dirname(os.path.abspath(__file__))
OUT = []
def pr(*a):
    s = " ".join(str(x) for x in a); print(s); OUT.append(s)

N = 10 ** 6 + 200
is_p = np.ones(N + 1, dtype=bool); is_p[:2] = False
for i in range(2, int(N ** 0.5) + 1):
    if is_p[i]: is_p[i * i::i] = False
P = np.flatnonzero(is_p)
SPLITS = [(int(p), int(q)) for p, q in zip(P, P[1:]) if 5 <= p < 10 ** 6]
BANDS = [(10 ** 3, 10 ** 4), (10 ** 4, 10 ** 5), (10 ** 5, 10 ** 6)]

# ================================================================ 1. THE TWO PARTS, EXACT
pr("TWO PARTS (Fable 4th run, 11-26-2026). Every odd n read as halving (neighbours' blocks) beside turn (own blocks).\n")
pr("1. THE TIE. Halving k, k+1, k of odd n: wing w = (n-1)/2, centre c = (n+1)/2, and c^2 - w^2 = (c-w)(c+w) = 1 x n.")
pr("   A turn face a x b (a <= b, both odd, ab = n) is the SAME shape: n = ((a+b)/2)^2 - ((b-a)/2)^2, centre (a+b)/2, wing (b-a)/2,")
pr("   centre - wing = a (the block). The halving picture is the turn face 1 x n read as a square difference (block 1).")
pr("   So: pictures of n with centre^2 - wing^2 = n  <->  turn faces of n, one to one. A prime has one face (1 x p), so one picture:")
pr("   its halving. An odd composite has one more picture per face; the extra pictures carry its own blocks as centre - wing.")
def pictures(n):           # all (c, w) with c^2 - w^2 = n, w >= 0
    return [((a + n // a) // 2, (n // a - a) // 2) for a in range(1, math.isqrt(n) + 1) if n % a == 0]
def faces(n):
    return [(a, n // a) for a in range(1, math.isqrt(n) + 1) if n % a == 0]
for n in (5, 11, 55, 121, 1729, 111121111):
    pics = pictures(n)
    pr(f"   {n}: faces {faces(n)}  pictures (centre, wing) {pics}  turn {dlh.turn_face(n)}")
for n in range(3, 5001, 2):
    pics = pictures(n)
    assert all(c * c - w * w == n for c, w in pics) and len(pics) == len(faces(n))
    assert pics[0] == ((n + 1) // 2, (n - 1) // 2)                    # the halving is the 1-face
    assert (len(pics) == 1) == isprime(n)
    assert all(math.gcd(n, n - 1) == 1 and math.gcd(n, n + 1) == 1 for _ in (0,))
pr("   Checked odd n < 5000: pictures = faces one to one; halving = the 1-face; exactly one picture iff prime. 55 = 28^2 - 27^2 = 8^2 - 3^2.")
pr("   Neighbours never carry a block of n (gcd(n, n+-1) = 1, proven): the halving reads what sits AROUND n, the turn reads n.")
pr("   Wing x centre = (n^2 - 1)/4 = (n-1)(n+1)/4: the left-outs' product, halved twice.\n")

# per family: where 2 and 3 of the left-outs sit
pr("2. PER FAMILY (p mod 12, read from p): where the 2 and 3 of the left-outs sit in the halving picture (w, c mod 6):")
fam = defaultdict(set)
for p, q in SPLITS[:20000]:
    w, c = (p - 1) // 2, (p + 1) // 2
    fam[p % 12].add((w % 6, c % 6, w % 4, c % 4))
for r in (1, 5, 7, 11):
    pr(f"   p = {r:2d} mod 12: (w mod 6, c mod 6, w mod 4, c mod 4) = {sorted(fam[r])}")
pr("   p = 1 mod 12: wing carries 2 and 3 (p-1 = 12m), centre odd off 3.   p = 11 mod 12: centre carries 2 and 3, wing odd off 3.")
pr("   p = 5 mod 12: wing even, centre carries 3 (odd).   p = 7 mod 12: wing carries 3 (odd), centre even.")
pr("   (6k+1 family = 1, 7 mod 12: 3 sits in the wing; 6k-1 family = 5, 11 mod 12: 3 sits in the centre; the circle p = +-1 mod 12")
pr("   puts 2 AND 3 on one side, the off-circle 5, 7 splits them.) 8 | p^2 - 1 and 3 | p^2 - 1 for p off 2,3: 6 | w x c.")
assert fam[1] == {(0, 1, 0, 1), (0, 1, 2, 3)} and fam[11] == {(5, 0, 1, 2), (5, 0, 3, 0)}
assert fam[5] == {(2, 3, 2, 3), (2, 3, 0, 1)} and fam[7] == {(3, 4, 3, 0), (3, 4, 1, 2)}
pr("")

# the opposite: odd composites
pr("3. THE OPPOSITE (odd composite n = a x b): own blocks in the turn faces, left-outs in the halving, and the extra pictures.")
pr("   The smallest face q x n/q has centre (q + n/q)/2 and wing (n/q - q)/2; the halving centre (n+1)/2 is larger by (q-1)(n/q-1)/2.")
cnt = Counter()
for n in range(9, 10 ** 5, 2):
    if isprime(n): continue
    f = factorint(n); q = min(f)
    both = set(f) & (set(factorint(n - 1)) | set(factorint(n + 1)))
    assert not both
    cnt["composites"] += 1
    cnt["square"] += (math.isqrt(n) ** 2 == n)
for n in (25, 35, 55, 121, 1729):
    f = factorint(n); q = min(f)
    pr(f"   {n} = {dlh.turn_face(n)}: pictures {pictures(n)}  centre gap halving - face = {(n + 1) // 2 - (q + n // q) // 2} = (q-1)(n/q-1)/2 = {(q - 1) * (n // q - 1) // 2}")
pr(f"   checked {cnt['composites']} odd composites < 1e5: no block of n in n-1 or n+1 (0 cases); {cnt['square']} squares have a wing-0 picture (c = sqrt n).\n")

# ================================================================ 2. DECIMAL UNIT LINE
pr("4. DECIMAL UNIT LINE. 11 = the one of 10s: d x 11 = 10d + d = 'dd' (d < 10). 55 = 5 x 11 = five 11s = the 5-turn of the 10s unit.")
assert all(d * 11 == int(f"{d}{d}") for d in range(1, 10))
pr("   Base+1 mirrors 10^k + 1 and the blocks they carry (these are the strands the decimal line names, in decimal order):")
for k in range(1, 10):
    m = 10 ** k + 1
    pr(f"     10^{k}+1 = {m} = {dict(factorint(m))}")
pr("   (k ones) x (10^(k-1)+1) = (k-1 ones) 2 (k-1 ones):")
for k in range(2, 10):
    R = int("1" * k); v = R * (10 ** (k - 1) + 1)
    assert str(v) == "1" * (k - 1) + "2" + "1" * (k - 1)
    pr(f"     R{k} x {10 ** (k - 1) + 1} = {v} = {dict(factorint(v))}")
pr("   Proven (Lean repunit_mirror, over 9x): (10^k - 1)(10^(k-1) + 1) = (10^(k-1) - 1) 10^k + 18 x 10^(k-1) + (10^(k-1) - 1).")
pr("   444,555,444 = 111 x 4005004 = 111 x (4,5,4 spread by 1000): " + str(444555444 == 111 * 4005004) + f"; 111 = 3 x 37; 4005004 = {dict(factorint(4005004))}")
assert 444555444 == 111 * 4005004
pr("   A candidate y read in units of 11: y = 11a + r is the 11-strand seat rule (r = 0 closed, h = 5p mod 11). In units of 101:")
pr("   the 101-strand (h = -p x 51 mod 101 ... 2 x 51 = 102 = 1 mod 101). 1001 = 7 x 11 x 13 adds nothing beyond 7, 11, 13;")
pr("   10001 adds 73 and 137; 100001 adds 9091; 1000001 adds 9901. The decimal line is the strand ladder in decimal order.\n")

# ================================================================ 3. THE NUT: NAMING
pr("5. THE NUT. Candidate y = p + 2h. Its halving picture is p's halving shifted by h: wing_y = w_p + h, centre_y = c_p + h (proven).")
pr("   y's left-outs: y-1 = 2(w_p + h), y+1 = 2(c_p + h). Their small blocks are read from p and h:")
pr("     r | y-1  iff  h = -w_p mod r;   r | y+1  iff  h = -c_p mod r;   r | y (seat closed)  iff  h = -(w_p + c_p) 2^-1 = -p 2^-1 mod r.")
pr("   What the real next prime's left-outs carry, given p's: the REPEAT reading (q-1 carries r where p-1 carried r  <=>  q = p mod r):")
H_MAX = 60
rows = []
for r in (3, 5, 7, 11, 13):
    rep = Counter()
    for p, q in SPLITS:
        if p < 10 ** 4: continue
        rep[(p % r, q % r)] += 1
    tot = sum(rep.values())
    same = sum(v for (a, b), v in rep.items() if a == b)
    classes = r - 1
    pr(f"     r = {r:2d}: next prime in the SAME seat mod {r} (q = p mod {r}) share {same / tot:.4f}; flat would be 1/{classes} = {1 / classes:.4f};"
       f" shortfall x{(same / tot) / (1 / classes):.3f}")
    rows.append((r, same / tot, 1 / classes))
assert all(s < f for r, s, f in rows)
pr("   Reading: the next prime moves its small-r seat more often than flat; the left-out that carried r below p (p-1 or p+1) does not")
pr("   come back in the same position as often. Same fact by a different route: Lemke Oliver and Soundararajan's consecutive-prime bias (2016).")
pr("   In h: q = p mod r  <=>  h = 0 mod r. So the fair ordering 'demote h = 0 mod r among open seats' is the two-part reading of the hop.\n")

# conditional probability that an open seat at distance h is the next prime, per h (does nearest-first hold?)
def open_mask(p, HS, rules):
    ys = p + 2 * HS
    alive = np.ones(len(HS), dtype=bool)
    for r in rules: alive &= (ys % r != 0)
    return alive
HS = np.arange(1, H_MAX + 1)
pr("6. IS NEAREST-FIRST RIGHT? The HAZARD: P(the open seat at distance h holds q | seats 1..h-1 did not), stack to 13, band [1e5,1e6):")
hit = np.zeros(H_MAX); opn = np.zeros(H_MAX); opn_all = np.zeros(H_MAX)
RULES13 = (2, 3, 5, 7, 11, 13)
for p, q in SPLITS:
    if p < 10 ** 5: continue
    h_true = (q - p) // 2
    if h_true > H_MAX: continue
    al = open_mask(p, HS, RULES13)
    opn[:h_true] += al[:h_true]; opn_all += al
    hit[h_true - 1] += 1
haz = hit / np.maximum(opn, 1)
pr("     h    : " + " ".join(f"{h:5d}" for h in range(1, 31)))
pr("     haz  : " + " ".join(f"{haz[h - 1]:.3f}" for h in range(1, 31)))
mean_haz = hit[:10].sum() / opn[:10].sum()
pr(f"   mean hazard over h <= 10: {mean_haz:.4f}; h = 0 mod 3 seats (3..30) mean {np.mean([haz[h - 1] for h in range(3, 31, 3)]):.4f}, others {np.mean([haz[h - 1] for h in range(1, 31) if h % 3]):.4f}")
pr("   Reading: the hazard is near FLAT (0.39 to 0.45 for h <= 20, rising slowly), with small dips on h = 0 mod 3 (the 3-seat repeat). A flat")
pr("   hazard z means the chance that q sits at the k-th open seat is z(1-z)^(k-1): the nearest open seat is the likeliest in every")
pr("   family, and any residue reading that moves a seat back one place trades a factor 1-z = 0.6 for a dip of a few hundredths.")
pr("   This is WHY nearest-first holds and why the stack (not the ordering) closes the range.")
pr("\n6b. RANGE FROM THE HAZARD (exact tie between the stack and the 90/99 table). z = (1/ln x) x prod r/(r-1) over the stack (the share of")
pr("   open seats that are prime); seats to 90% = ceil(ln 0.1 / ln(1-z)), to 99% = ceil(ln 0.01 / ln(1-z)); first-named share = z.")
def predict(rules, lo, hi):
    x = math.sqrt(lo * hi); z = (1 / math.log(x)) * math.prod(r / (r - 1) for r in rules)
    return z, math.ceil(math.log(0.1) / math.log(1 - z)), math.ceil(math.log(0.01) / math.log(1 - z))
PRED = {}
for rules in [(2, 3), (2, 3, 5), (2, 3, 5, 7), (2, 3, 5, 7, 11), (2, 3, 5, 7, 11, 13), (2, 3, 5, 7, 11, 13, 17, 19, 23)]:
    cells = []
    for lo, hi in BANDS:
        z, a, b = predict(rules, lo, hi); PRED[(rules, lo)] = (a, b, z)
        cells.append(f"z {z:.3f} -> {a:2d}/{b:2d}")
    pr(f"     {str(rules):<34} | " + " | ".join(f"{c:>18}" for c in cells))
pr("   (measured in 7 below; the same fact by a different route: Mertens' product and the prime density.)\n")

# ---------------------------------------------------------------- range closing with the two-part orderings
def band_ranks(lo, hi, rules, order):
    ranks = []
    for p, q in SPLITS:
        if p < lo or p < max(rules): continue
        if p >= hi: break
        h_true = (q - p) // 2
        if h_true > H_MAX: continue
        alive = open_mask(p, HS, rules)
        assert alive[h_true - 1]
        scores = order(p, HS)
        s = scores[h_true - 1]
        before = alive & ((scores > s) | ((scores == s) & (HS < h_true)))
        ranks.append(1 + int(before.sum()))
    r = np.array(ranks)
    return int(np.percentile(r, 90, method="higher")), int(np.percentile(r, 99, method="higher")), r.mean(), (r == 1).mean()

# learned table (fair: read below the band) P(h | p mod 30) from the band below, as an upper bound for residue readings
def learn(lo, hi, rules, key):
    hit = defaultdict(lambda: np.zeros(H_MAX)); opn = defaultdict(lambda: np.zeros(H_MAX))
    for p, q in SPLITS:
        if p < lo or p < max(rules): continue
        if p >= hi: break
        h_true = (q - p) // 2
        if h_true > H_MAX: continue
        al = open_mask(p, HS, rules); k = key(p)
        opn[k] += al; hit[k][h_true - 1] += 1
    return {k: (hit[k] + 0.5) / (opn[k] + 1.0) for k in hit}
def learned_order(table, key):
    return lambda p, H: table.get(key(p), np.zeros(H_MAX))[H - 1]
def demote(rs, eps):
    def f(p, H):
        s = -H.astype(float)
        for r in rs: s -= eps * (H % r == 0)
        return s
    return f
pr("7. RANGE CLOSING (90% / 99% seats, mean rank, share named first) per band. Stack = seat rules; orderings on the open seats:")
pr(f"     {'stack / ordering':<46} | {'[1e3,1e4)':>22} | {'[1e4,1e5)':>22} | {'[1e5,1e6)':>22}")
RES = {}
def show(name, rules, order):
    cells = []
    for lo, hi in BANDS:
        r90, r99, mean, first = band_ranks(lo, hi, rules, order)
        RES[(name, lo)] = (r90, r99, mean, first)
        cells.append(f"{r90:3d}/{r99:3d} {mean:5.2f} {first:.3f}")
    pr(f"     {name:<46} | " + " | ".join(f"{c:>22}" for c in cells))
nearest = lambda p, H: -H.astype(float)
for rules in [(2, 3), RULES13, (2, 3, 5, 7, 11, 13, 17, 19, 23)]:
    show(f"{rules} nearest", rules, nearest)
assert RES[("(2, 3) nearest", 10 ** 5)][:2] == (9, 17) and RES[(f"{RULES13} nearest", 10 ** 5)][:2] == (5, 9)
pr("   two-part REPEAT reading on top of the stack to 13 (demote h = 0 mod r by eps seats):")
pr("   (eps < 1 cannot change an integer order; eps 1.2 moves the repeat seat one open place back, 2.2 two places)")
for rs, eps in [((3,), 1.2), ((3,), 2.2), ((3, 5), 1.2), ((5, 7, 11, 13), 1.2), ((3, 5, 7, 11, 13), 1.2)]:
    show(f"to 13, demote h=0 mod {rs} eps {eps}", RULES13, demote(rs, eps))
pr("   learned ceiling for residue readings (P(q at open seat h | key) read from the band below; first band learns on [1e2,1e3)):")
for kname, key in [("p mod 6", lambda p: p % 6), ("p mod 30", lambda p: p % 30), ("p mod 60", lambda p: p % 60)]:
    cells = []
    for (lo, hi), (llo, lhi) in zip(BANDS, [(10 ** 2, 10 ** 3)] + BANDS[:-1]):
        table = learn(llo, lhi, RULES13, key)
        r90, r99, mean, first = band_ranks(lo, hi, RULES13, learned_order(table, key))
        RES[(f"learned {kname}", lo)] = (r90, r99, mean, first)
        cells.append(f"{r90:3d}/{r99:3d} {mean:5.2f} {first:.3f}")
    pr(f"     {'to 13, learned P(h | ' + kname + ')':<46} | " + " | ".join(f"{c:>22}" for c in cells))
pr("   decimal unit line as the stack order (same number of rules as the size-order stack):")
show("(2, 3, 11) decimal line 1", (2, 3, 11), nearest)
show("(2, 3, 5) size order 1", (2, 3, 5), nearest)
show("(2, 3, 11, 101) decimal line 2", (2, 3, 11, 101), nearest)
show("(2, 3, 5, 7) size order 2", (2, 3, 5, 7), nearest)
show("(2, 3, 7, 11, 13, 101, 73, 137) decimal line to 10^4+1", (2, 3, 7, 11, 13, 101, 73, 137), nearest)
show("(2, 3, 5, 7, 11, 13, 17, 19) size order 8 rules", (2, 3, 5, 7, 11, 13, 17, 19), nearest)
pr("   predicted from the hazard (6b) vs measured, top band, nearest-first:")
for rules in [(2, 3), RULES13, (2, 3, 5, 7, 11, 13, 17, 19, 23)]:
    a, b, z = PRED[(rules, 10 ** 5)]; m = RES[(f"{rules} nearest", 10 ** 5)]
    pr(f"     {str(rules):<34} predicted {a:2d}/{b:2d} first {z:.3f} | measured {m[0]:2d}/{m[1]:2d} first {m[3]:.3f}")
    assert abs(a - m[0]) <= 1 and abs(b - m[1]) <= 1 and abs(z - m[3]) < 0.04
base = RES[(f"{RULES13} nearest", 10 ** 5)]
best = max((v[3], k) for k, v in RES.items() if k[1] == 10 ** 5 and k[0].startswith("to 13"))
pr(f"\n   Top band, stack to 13: nearest-first names first {base[3]:.4f}; best two-part / learned ordering {best[0]:.4f} ({best[1][0]}).")
pr("   Reading: the repeat reading (demote the same-seat hop) lowers the first-named share whenever it changes the order, and the")
pr("   learned ceiling (any reading from p mod 60 and h) does not pass nearest-first: with a near-flat hazard the order is settled,")
pr("   and the range closes by adding seat rules (strands of passed places), exactly as the hazard formula says. The decimal line")
pr("   names the same strands in a worse order (11 before 5: a 1/10 share before a 1/4 share), so size order stays the stack order.")
pr("\n   Lean: PRIMES_Fold_v1.0_11-20-2026/lean-two-parts_v1.0_11-26-2026/TwoParts.lean (halving_square, face_square, centre_gap, prime_one_picture,")
pr("   neighbour_up/down, candidate_shift, wing_add_centre, five_left_outs, repeat_three/five/seven, family_*, wing_centre_six_*, eleven_unit, repunit_mirror).")
pr(f"\n[{time.time() - T0:.0f}s]")
with open(os.path.join(HERE, "two-parts_v1.0_11-26-2026.txt"), "w") as f: f.write("\n".join(OUT) + "\n")

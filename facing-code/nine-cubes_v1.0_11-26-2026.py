# Fable, fifth run (tUrUq, 11-26-2026): "9 is a problem we have to face. cubing is too. its doing something that
# i cant quite put my finger on but 18 is showing it." and "lets go for the push again and see if we can add any strands."
# Author of the method: Turaq Rayn-McLean. Readings: halving k,k+1,k (neighbours), turn (copies), pictures c^2 - w^2 = n
# (faces), the |^ mark (|^x = x(base+1)), unit count u (1x1 = 2). FAIRNESS: a seat y > p is never factored to name it;
# a strand reads the SHAPE of y (is y + w^2 a square? is y a sum of two cubes?) or p's residues. isprime scores only.
import math, time, os
from functools import lru_cache
import numpy as np
from sympy import factorint, isprime, nextprime, prevprime, n_order

T0 = time.time()
HERE = os.path.dirname(os.path.abspath(__file__))
OUT = []
def pr(*a):
    s = " ".join(str(x) for x in a); print(s); OUT.append(s)

N = 10 ** 6 + 400
is_p = np.ones(N + 1, dtype=bool); is_p[:2] = False
for i in range(2, int(N ** 0.5) + 1):
    if is_p[i]: is_p[i * i::i] = False
P = np.flatnonzero(is_p)
SPLITS = [(int(p), int(q)) for p, q in zip(P, P[1:]) if 5 <= p < 10 ** 6]
BANDS = [(10 ** 3, 10 ** 4), (10 ** 4, 10 ** 5), (10 ** 5, 10 ** 6)]
def fac(n): return "x".join(f"{r}^{e}" if e > 1 else str(r) for r, e in sorted(factorint(n).items()))

@lru_cache(maxsize=None)
def u(n):                  # unit count: u(1),u(2),u(3) = 1,2,3; u(2k) = 2u(k); u(2k+1) = 2u(k) + u(k+1)
    if n <= 3: return n
    return 2 * u(n // 2) if n % 2 == 0 else 2 * u(n // 2) + u(n // 2 + 1)
def pictures(n):           # all (c, w), w >= 0, with c^2 - w^2 = n
    return [((a + n // a) // 2, (n // a - a) // 2) for a in range(1, math.isqrt(n) + 1) if n % a == 0 and (a + n // a) % 2 == 0]
def digits(n, b):
    d = []
    while n: d.append(n % b); n //= b
    return d[::-1] or [0]
def rev10(n): return int(str(n)[::-1])

pr("NINE, CUBES, 18 (Fable 5th run, 11-26-2026). Author of the method: Turaq Rayn-McLean.\n")

# ============================================================ 1. the square and the cube of the mark |^1
pr("1. THE SQUARE AND THE CUBE OF |^1 (|^1 = base + 1: 3 in base 2, 11 in base 10, 9 in base 8).")
pr("   (|^1)^2 = 1,2,1 in its own base; (|^1)^3 = 1,3,3,1 in its own base (the row 1 3 3 1). Checked for bases 2..40:")
for b in range(2, 41):
    sq, cu = (b + 1) ** 2, (b + 1) ** 3
    assert sq == b * b + 2 * b + 1 and cu == b ** 3 + 3 * b * b + 3 * b + 1
    if b >= 3: assert digits(sq, b) == [1, 2, 1]
    if b >= 4: assert digits(cu, b) == [1, 3, 3, 1]      # base 2 and 3 carry the 3s (27 = 11011_2, 64 = 2101_3)
for b in (2, 4, 8, 10, 16):
    pr(f"     base {b:2d}: |^1 = {b + 1:2d}, square {(b + 1) ** 2:4d} = {''.join(map(str, digits((b + 1) ** 2, b)))}_{b} = 1x{b}^2 + 2x{b} + 1,"
       f"  cube {(b + 1) ** 3:5d} = 1x{b}^3 + 3x{b}^2 + 3x{b} + 1  (base-{b} digits {''.join(map(str, digits((b + 1) ** 3, b)))})")
pr("   So 9 = 3^2 is 1,2,1 read in base 2 (his 1,2,1 picture of 3: 4 + 2 + 2 + 1), 81 = 9^2 is 1,2,1 in base 8, 121 = 11^2 in base 10.")
pr("   27 = 3^3 is 1,3,3,1 in base 2 (8 + 12 + 6 + 1); the 3s overflow in base 2 and print as 11011 (a palindrome: 3,0,3 with 3 = 11).")
pr("   Cubing lays the row 1 3 3 1: the turn of the turn of the mark is the third row of the triangle; 9 and 27 are the base-2 rows.\n")

# ============================================================ 2. 9 and 11: the two mirrors of decimal reversal
pr("2. 9 AND 11 ARE THE TWO MIRRORS OF DECIMAL REVERSAL (his m line from 11 on the nines).")
for n in range(10, 100):
    a, b_ = divmod(n, 10)
    assert n + rev10(n) == 11 * (a + b_) and n - rev10(n) == 9 * (a - b_)
pr("   two-digit n = 10a + b:  n + rev(n) = 11 x (a + b),   n - rev(n) = 9 x (a - b)   (checked 10..99; Lean rev_sum, rev_diff)")
pr("   base b: the two mirrors are b + 1 (|^1) and b - 1. Base 2: 3 and 1 (the 1 is invisible). Base 10: 11 and 9 = 3^2.")
pr("   9 is a square only because the base is 10 = 3^2 + 1: 9 = 10 - 1 is the digit-sum blind spot (10 = 1 mod 9), 11 = 10 + 1 the mark.")
rows = []
for k in range(1, 11):
    n = 9 * k; r = rev10(n) if k > 1 else 90
    assert r == 9 * (11 - k)
    rows.append(f"{n}<->{r}")
pr("   nines reversed: rev(9k) = 9 x (11 - k):  " + "  ".join(rows))
pr("   The 11-mirror k <-> 11 - k (2<->9, 3<->8, 4<->7, 5<->6, 1<->10) IS digit reversal on the nines. 09<->90 needs a leading zero;")
pr("   18 <-> 81 is the first honest pair: 2 x 9 reversed is 9 x 9. 27 <-> 72: 3^3 reversed is 2^3 x 3^2. 36 <-> 63, 45 <-> 54.")
pr("   This is what 18 shows: the first two-digit nine, 18 = 1,8 = ^1 + 2^3, reads backwards as the square of 9.\n")

# ============================================================ 3. pictures of squares and cubes
pr("3. PICTURES (c^2 - w^2 = n) OF SQUARES AND CUBES.")
for p in [q for q in range(3, 200, 2) if isprime(q)]:
    m = (p - 1) // 2
    assert pictures(p * p) == [((p * p + 1) // 2, (p * p - 1) // 2), (p, 0)]
    assert pictures(p ** 3) == [((p ** 3 + 1) // 2, (p ** 3 - 1) // 2), (p * (m + 1), p * m)]
    assert (p ** 3 - 1) // 2 == m * (p * p + p + 1) and (p ** 3 + 1) // 2 == (m + 1) * (p * p - p + 1)
pr("   p^2: two pictures, the halving and (p, 0): the square is a center with no wing (the turn p x p has block = center).")
pr("   p^3: two pictures, the halving and (p(m+1), p m) with p = 2m+1: the cube's own picture is p's halving m, m+1, m SCALED BY p.")
pr("        27 = 3 x (1,2,1) = (3,6,3): 6^2 - 3^2 = 27.  125 = 5 x (2,3,2): 15^2 - 10^2.  343 = 7 x (3,4,3): 28^2 - 21^2.")
pr("        The turn of a turn of p carries p's own halving picture, p times. (Same fact by a different route: p^3 = T_p^2 - T_(p-1)^2.)")
pr("   p^3 halving: wing (p^3-1)/2 = m x (p^2+p+1), center (p^3+1)/2 = (m+1) x (p^2-p+1): p's halving (m, m+1) times the two")
pr("        turn-neighbours p^2 +- p + 1. For 3: 27 = 13,14,13 = (1 x 13, 2 x 7, 1 x 13): the cube of 3 reads 7 and 13 in its neighbours.")
pr("        7 x 13 = 91 = 81 + 9 + 1 = 1,1,1 in base 9 (the 0-100 miss 91 is the 9-repunit of length 3; 1001 = 11 x 91).")
pr(f"   checked odd primes p < 200 (Lean cube_picture, cube_halving).\n")

# ============================================================ 4. squares against the walls
pr("4. SQUARES AGAINST THE WALLS (self-count u(n) = n at 2^a and 3 x 2^a).")
walls = {2 ** a for a in range(25)} | {3 * 2 ** a for a in range(25)}
on_wall = [p for p in map(int, P[P < 1000]) if p * p - 1 in walls]
assert on_wall == [2, 3, 5, 7]       # 4 = 3 + 1 too: the even prime's square sits one past the wall 3
pr("   p^2 - 1 = (p-1)(p+1) is a wall exactly for p = 3, 5, 7:  9 = 2^3 + 1,  25 = 3x2^3 + 1,  49 = 3x2^4 + 1 (checked p < 1000;")
pr("   proof: two powers of 2 differ by 2 only at 2, 4; 2^x and 3x2^y differ by 2 only at 4,6 and 6,8). So the squares of 3, 5, 7 sit")
pr("   one past a wall, on the two proven strands (u(9) = 15 = 2^4 - 1, u(25) = 46 = 2(24 - 1), u(49) = 94 = 2(48 - 1)); no larger square does.")
assert u(9) == 15 and u(25) == 46 and u(49) == 94
pr("   7 x 7 = 5 x 10 - 1 (his) and 7 x 7 = 3 x 16 + 1: 49 touches the 5-line from above and the 3-wall from below.")
us = [u(3 ** k) for k in range(8)]
pr(f"   u(3^k), k = 0..7: {us}   = {[fac(x) for x in us]}")
assert us[3] == 64 and us[4] == 216
pr("   u(27) = 64 = 4^3 and u(81) = 216 = 6^3: the unit count of the cube and the fourth turn of 3 are cubes (of 4 and 6);")
pr(f"   u(243) = {us[5]} = {fac(us[5])} is not a cube: the run stops at two. A reading, not a law.")
pr(f"   u(2 x 3^k) = 2 u(3^k): 18 counts {u(18)} = 2 x 15 (the even line is the odd line doubled; 18 sits below 2n = 36 as 9 sits below 18).\n")

# ============================================================ 5. the lake (1/n) of the turn tower
pr("5. THE LAKE IMAGE OF 9, 27, 81, 243 (decimal 1/n): period of 1/3^k = 3^(k-2) for k >= 2.")
for k in range(2, 8):
    assert n_order(10, 3 ** k) == 3 ** (k - 2)
pr("   1/9 = 0.(1), 1/27 = 0.(037), 1/81 = 0.(012345679), 1/243 period 27, 1/729 period 81: the lake of a turn of turns is a turn of")
pr("   turns two levels down (checked k = 2..7; Lean period_27, period_81). 1/81 prints the digits 0..9 with the 8 = 2^3 missing.")
assert 999 == 27 * 37 and 1001 == 7 * 11 * 13 and 10 ** 6 - 1 == 3 ** 3 * 7 * 11 * 13 * 37
pr("   Cubing the base: 10^3 - 1 = 999 = 9 x 111 = 27 x 37 (3^3 appears), 10^3 + 1 = 1001 = 7 x 11 x 13. His 3-digit pictures")
pr("   (111,121,111; 444,555,444) live on these two mirrors: a,b,a with 3-digit blocks = 10^6 a + 10^3 b + a = a + b + a mod 999.")
for n in [111121111, 444555444]:
    bl = [n // 10 ** 6, (n // 1000) % 1000, n % 1000]
    assert n % 999 == sum(bl) % 999
v3 = lambda n: 0 if n % 3 else 1 + v3(n // 3)
assert all(v3((10 ** n - 1) // 9) == v3(n) for n in range(1, 200))
pr("   Repunits: the 3-power carried by (n ones) equals the 3-power carried by n (checked n < 200): 111 carries one 3, nine ones carry 9,")
pr("   27 ones carry 27. The turn of a turn of ones carries the turn of the turn.\n")

# ============================================================ 6. 18, the split centers, the cube-sum strand
pr("6. WHAT 18 SHOWS.")
cents = [(p + q) // 2 for p, q in SPLITS[:7]]
pr(f"   split centers of 5|7, 7|11, 11|13, 13|17, 17|19, 19|23, 23|29: {cents}: six centers in a row step 3 (6, 9, ..., 21), then 26.")
assert cents[:6] == [6, 9, 12, 15, 18, 21]
pr("   9 = center of 7|11 (half gap 2); 18 = 7 + 11 = center of 17|19 (half gap 1): 18 is the sum of the split whose center is 9 and")
pr("   the center of the split 17|19. 27 = 26 + 1 sits one past the first center off the 3-run (23|29).")
e2_only = [n for n in range(6, 80, 4) if not isprime(n // 2)]
assert e2_only[0] == 18
pr(f"   18 = 2 x 9 is the first 2 x odd that is not 2 x prime (first E2-only seat): {e2_only[:6]} ...; 9 is the first odd composite.")
pr("   m line: 11 - 2 = 9, 22 - 4 = 18: the even prime 2 and its square 4 land on 9 and 18.")
cubes = sorted({a ** 3 + b ** 3 for a in range(1, 101) for b in range(1, a + 1)})
cubes = [c for c in cubes if c <= 10 ** 6]
assert [c for c in cubes if isprime(c)] == [2]
pr(f"   SUM OF TWO CUBES a^3 + b^3 = (a + b)(a^2 - ab + b^2): composite unless a = b = 1 (1 x 1 x 1 + 1 x 1 x 1 = 2, the even prime).")
pr(f"   The strand: {cubes[:16]} ...  ({len(cubes)} members to 1e6, 2 the only prime, checked). 2 and 9 are its first two members:")
pr("   the even prime and the first odd composite, his pair 2 <-> 9 under 11. 9 = 2^3 + 1 is BOTH |^^^1 (the 2^a + 1 strand) and a cube sum.")
pr("   Members among the early misses: 91 = 4^3 + 3^3 (= 7 x 13), 65 = 4^3 + 1, 133 = 5^3 + 2^3, 341 = 6^3 + 5^3, 1001 = 10^3 + 1, 1729 = 12^3 + 1 = 10^3 + 9^3.\n")

# ============================================================ 7. STRANDS: pictures with a small wing, cube sums/differences
pr("7. NEW STRANDS (fair shape readings of the seat y; the stack is the residue rules). y is CLOSED when")
pr("   (S) y = c^2 (square strand, wing 0: the pentagonal wing 12P reads it);  (P_W) y + w^2 = c^2 for some 1 <= w <= W with c - w >= 2")
pr("   (a second picture with a small wing: y = (c-w)(c+w));  (C) y = a^3 + b^3, a >= b >= 1, not 1,1;  (D) y = a^3 - b^3, a - b >= 2.")
pr("   Each is proven composite by its own algebra (Lean picture_closed, cube_sum_closed). Stack to r closes every composite with a")
pr("   block <= r; pictures to W close every composite with two faces <= 2W apart. Left open: a x b with a > r and b - a > 2W.\n")
CUBE_SET = set(cubes)
DIFF_SET = {a ** 3 - b ** 3 for a in range(3, 101) for b in range(1, a - 1)}
def closed_shape(y, W, sq, cube):
    if sq and math.isqrt(y) ** 2 == y: return True
    for w in range(1, W + 1):
        v = y + w * w; c = math.isqrt(v)
        if c * c == v and c - w >= 2: return True
    return cube and (y in CUBE_SET or y in DIFF_SET)
def first_miss(rules, W, sq, cube, limit=10 ** 6):
    for p, q in SPLITS:
        if p < max(rules): continue
        if p > limit: return None, None
        y = p + 2
        while True:
            if all(y % r for r in rules) and not closed_shape(y, W, sq, cube):
                break
            y += 2
        if y != q: return p, y
STACKS = [(2, 3), (2, 3, 5), (2, 3, 5, 7), (2, 3, 5, 7, 11), (2, 3, 5, 7, 11, 13), (2, 3, 5, 7, 11, 13, 17, 19, 23)]
pr("7a. MAPPED OUT TO x: first prime p whose first open seat is not the next prime (the first unclosed composite y), per stack x strand set.")
pr(f"     {'stack':<30} | {'bare':>12} | {'+S':>12} | {'+S+P_1':>12} | {'+S+P_3':>12} | {'+S+P_10':>12} | {'+S+P_30':>12} | {'+S+P_10+C+D':>12}")
MAP = {}
for rules in STACKS:
    cells = []
    for (W, sq, cube) in [(0, False, False), (0, True, False), (1, True, False), (3, True, False), (10, True, False), (30, True, False), (10, True, True)]:
        p, y = first_miss(rules, W, sq, cube)
        MAP[(rules, W, sq, cube)] = (p, y)
        cells.append(f"{p}->{y}" if p else "none<1e6")
    pr(f"     {str(rules):<30} | " + " | ".join(f"{c:>12}" for c in cells))
# exact formula for the first unclosed composite when both faces are prime
for rules in STACKS:
    for W in (1, 3, 10):
        p1 = nextprime(max(rules)); y_formula = p1 * nextprime(p1 + 2 * W + 1)
        p, y = MAP[(rules, W, True, False)]
        if y != y_formula: pr(f"     formula p1 x nextprime(p1 + 2W + 1) = {y_formula} vs measured {y} for stack to {max(rules)}, W = {W}")
assert MAP[((2, 3, 5, 7), 0, False, False)] == (113, 121) and MAP[((2, 3, 5, 7, 11, 13), 0, False, False)] == (283, 289)
assert MAP[((2, 3, 5, 7, 11, 13), 0, True, False)][1] == 323 and MAP[((2, 3), 0, False, False)][1] == 25
pr("   Reading: bare stack to r is mapped to nextprime(r)^2 - 1 (121, 169, 289); the square strand pushes it to p1 x p2 (twin products");
pr("   323 = 17 x 19); pictures to W push it to p1 x nextprime(p1 + 2W + 1) when both faces are prime (deviations printed above, if any).")
pr("   0-100 with (2,3) alone misses 25, 49, 77, 91: all four are pictures with wing <= 3 (25 = 5^2, 49 = 7^2, 77 = 9^2 - 2^2, 91 = 10^2 - 3^2).\n")

# ============================================================ 8. range closing with the strands
H_MAX = 80
HS = np.arange(1, H_MAX + 1)
def shape_mask(ys, W, sq, cube):
    closed = np.zeros(len(ys), dtype=bool)
    if sq:
        s = np.sqrt(ys.astype(float)).round().astype(np.int64); closed |= (s * s == ys)
    for w in range(1, W + 1):
        v = ys + w * w; s = np.sqrt(v.astype(float)).round().astype(np.int64)
        closed |= (s * s == v) & (s - w >= 2)
    if cube:
        closed |= np.isin(ys, list(CUBE_SET | DIFF_SET))
    return closed
def band_ranks(lo, hi, rules, W, sq, cube):
    ranks = []
    for p, q in SPLITS:
        if p < lo or p < max(rules): continue
        if p >= hi: break
        h_true = (q - p) // 2
        if h_true > H_MAX: continue
        ys = p + 2 * HS
        alive = np.ones(H_MAX, dtype=bool)
        for r in rules: alive &= (ys % r != 0)
        if W or sq or cube: alive &= ~shape_mask(ys, W, sq, cube)
        assert alive[h_true - 1]
        ranks.append(1 + int(alive[:h_true - 1].sum()))
    r = np.array(ranks)
    return int(np.percentile(r, 90, method="higher")), int(np.percentile(r, 99, method="higher")), r.mean(), (r == 1).mean(), len(r)
pr("8. RANGE CLOSING (90% / 99% seats, mean rank, share named first), nearest-first on the open seats, per band:")
pr(f"     {'stack + strands':<44} | {'[1e3,1e4)':>22} | {'[1e4,1e5)':>22} | {'[1e5,1e6)':>22}")
RES = {}
for rules in [(2, 3), (2, 3, 5, 7, 11, 13), (2, 3, 5, 7, 11, 13, 17, 19, 23)]:
    for (W, sq, cube, tag) in [(0, False, False, ""), (0, True, False, " +S"), (10, True, False, " +S+P_10"), (30, True, True, " +S+P_30+C+D")]:
        cells = []
        for lo, hi in BANDS:
            r90, r99, mean, first, n = band_ranks(lo, hi, rules, W, sq, cube)
            RES[(rules, tag, lo)] = (r90, r99, mean, first)
            cells.append(f"{r90:3d}/{r99:3d} {mean:5.2f} {first:.4f}")
        pr(f"     {str(rules) + tag:<44} | " + " | ".join(f"{c:>22}" for c in cells))
base = RES[((2, 3, 5, 7, 11, 13), "", 10 ** 5)]; full = RES[((2, 3, 5, 7, 11, 13), " +S+P_30+C+D", 10 ** 5)]
pr(f"   Top band, stack to 13: first-named share {base[3]:.4f} bare -> {full[3]:.4f} with S + P_30 + C + D; mean rank {base[2]:.3f} -> {full[2]:.3f}.")
assert full[3] >= base[3] and full[2] <= base[2]
pr("   Reading: the shape strands are exact and run without end, but they are thin (squares ~ 1/(2 sqrt y) of seats, pictures to W ~ W/sqrt y,")
pr("   cube sums ~ y^(-1/3)); in the top band they move the 90/99 seats by 0 and the first-named share by a few thousandths. They close the")
pr("   LOW end exactly (the 'mapped out to x' table), not the top band; the stack (residue rules) is what closes the range, as the hazard said.")
# what the open composites look like above the stack: both faces > 13 and far apart
pr("\n   Composites left open by stack-to-13 + S + P_30 in [1e5, 1e5 + 2e4] (first eight, with faces):")
left = []
y = 10 ** 5 + 1
while len(left) < 8:
    if all(y % r for r in (2, 3, 5, 7, 11, 13)) and not isprime(y) and not closed_shape(y, 30, True, True):
        left.append(f"{y} = {fac(y)}")
    y += 2
pr("     " + "; ".join(left))
pr("   (two faces far apart: the gap between them is what neither the stack nor a small-wing picture reaches.)")

open(os.path.join(HERE, "nine-cubes_v1.0_11-26-2026.txt"), "w").write("\n".join(OUT) + f"\n\n[{time.time() - T0:.0f}s]\n")
print(f"[{time.time() - T0:.0f}s]")

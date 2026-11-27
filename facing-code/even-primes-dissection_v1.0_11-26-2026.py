# Even primes dissected (tUrUq, 11-26-2026). Three readings side by side:
#   E1 = 2p, p an odd prime (prime place on the even line, 2 = the unit, place k at 2k)
#   E2 = prime inside the evens alone = not a product of two evens = n = 2 mod 4, n != 2
#   E3 = even mirror of an odd prime under offset 11 (carried 11 - p, and per-block (2j+1)*11 - p)
# Imports (unchanged): even-primes, unified-code, missing-wings, dual-forms, standard-mirror-line.
# asymmetric-tell runs its whole study on import, so its R1 rule (mirror at the walker) is restated here.
# Writes even-primes-dissection_v1.0_11-26-2026.txt beside this file. Runs in well under a minute.
import importlib.util, os, math
from fractions import Fraction as Fr
from collections import Counter
from functools import lru_cache
from sympy import isprime, primerange

HERE = os.path.dirname(os.path.abspath(__file__))
def load(name, tag):
    s = importlib.util.spec_from_file_location(tag, os.path.join(HERE, name + "_v1.0_11-26-2026.py"))
    m = importlib.util.module_from_spec(s); s.loader.exec_module(m); return m
ep, uc, mw = load("even-primes", "ep"), load("unified-code", "uc"), load("missing-wings", "mw")
df, sm = load("dual-forms", "df"), load("standard-mirror-line", "sm")

out = []
def P(*a):
    s = " ".join(str(x) for x in a); print(s); out.append(s)

N = 10 ** 6
spf = list(range(N + 1))                       # smallest factor table (for factoring counts only)
for i in range(2, int(N ** 0.5) + 1):
    if spf[i] == i:
        for j in range(i * i, N + 1, i):
            if spf[j] == j: spf[j] = i
oddprime = lambda n: n > 2 and spf[n] == n
E1 = lambda n: n % 2 == 0 and oddprime(n // 2)
E2 = lambda n: n % 4 == 2 and n != 2
v2 = lambda n: (n & -n).bit_length() - 1
assert all(E2(n) == ep.even_world_prime(n) for n in range(2, 400))

# ---------------- 1. unified code (w, c, w; commas = levels) ----------------
P("== 1. Unified code ==")
for p in (3, 5, 7, 9, 11, 13):
    P(f"  2x{p} = {2*p}: 1 down {uc.write(2*p, 1)} | 2 down {uc.write(2*p, 2)}   ({p} 1 down: {uc.write(p, 1)})")
# exact: the left third of 2n written L+1 down is n written L down; middle third is 0 written L down.
for n in range(1, 300):
    for L in range(1, 5):
        s = uc.write(2 * n, L + 1); parts = s.split("," * (L + 1))
        assert parts == [uc.write(n, L), uc.write(0, L), uc.write(n, L)], (n, L)
P("  proven-by-build (checked n < 300, 1..4 levels): code(2n) one level further down = code(n) ,,,hinge block of zeros,,, code(n).")
P("  So 2p is p's code zoomed one level, two copies around an empty block. 4k = 2k,0,2k: its wings are again hinges.")
def centres(n):                                 # centre digit at each level, top down
    c = []
    while n: c.append(n % 2); n //= 2
    return c
P("  centre chain top-down (= base-2 digits from the bottom): E2 opens 0,1 ; 4k opens 0,0 ; odd opens 1.")
P("   ", ", ".join(f"{n}:{''.join(map(str, centres(n)))}" for n in (6, 10, 14, 18, 22, 26, 30, 4, 8, 12)))
P("  E1 vs E2-only (14 vs 18) are not told apart by the chain: the prime question sits in the odd wing, one level down.")
# T face (dual forms)
eq_turn_E1 = [n for n in range(6, 20000, 2) if E1(n) and n % 3 == 0]
assert eq_turn_E1 == [6]
P("  dual forms: an E1 2p has an equal turn face k,k,k only when 3 | 2p, i.e. p = 3: 6 = 3,0,3:2 = 2,2,2:3 (proven).")
P("   E1 faces:", ", ".join(f"{n}={df.t_top(n)}" for n in (10, 14, 22, 26, 34, 38)),
  "| E2-only with turn faces:", ", ".join(f"{n}={df.t_top(n)}" for n in (18, 30, 42, 54, 66)))
P("   E1 2p, p = 1 mod 3 -> near-turn t+1,t,t+1 ; p = 2 mod 3 -> t,t+1,t (checked p < 20000).")
for p in primerange(5, 20000):
    t = df.t_top(2 * p); assert (t[0] == t[1] + 1) == (p % 3 == 1)

# ---------------- 2. the even line as its own line ----------------
P("\n== 2. The even line (place k at 2k; places multiply a (x) b = 2ab) ==")
P("  Its own primes under its own product: place k is a (x) b exactly when k is even, so its primes are the odd places k >= 3.")
P("  -> E2 = the whole odd line one zoom up, prime odds and composite odds alike (3,5,7,9,11,13,15,... at 6,10,14,18,22,26,30).")
E2s = [n for n in range(6, N + 1, 4)]
assert all(E2(n) for n in E2s) and len(E2s) == sum(1 for n in range(2, N + 1) if E2(n))
P(f"  E2 gaps: every consecutive E2 gap is 4 (proven: n = 2 mod 4). Count to 1e6: {len(E2s)} = (10^6 - 2)/4 exactly.")
P("  R1 mirror at the walker on E2: from n stand at n+2 (a 4k seat), mirror n+4 is open at once; both sides of every")
P("   E2 seat are 4k seats (n-2, n+2): no broken side. The odd line's broken side has no copy here.")
# Factoring in the even world: n = 2^a * m, m odd. Every E-prime (2 included) carries exactly one 2,
# so a factoring uses exactly a atoms 2*m_i with prod m_i = m (m_i odd >= 1; m_i = 1 is the atom 2).
@lru_cache(None)
def mparts(m, k, lo):  # unordered factorings of m into at most k factors >= lo (factor 1 not used)
    if m == 1: return 1
    if k == 0: return 0
    t = 1 if m >= lo else 0
    d = lo
    while d * d <= m:
        if m % d == 0: t += mparts(m // d, k - 1, d)
        d += 2 if lo % 2 else 1
    return t
@lru_cache(None)
def mparts_exact(m, k, lo):  # into exactly k factors >= lo
    if k == 0: return 1 if m == 1 else 0
    if k == 1: return 1 if m >= lo else 0
    t, d = 0, lo
    while d ** k <= m:
        if m % d == 0: t += mparts_exact(m // d, k - 1, d)
        d += 2
    return t
def sig(m):
    e = Counter()
    while m > 1: e[spf[m]] += 1; m //= spf[m]
    return tuple(sorted(e.values(), reverse=True))
ODDP = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]
def rep(s): return math.prod(q ** e for q, e in zip(ODDP, s))
def ways(n, with2=True):
    a, m = v2(n), n >> v2(n)
    r = rep(sig(m))
    return mparts(r, a, 3) if with2 else mparts_exact(r, a, 3)
for n in range(4, 400, 2):                      # cross-check with the imported brute force
    assert ways(n) == len(ep.even_world_factorings(n)) or E2(n), n
    if not E2(n): assert ways(n) == len(ep.even_world_factorings(n)), n
P("  Ways to build n = 2^a*m from E-primes (2 counted as the atom 2x1) = ways to split the odd part m into at most a")
P("   odd pieces (checked against even-primes.even_world_factorings, n < 400). Without 2: exactly a pieces each >= 3.")
cnt = Counter(); first = {}; first_no2 = {}; rec = []; best = 0; zero_no2 = 0; cnt_no2 = Counter()
for n in range(2, N + 1, 2):
    w = ways(n); cnt[w] += 1; first.setdefault(w, n)
    w0 = ways(n, False); cnt_no2[w0] += 1; first_no2.setdefault(w0, n); zero_no2 += (w0 == 0)
    if w > best: best = w; rec.append((n, w))
P("  first even with k ways (2 allowed):", {k: first[k] for k in sorted(first)[:12]})
P("  first even with k ways (no 2):     ", {k: first_no2[k] for k in sorted(first_no2)[:12]})
P("  count distribution to 1e6 (2 allowed), k: numbers:", dict(sorted(cnt.items())[:14]), "... max", max(cnt))
P(f"  evens to 1e6 with no build at all without the atom 2 (fewer odd pieces than 2s, e.g. 4, 8, 12, 20): {zero_no2}")
P("  record setters (2 allowed):", rec)
def hcn(lim):
    out_, b = [], 0
    for n in range(1, lim + 1):
        t = 1; x = n
        while x > 1:
            p_ = spf[x]; e = 0
            while x % p_ == 0: x //= p_; e += 1
            t *= e + 1
        if t > b: b = t; out_.append(n)
    return out_
H = hcn(N)
P("  highly composite (antiprimes) to 1e6:", H)
P("  records that are also antiprimes:", [n for n, _ in rec if n in set(H)])
P("  records' shape (a = 2s, odd part):", [(n, v2(n), n >> v2(n)) for n, _ in rec])
# a = 2: ways = ceil(tau(m)/2)
def tau(m):
    t = 1
    for e in sig(m): t *= e + 1
    return t
assert all(ways(4 * m) == (tau(m) + 1) // 2 for m in range(1, 50000, 2))
P("  exact (checked m odd < 50000): ways(4m) = ceil(tau(m)/2) = the divisor pairs of the odd part.")

# ---------------- 3. densities and gaps of E1, E2; the split ----------------
P("\n== 3. Densities, gaps, splits to 1e6 ==")
e1 = [n for n in range(6, N + 1, 4) if E1(n)]
P(f"  E1 count {len(e1)}, E2 count {len(E2s)}, E2-only (2 x odd composite) {len(E2s) - len(e1)}")
for top in (10 ** 2, 10 ** 3, 10 ** 4, 10 ** 5, 10 ** 6):
    a_ = sum(1 for n in e1 if n <= top); b_ = (top - 2) // 4
    P(f"   to {top:>7}: E1 {a_:6d} ({Fr(a_, top)} = {a_/top:.5f}), E2 {b_:6d} ({b_/top:.5f}), E1 share of E2 {a_/b_:.4f}")
oddp = [p for p in range(3, N // 2 + 1) if oddprime(p)]
g_odd = Counter(q - p for p, q in zip(oddp, oddp[1:])); g_e1 = Counter(b - a for a, b in zip(e1, e1[1:]))
assert all(g_e1[2 * g] == c for g, c in g_odd.items()) and sum(g_e1.values()) == sum(g_odd.values())
P("  E1 gaps = 2 x odd-prime gaps exactly (in place units the same gaps, one zoom up). Top E1 gaps:", g_e1.most_common(6))
P("   E1 largest gap to 1e6:", max(g_e1), "(odd line", max(g_odd), ")")
splits = [n for n in range(6, 400, 4) if not E1(n)]
P("  split points (E2 not E1 = 2 x odd composite):", splits[:20])
fresh = [2 * p * p for p in primerange(3, 40)]
P("  fresh splits (first E2-only whose odd part has smallest prime p = 2p^2):", fresh)
assert all(min(n for n in range(6, 2 * p * p + 1, 4) if not E1(n) and spf[n // 2] == p) == 2 * p * p for p in primerange(3, 40))
runs = []; r = 0
for n in E2s:
    r = r + 1 if E1(n) else 0; runs.append(r)
P(f"  longest run of consecutive E2 that are all E1: {max(runs)} (6, 10, 14 = 2x3, 2x5, 2x7); runs of 2 to 1e6: "
  f"{sum(1 for a, b in zip(E2s, E2s[1:]) if E1(a) and E1(b))} (= odd twin pairs)")
assert max(runs) == 3

# ---------------- 4. mirrors E3 ----------------
P("\n== 4. Mirrors ==")
cls = lambda n: "E1" if E1(n) else "E2only" if E2(n) else "4k" if n % 4 == 0 else "odd"
P("  offset 11, first block:", {p: (11 - p, cls(11 - p)) for p in (2, 3, 5, 7)})
# carried mirror 11 - p (negative past 11): read |p - 11|
car = Counter()
for p in oddp:
    if p == 11: continue
    m_ = abs(11 - p); car[(p % 4, "E2" if m_ % 4 == 2 else "4k")] += 1
    if m_ % 4 == 2: car[(p % 4, "E1")] += E1(m_)
P("  carried 11 - p, by p mod 4 (odd primes to 5e5):", dict(car))
assert car[(3, "E2")] == 0 and car[(1, "4k")] == 0
P("  proven: 11 = 3 mod 4, so 11 - p = 2 mod 4 iff p = 1 mod 4. The carried offset-11 mirror sends every circle prime")
P("   (1 mod 4, sum of two squares) onto an E2 seat and every 3 mod 4 prime onto a 4k seat. 5 -> 6, 3 -> 8, 7 -> 4.")
blk = Counter()
for p in oddp:
    if p == 11: continue
    b = sm.block_mirror(p); j = (p - 1) // 11
    blk[(j % 2, p % 4, cls(b))] += 1
P("  per-block mirror (2j+1)*11 - p, keyed (block parity, p mod 4, landing):")
for k in sorted(blk): P("    ", k, blk[k])
assert all(c == 0 or (k[2] in ("E1", "E2only")) == ((k[0] == 0) == (k[1] == 1)) for k, c in blk.items())
P("  proven: block j even -> circle primes land on E2, block j odd -> 3 mod 4 primes land on E2; the blocks alternate.")
le = sum(c for k, c in blk.items() if k[2] == "E1"); lo = sum(c for k, c in blk.items() if k[2] == "E2only")
P(f"  of E2 landings: E1 {le}, E2-only {lo} (E1 landing = (2j+1)*11 = p + 2r, r prime; same fact by a different")
P("   route in Lemoine's odd = p + 2q).")
# imaginary side: each odd prime has one E2 neighbour and one 4k neighbour
side = Counter()
for p in oddp[1:]:
    e2n = p + 1 if (p + 1) % 4 == 2 else p - 1
    side[("right" if e2n == p + 1 else "left", "E1" if E1(e2n) else "E2only")] += 1
P("  each odd prime p > 3 has its E2 neighbour on one side only: right (p+1) for 1 mod 4, left (p-1) for 3 mod 4:", dict(side))
wings = mw.lay_strands(N // 4 + 5)
assert all((wings[w] == 0) == oddprime(2 * w + 1) for w in range(1, N // 4))
P("  open wing w even (circle primes) <-> 2w = p-1 is a 4k seat; open wing w odd <-> 2w = p-1 is an E2 seat.")
P("   So the imaginary side (sums of two squares) is where the wing doubles onto a 4k seat; even primes (E2) sit")
P("   on the left of the 3 mod 4 primes and on the right of the circle primes.")

# ---------------- 5. fractions: down into scale ----------------
P("\n== 5. Down into scale (2k -> k -> k/2 ...) ==")
P("  every E2 meets the odd line after exactly one halving (v2 = 1): E1 meets its odd prime, E2-only an odd composite.")
P("  next step down: p/2 = w + 1/2 (the wing plus half the centre unit): 14 -> 7 -> 7/2 = 3 + 1/2 ; 18 -> 9 -> 4 + 1/2.")
P("  4k need v2 >= 2 halvings; the depth equals the number of hinge levels in the unified code (centre chain zeros).")
P("  fraction reading 2k <-> 1/k: E1 <-> 1/p, E2 <-> 1/odd; the place product 2ab <-> (1/2)(1/a)(1/b):")
P("   each even multiplication = unit fractions multiplied and halved once (2 as the halving mover).")
for k in range(1, 60, 2):
    for j in range(1, 60):
        assert Fr(1, 2 * k * j) == Fr(1, 2) * Fr(1, k) * Fr(1, j)
for n in range(6, 20000, 4):
    assert n // 2 % 2 == 1 and centres(n)[:2] == [0, 1]

# ---------------- 6. the oddity ----------------
P("\n== 6. The oddity: primality and factoring trade places ==")
P("  odd line: primes thin (odd primes to 5e5: %d, share %.5f), factoring is single." % (len(oddp), len(oddp) / (N // 2)))
P("  even line (own product): primes are a fixed quarter of all numbers, gap always 4, no broken side;")
P("   factoring is not single and the number of ways = splits of the odd part into at most v2 pieces.")
P(f"  first k-way evens: 2 -> {first[2]}, 3 -> {first[3]}, 4 -> {first[4]}, 5 -> {first[5]}; max ways to 1e6: {max(cnt)} at {first[max(cnt)]}")
absent = [k for k in range(1, max(cnt)) if k not in cnt]
P("  way-counts that no even <= 1e6 has:", absent[:12], f"... ({len(absent)} of 1..{max(cnt)-1})")
P("  13 ways only at:", [n for n in range(2, N + 1, 2) if ways(n) == 13], "(2^5*3^7, 4*3^4*5^4, 4*3^4*7^4)")
assert 17 in absent and 22 in absent and cnt[13] == 3
P("  The odd line's prime/composite split reappears in the even line only as how many builds a number has:")
P("   2p^1 (E2) 1 build, 4p 1 build, 4pq 2 builds, 4p^2 2 builds; E1 and E2-only look the same from inside the evens.")
open(os.path.join(HERE, "even-primes-dissection_v1.0_11-26-2026.txt"), "w").write("\n".join(out) + "\n")

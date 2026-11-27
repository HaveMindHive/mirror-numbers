# Layered method (11-26-2026): layers L = 2, 3, 5, 7 read through the unit count
# u(2k)=2u(k), u(2k+1)=2u(k)+u(k+1), u(1..3)=1,2,3. Imports the ladder shorthand (does not change it).
# Writes layered-method-table_v1.0_11-26-2026.txt beside this file. Runs in about a minute.
import importlib.util
from fractions import Fraction as Fr
from collections import Counter
from sympy import isprime, primerange

HERE = __file__.rsplit("/", 1)[0]
sp = importlib.util.spec_from_file_location("lad", f"{HERE}/ladder-shorthand_v1.0_11-26-2026.py")
lad = importlib.util.module_from_spec(sp); sp.loader.exec_module(lad)

def pair(n):  # (u(n), u(n+1)) without a cache, any size
    if n <= 3: return (n, (0, 2, 3, 4)[n] if n else 1)
    a, b = pair(n // 2)
    return (2 * a, 2 * a + b) if n % 2 == 0 else (2 * a + b, 2 * b)
U = lambda n: pair(n)[0]
assert all(U(n) == lad.u(n) for n in range(0, 5000))
def v2(x):
    c = 0
    while x and x % 2 == 0: x //= 2; c += 1
    return c
depth = lambda n: v2((n >> v2(n)) - 1)  # midpoint depth of the odd core
LAY = (2, 3, 5, 7)
out = []; P = lambda *a: out.append(" ".join(str(x) for x in a))

# ---- 1. the L-world: 1 (x) 1 = L, split point, first double factorings ----
def doubles(L, withL, lim=600):
    el = [L * m for m in range(1, lim) if m % L and (withL or m > 1)]
    def fs(n, mx, cur):
        if n == 1: yield tuple(cur); return
        for e in el:
            if e > mx or e > n: break
            if n % e == 0: yield from fs(n // e, e, cur + [e])
    for n in range(L, L * lim, L):
        f = list(fs(n, n, []))
        if len(f) >= 2: return n, f
P("== 1. L-world (place k = L*k, a (x) b = L*ab) ==")
for L in LAY:
    split = next(L * m for m in range(2, 99) if m % L and not isprime(m))
    d1, d0 = doubles(L, True), doubles(L, False)
    assert d1[0] == L * split  # first double factoring = unit x split point
    P(f"L={L}: 1(x)1={L}  split (first L*m, L!|m, m composite) = {split} = {L}*{split // L}"
      f"  first double counting {L}: {d1}  without {L}: {d0}")
P("asserted: first double = L x split point for L = 2,3,5,7 (also checked for L <= 31 except L = 4, where 64 = 4*4*4 = 8*8)")
P("only L = 2 splits at 9L; every odd L splits at 4L (4 is the first composite the layer cannot see)")

# ---- 2. the anchor law per layer: u(L*2^a + j) = u(L)*S_j*2^(a-l) - d(L)*T_j, lock exactly at 2^a > j ----
P("\n== 2. layer anchors: strand L*2^a + j (odd j), slope and constant, fold count to lock ==")
A = 48; base = {}
for L in (2,) + LAY[1:]:
    dL = 2 * U(L) - U(L + 1)
    for j in range(1, 256, 2):
        vals = [U(L * 2 ** a + j) for a in range(A + 1)]
        beta = vals[A] - 2 * vals[A - 1]; alpha = Fr(vals[A] + beta, 2 ** A)
        a0 = next(a for a in range(A + 1) if all(vals[b] == alpha * 2 ** b - beta for b in range(a, A + 1)))
        assert a0 <= j.bit_length() and (a0 == 0 or 2 ** (a0 - 1) <= j)  # locks once 2^a > j, not before (j>1)
        if L == 2: base[j] = (alpha, beta)
        else:
            assert alpha == base[j][0] * Fr(U(L), 2) and beta == base[j][1] * dL  # layer part x offset part
        if j <= 15:
            pr = [a for a in range(a0, 120) if isprime(L * 2 ** a + j)]
            P(f"L={L} (u={U(L)}, d={dL}) j={j:2d}: u = {alpha}*2^a - {beta}, lock a>={a0}, ratio limit {alpha / L},"
              f" prime rungs a<120: {pr[:14]}{' ...' if len(pr) > 14 else ''} ({len(pr)})")
P("asserted j<256, a<=48: layer L strand = (u(L)/2 x layer-2 slope, d(L) x layer-2 constant); lock fold = bit length of j at most")

# ---- 3. windows: which layer anchor is the prefix of p ----
P("\n== 3. prefix windows: p in [x*2^a, (x+1)*2^a) for x = 4,5,6,7 (x=4,5 inside layer 2's window 2|3; x=6,7 inside layer 3's 1|2) ==")
for N in (541, 10 ** 4, 10 ** 5):
    ps = [p for p in primerange(8, N + 1)]
    c = Counter(p >> (p.bit_length() - 3) for p in ps)
    bot = Counter(lad.ladder(p)[-1] for p in ps)
    assert c[4] + c[5] == bot[(2, 3)] and c[6] + c[7] == bot[(1, 2)]
    P(f"primes 8..{N}: prefix 4:{c[4]} 5:{c[5]} 6:{c[6]} 7:{c[7]}  ladder bottom 2|3:{bot[(2, 3)]} 1|2:{bot[(1, 2)]}")

# ---- 4. primes through each layer: tables (first 100) and up / down folds ----
ps100 = list(primerange(2, 542)); assert len(ps100) == 100
def coprime_seat(p, L):  # p's place among numbers coprime to every prime <= L
    sm = [q for q in (2, 3, 5, 7) if q <= L]; W = 1
    for q in sm: W *= q
    seats = [r for r in range(1, W + 1) if all(r % q for q in sm)]
    k, r = divmod(p, W)
    return (k * len(seats) + seats.index(r) + 1, r, W) if r in seats else None
def up_cross(p, L, J=40):  # fold j* after which u(L^j p) > 2 L^j p holds to J
    sgn = [U(L ** j * p) > 2 * L ** j * p for j in range(J + 1)]
    if not sgn[-1]: return None
    j = J
    while j > 0 and sgn[j - 1]: j -= 1
    return j
tab = []
for L in LAY:
    tab.append(f"\n==== layer {L} : first 100 primes; n = {L}p ====")
    tab.append("p | n | ladder of n | u(n) | 2n-u | u/n | depth | seat (index,res,W) | u(seat) | up u/n at L^2p, L^3p | cross 2n at fold")
    for p in ps100:
        n = L * p; s = coprime_seat(p, L)
        lads = " : ".join(f"{a}|{b}" for a, b in lad.ladder(n))
        upr = [str(Fr(U(L ** j * p), L ** j * p)) for j in (2, 3)]
        tab.append(f"{p} | {n} | {lads} | {U(n)} | {2 * n - U(n)} | {Fr(U(n), n)} | {depth(n)} | {s} | "
                   f"{U(s[0]) if s else '-'} | {upr} | {up_cross(p, L)}")
P("\n== 4. up direction: fold j* at which u(L^j p) rises above 2 L^j p for good (checked to j = 40) ==")
for L in LAY:
    for N in (541, 10 ** 4):
        cr = Counter(up_cross(p, L) for p in primerange(3, N + 1))
        P(f"L={L} primes 3..{N}: fold counts {sorted(cr.items(), key=lambda t: (t[0] is None, t[0] or 0))}")
assert all(up_cross(p, 2) in (None, 0) for p in primerange(3, 10 ** 4))  # evens copy: side never changes
P("L=2 never changes side (u(2^j p) = 2^j u(p) copies the odd core; asserted p < 10^4)")
P("up u/n along L^j for odd L (exact):", {L: [str(Fr(U(L ** j), L ** j)) for j in range(1, 7)] for L in (3, 5, 7)})

# ---- 5. down direction: p/L side = the L-adic ladder (p // L^i, +1), and seats ----
P("\n== 5. down direction and seats, primes to 10^5 ==")
PS = list(primerange(11, 10 ** 5 + 1))
for L in (3, 5, 7):
    W = {3: 6, 5: 30, 7: 210}[L]
    side = Counter(); dep = Counter(); usea = Counter()
    for p in PS:
        s, r, _ = coprime_seat(p, L)
        side[r < W // 2] += 1
        dep[(r < W // 2, min(depth(p), 3))] += 1
        usea[(r < W // 2, v2(U(s)) if U(s) else 0)] += 1
    P(f"W={W}: low-half seats {side[True]}, mirror high-half seats {side[False]}")
    P(f"   (low?, midpoint depth capped 3): {sorted(dep.items())}")
    P(f"   (low?, v2 of u(seat index)) first: {sorted(usea.items())[:10]}")
lad_bottom = {L: Counter() for L in LAY}
for p in PS:
    for L in LAY:
        k = p
        while k // L > 1: k //= L
        lad_bottom[L][(k, k + 1)] += 1
P("L-adic down ladder bottoms (k|k+1 with k = leading L-digit):", {L: dict(sorted(c.items())) for L, c in lad_bottom.items()})

# ---- 6. strands among the primes: ratio u/p records going up and down ----
P("\n== 6. strands among primes to 10^5: u/p record highs and record lows ==")
hi, lo, mx, mn = [], [], Fr(0), Fr(99)
for p in [2, 3, 5, 7] + PS:
    r = Fr(U(p), p)
    if r > mx: mx = r; hi.append((p, str(r)))
    if r < mn: mn = r; lo.append((p, str(r)))
P("record highs:", hi); P("record lows:", lo)

open(f"{HERE}/layered-method-table_v1.0_11-26-2026.txt", "w").write("\n".join(out + tab) + "\n")
print("\n".join(out))

# ---- 7. the top strand: running max of u/n over ALL n sits on the alternating words 1010...1011 = (2^q+1)/3 ----
P("\n== 7. top strand (record highs of u/n over all n < 2^20) ==")
rec, mx = [], Fr(0)
for n in range(1, 1 << 20):
    r = Fr(U(n), n)
    if r > mx: mx = r; rec.append(n)
jac = [(2 ** q + 1) // 3 for q in range(3, 21, 2)]
P("all-n records:", rec)
P("(2^q+1)/3, q odd:", jac, " in records:", [n in rec for n in jac])
P("u at (2^q+1)/3:", [(q, U((2 ** q + 1) // 3), str(Fr(U((2 ** q + 1) // 3), (2 ** q + 1) // 3))) for q in range(3, 40, 2)])
P("per-fold step of u on the strand (u(next) - 4u):", [U((2 ** (q + 2) + 1) // 3) - 4 * U((2 ** q + 1) // 3) for q in range(3, 40, 2)])
P("prime rungs q < 200:", [q for q in range(3, 200, 2) if isprime((2 ** q + 1) // 3)])
open(f"{HERE}/layered-method-table_v1.0_11-26-2026.txt", "w").write("\n".join(out + tab) + "\n")
print("\n".join(out[-6:]))
J = [U((2 ** q + 1) // 3) for q in range(5, 80, 2)]
assert all(J[i + 2] == 8 * J[i + 1] - 8 * J[i] for i in range(len(J) - 2))  # q = 5..79
P("asserted q=5..79: u(J_{q+4}) = 8 u(J_{q+2}) - 8 u(J_q), J_q = (2^q+1)/3 (roots 4 +- 2*sqrt2)")
open(f"{HERE}/layered-method-table_v1.0_11-26-2026.txt", "w").write("\n".join(out + tab) + "\n")

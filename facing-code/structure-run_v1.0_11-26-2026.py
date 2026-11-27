# Structure run (11-26-2026): midpoint chains, circles, 11 in the divisors, cube/square forms.
# Imports the build (does not change it). u(2k)=2u(k), u(2k+1)=2u(k)+u(k+1), u(1..3)=1,2,3.
# Writes structure-run-table_v1.0_11-26-2026.txt beside this file. Runs in ~1 min.
import importlib.util, sys
from fractions import Fraction as Fr
from collections import Counter
import numpy as np
from sympy import primerange, factorint

HERE = __file__.rsplit("/", 1)[0]
def load(name, f):
    sp = importlib.util.spec_from_file_location(name, f"{HERE}/{f}")
    m = importlib.util.module_from_spec(sp); sp.loader.exec_module(m); return m
fnl = load("fnl", "facing-number-line_v1.0_11-26-2026.py")
mine = load("mine", "facing-prime-mining_v1.0_11-26-2026.py")

N = 1 << 24
u = np.zeros(N + 2, dtype=np.int64); u[1:4] = [1, 2, 3]
lo = 4
while lo <= N + 1:  # evens first, odds read u(k+1) which may be this level's first even
    hi = min(2 * lo, N + 2)
    ev = np.arange(lo, hi, 2); u[ev] = 2 * u[ev // 2]
    od = np.arange(lo + 1, hi, 2); u[od] = 2 * u[od // 2] + u[od // 2 + 1]
    lo = hi
U = lambda n: int(u[n])
assert all(U(n) == mine.u(n) for n in range(1, 5000))
assert all(U(n) == fnl.B(n).count("1") for n in range(1, 1200))
def v2(x):
    c = 0
    while x % 2 == 0: x //= 2; c += 1
    return c
def oddpart(x): return x >> v2(x)

out = []
P = lambda *a: out.append(" ".join(str(x) for x in a))

# ---- 1. midpoint and wing chains ----
def mid_chain(n):  # p = k, k+1, k -> follow the middle block while it is filled (odd)
    ch = [n]
    while n > 3 and n % 2 == 1: n = n // 2 + 1; ch.append(n)
    return ch
def wing_chain(n):
    ch = [n]
    while n > 3: n //= 2; ch.append(n)
    return ch
for n in range(5, 1 << 16, 2):
    ch = mid_chain(n); d = len(ch) - 1
    if oddpart(n - 1) > 1:  # off the 2^a+1 strand the chain lands in an even block
        assert d == v2(n - 1) and ch[-1] == oddpart(n - 1) + 1 and ch[-1] % 2 == 0
    else:
        assert ch[-1] == 3
    assert wing_chain(n) == [n >> i for i in range(len(wing_chain(n)))]  # wing chain = binary prefixes
ps = list(primerange(3, 10 ** 6))
P("== 1. midpoint chain: depth d = v2(p-1) odd zooms, then lands on block oddpart(p-1)+1 (even) ==")
P("primes 3..10^6 by depth d:", sorted(Counter(v2(p - 1) for p in ps).items()))
sc = lambda m: m > 0 and oddpart(m) in (1, 3)
land = Counter((p % 4, sc(mid_chain(p)[-1])) for p in ps)
P("lands on a self-count point (2^a or 3*2^a), by p mod 4 (mod4, lands): ", sorted(land.items()))
# circle tie: the odd-midpoint depth d is the largest 2^d-gon of roots of 1 that p's line holds
for p in ps[:2500]:
    d = v2(p - 1)
    for k in range(1, 7):
        assert sum(1 for x in range(1, p) if pow(x, 2 ** k, p) == 1) == 2 ** min(k, d)
P("assert (p<22441): #{x: x^(2^k)=1 mod p} = 2^min(k,d), d = midpoint depth. d>=2 <=> p on a circle x^2+y^2.")

# ---- 2. the 2-adic reading of the unit count ----
n = np.arange(1, N, 2); t = u[n].copy(); vv = np.zeros_like(t)
while True:
    m = (t % 2 == 0)
    if not m.any(): break
    vv[m] += 1; t[m] //= 2
s0 = set(n[vv == 0].tolist()); s1 = set(n[vv == 1].tolist())
assert s0 == {1} | {2 ** a + 1 for a in range(1, 24)}
assert s1 == {3 * 2 ** a + 1 for a in range(1, 23)}
P("\n== 2. v2(u(n)) for odd n < 2^24 ==")
P("v2=0 exactly n=1, 2^a+1; v2=1 exactly 3*2^a+1 (a>=1)  [asserted]")
P("so the ratio-two strands are the odd n whose unit count is not a multiple of 4; 11 and 15 are the first two with v2=2 (u=20, 28)")
P("counts by v2 (odd n < 2^24):", sorted(Counter(vv.tolist()).items())[:12])
P("smallest odd n with v2=2:", n[vv == 2][:20].tolist())
# step defect delta(n)=2u(n)-u(n+1): delta(2k)=delta(k), delta(2k+1)=4u(k)
for k in range(2, 100000):
    assert 2 * U(2 * k) - U(2 * k + 1) == 2 * U(k) - U(k + 1)
    assert 2 * U(2 * k + 1) - U(2 * k + 2) == 4 * U(k)
# anchor law for every x: u(x*2^a + j) = 2^(a-l) u(x) S_j - delta(x) T_j (l = bitlength j)
A = {0: ((2, 0), (2, 1)), 1: ((2, 1), (0, 2))}
def apply(j, v):
    for b in bin(j)[2:]:
        M = A[int(b)]; v = (M[0][0] * v[0] + M[0][1] * v[1], M[1][0] * v[0] + M[1][1] * v[1])
    return v
for x in range(2, 300):
    dx = 2 * U(x) - U(x + 1)
    for j in range(1, 64):
        l = j.bit_length()
        for a in range(l, l + 4):
            if x * 2 ** a + j > N: continue
            S = apply(j, (1, 2))[0]; T = apply(j, (0, 1))[0]
            assert U(x * 2 ** a + j) == 2 ** (a - l) * U(x) * S - dx * T
P("asserted: delta(2k)=delta(k), delta(2k+1)=4u(k); u(x*2^a+j) = 2^(a-l)u(x)S_j - delta(x)T_j for every x>=2 (not only anchors)")

# ---- 3. 11 into the divisors ----
P("\n== 3. divisor-record numbers: u/n (u/n depends only on the odd part, u(2m)=2u(m)) ==")
PR = [2, 3, 5, 7, 11, 13, 17, 19, 23]; cands = []
def gen(i, e0, m, d):
    cands.append((m, d))
    if i == len(PR): return
    for e in range(1, e0 + 1):
        m *= PR[i]
        if m > N: break
        gen(i + 1, e, m, d * (e + 1))
gen(0, 30, 1, 1); cands.sort(); best = 0
for m, d in cands:
    if d > best:
        best = d; q = Fr(U(m), m)
        P(m, dict(factorint(m)), "u =", U(m), "u/n =", q, "odd part", oddpart(m))
P("\nu(cm)/u(m) over odd m < 2*10^5 (c odd): distinct values / count, most common")
for c in [3, 5, 7, 11, 13]:
    rs = Counter(Fr(U(c * m), U(m)) for m in range(1, 200001, 2))
    P(c, "u(c) =", U(c), "distinct", len(rs), "of 100000; top", [(str(k), v) for k, v in rs.most_common(3)])
P("u(11*2^j)/u(2^j) = 20 and u(33*2^j)/u(3*2^j) = 21 (self-count m); no fixed law off those.")
P("pairs odd 3<=c<=m<=2000 with u(cm)=u(c)u(m):",
  [(c, m) for c in range(3, 2001, 2) for m in range(c, 2001, 2) if U(c * m) == U(c) * U(m)][:12], "...")

# ---- 4. square / cube / power forms ----
P("\n== 4. powers ==")
for a in range(2, 25): assert U(2 ** a - 1) == (2 * a - 1) * 2 ** (a - 2)
P("u(2^a - 1) = (2a-1) * 2^(a-2), a>=2 [asserted to a=24]: the all-ones line holds the odd number 2a-1")
sq = [a for a in range(1, 4097) if U(a * a) == U(a) ** 2]
assert sq == [2 ** i for i in range(13)]
P("u(a^2) = u(a)^2 only at a = 2^i (a <= 4096); same for a^3 (checked a <= 255)")
assert [a for a in range(1, 256) if U(a ** 3) == U(a) ** 3] == [2 ** i for i in range(8)]
for b in [3, 5, 7, 11]:
    P(b, [(a, U(b ** a)) for a in range(1, 16) if b ** a <= N])
P("u(27) = 64 = 4^3, u(81) = 216 = 6^3 (u(243)=1184 not a cube): two examples only")

# ---- 5. how fast the count grows: u/n is unbounded ----
P("\n== 5. max u/n per binary level ==")
for a in range(2, 25):
    s = u[1 << (a - 1): 1 << a] / np.arange(1 << (a - 1), 1 << a); i = int(s.argmax()) + (1 << (a - 1))
    P(a, i, bin(i)[2:], U(i), Fr(U(i), i))
r = u[1:N + 1] / np.arange(1, N + 1); cm = np.maximum.accumulate(r)
P("u/n record setters:", (np.nonzero(np.r_[True, cm[1:] > cm[:-1]])[0] + 1)[:45].tolist())

open(f"{HERE}/structure-run-table_v1.0_11-26-2026.txt", "w").write("\n".join(out) + "\n")
print("\n".join(out[:12])); print("... all asserts passed")

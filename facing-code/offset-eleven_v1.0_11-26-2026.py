# Offset 11 (tUrUq, 11-26-2026): "the offset cannot be just 10, it needs to be 11. so 11s above it is 0m. and 1s is 10m."
# Mirror line n_m = O - n for offset families O = b^k + 1 (decimal 11, 101, 1001, 10001; binary 2^k+1; walls 3*2^k+1),
# compared with O = base and base - 1. Units u from the ladder shorthand (imported, not changed).
# Writes offset-eleven-table_v1.0_11-26-2026.txt beside this file. Runs in well under a minute.
import importlib.util
from fractions import Fraction as Fr
from collections import Counter

HERE = __file__.rsplit("/", 1)[0]
sp = importlib.util.spec_from_file_location("lad", f"{HERE}/ladder-shorthand_v1.0_11-26-2026.py")
lad = importlib.util.module_from_spec(sp); sp.loader.exec_module(lad)

N = 1_000_002 * 3
u = [0, 1, 2, 3] + [0] * (N - 3)
for n in range(4, N + 1):
    k = n >> 1
    u[n] = 2 * u[k] + (u[k + 1] if n & 1 else 0)
assert all(u[n] == lad.u(n) for n in range(5000))
pr = bytearray([1]) * (N + 1); pr[0] = pr[1] = 0
for i in range(2, int(N ** .5) + 1):
    if pr[i]: pr[i * i::i] = bytearray(len(pr[i * i::i]))

def v2(x):
    c = 0
    while x % 2 == 0: x //= 2; c += 1
    return c
core = lambda m: m >> v2(m)
ispow = lambda x: x > 0 and x & (x - 1) == 0
SC = lambda m: m > 0 and (ispow(m) or (m % 3 == 0 and ispow(m // 3)))   # self-count u(m) = m

def strand(c):  # odd core -> its place on the ratio-2 line
    if c in (1, 3): return "self"
    if ispow(c - 1): return "2^a+1"
    if (c - 1) % 3 == 0 and ispow((c - 1) // 3): return "3*2^a+1"
    if c in (11, 15): return "11/15"
    return "above"

def clean(m):  # class of an even mirror m > 0
    s = strand(core(m))
    if s != "above": return s
    if m % 4 == 2 and pr[m // 2]: return "2p"
    return "fray"

def window(m):  # 2-window [2*2^a,3*2^a) root 2|3, 3-window [3*2^a,4*2^a) root 1|2; sub 5, 7
    a = m.bit_length() - 2  # m in [2^(a+1), 2^(a+2))
    if a < 0: return "-"
    w = "2|3" if m < 3 << a else "1|2"
    a5 = m.bit_length() - 3
    sub = ""
    if a5 >= 0 and 5 << a5 <= m < 6 << a5: sub = " in5"
    if a5 >= 0 and 7 << a5 <= m < 8 << a5: sub = " in7"
    return w + sub

def even_class(m):
    if ispow(m): return "2^a"
    if SC(m): return "wall"
    return "2mod4" if m % 4 == 2 else "0mod4"

# self-check: below the line for an even m is exactly the clean core classes; u/m depends only on the core
for m in range(2, 200000, 2):
    assert (u[m] < 2 * m) == (strand(core(m)) != "above")
    assert Fr(u[m], m) == Fr(u[core(m)], core(m))
assert all(SC(m) == (u[m] == m) for m in range(1, 200000))

out = []; P = lambda *a: out.append(" ".join(str(x) for x in a))

def tally(pairs):
    """pairs: list of (p, m). Counts how primes map."""
    c = Counter()
    first_fray = []
    for p, m in pairs:
        if m == 0: c["->0"] += 1; continue
        if pr[m]: c["->prime"] += 1
        elif m == 1: c["->1"] += 1
        else: c["->composite"] += 1
        if m % 2: c["->odd"] += 1; continue
        c["->even"] += 1; c[even_class(m)] += 1
        k = clean(m); c[k] += 1
        if m % 4 == 2: c["2mod4 half prime" if pr[m // 2] else "2mod4 half comp"] += 1
        if k == "fray" and len(first_fray) < 6: first_fray.append(f"{p}->{m}")
        if u[m] < 2 * m: c["below"] += 1
    return c, first_fray

def summary(name, O, pairs):
    c, ff = tally(pairs)
    ev = c["->even"]
    cl = ev - c["fray"]
    P(f"{name:>12} O={O:<8} primes={len(pairs):<6} ->prime {c['->prime']:<3} ->comp {c['->composite']:<6} ->1 {c['->1']} ->0 {c['->0']} "
      f"->odd {c['->odd']:<5} ->even {ev:<6} [2mod4 {c['2mod4']} (half prime {c['2mod4 half prime']}) 0mod4 {c['0mod4']} 2^a {c['2^a']} wall {c['wall']}] "
      f"clean {cl}/{ev} = self {c['self']} 2^a+1 {c['2^a+1']} 3*2^a+1 {c['3*2^a+1']} 11/15 {c['11/15']} 2p {c['2p']} | below-line {c['below']} | first fray {' '.join(ff)}")
    return c

def block0(O):  # primes p in 1..O, pair p <-> O - p
    return [(p, O - p) for p in range(2, O + 1) if pr[p]]

# ---------------- 1. first block, per family ----------------
P("== 1. first block 0..O, pair n <-> O - n, primes only ==")
P("(clean even = odd core on the ratio-2 line [self 1|3, 2^a+1, 3*2^a+1, 11/15] or 2p; below-line = u(m) < 2m)")
FAM = {
    "dec b^k+1": [10 ** k + 1 for k in range(1, 6)],
    "dec b^k": [10 ** k for k in range(1, 6)],
    "dec b^k-1": [10 ** k - 1 for k in range(1, 6)],
    "bin 2^k+1": [2 ** k + 1 for k in range(2, 21)],
    "bin 2^k": [2 ** k for k in range(2, 21)],
    "bin 2^k-1": [2 ** k - 1 for k in range(2, 21)],
    "wall 3*2^k+1": [3 * 2 ** k + 1 for k in range(1, 19)],
    "wall 3*2^k": [3 * 2 ** k for k in range(1, 19)],
    "wall 3*2^k-1": [3 * 2 ** k - 1 for k in range(1, 19)],
}
RES = {}
for fam, Os in FAM.items():
    P(f"-- {fam}")
    for O in Os: RES[(fam, O)] = summary(fam, O, block0(O))

# exact structural fact: odd O, p + q = O both prime forces 2 in the pair; decimal 10^k+1-2 = 9..9 is never prime
for k in range(1, 6):
    O = 10 ** k + 1
    assert RES[("dec b^k+1", O)]["->prime"] == 0
P("asserted: decimal 11,101,1001,10001,100001 send NO prime to a prime (odd offset forces 2; 10^k - 1 = 9..9 composite)")

# ---------------- first block 11 and 101 in full, through the layers ----------------
def row(p, m):
    if m <= 0: return f"{p:>6} -> {m}"
    if m % 2: return f"{p:>6} -> {m:<6} odd {'P' if pr[m] else 'c'}  u={u[m]} 2m-u={2*m-u[m]} u/m={Fr(u[m], m)}"
    c = core(m)
    return (f"{p:>6} -> {m:<6} {even_class(m):<6} win {window(m):<8} u={u[m]:<7} 2m-u={2*m-u[m]:<7} u/m={str(Fr(u[m], m)):<9} "
            f"core {c} [{strand(c)}] {clean(m)}")
for O in (11, 101, 33, 65, 129, 49, 97):
    P(f"== layer rows, O = {O} ==")
    for p, m in block0(O): P(row(p, m))

# ---------------- 2. tiling: n <-> (2j+1)O - n inside block [jO,(j+1)O], and the shift reading n - O ----------------
P("== 2. tiling up to 1,000,000: (a) per-block mirror n <-> (2j+1)O - n; (b) one line continued past 0m, |n_m| = n - O ==")
TIL = [11, 101, 1001, 10001, 10, 100, 1000, 10000, 9, 99, 999, 9999, 17, 257, 65537, 16, 256, 65536, 15, 255, 65535, 13, 193, 12289]
LIM = 1_000_000
for O in TIL:
    pa = [(p, (2 * (p // O) + 1) * O - p) for p in range(2, LIM) if pr[p] and p % O]
    pb = [(p, p - O) for p in range(O + 1, LIM) if pr[p]]
    summary(f"blk {O}", O, pa)
    summary(f"shift {O}", O, pb)

# ---------------- clean rate by scale for the decimal family's per-block mirror ----------------
P("== clean evens per block, O = 11, per-block mirror, blocks j < 20 ==")
for j in range(20):
    lo, hi = j * 11, (j + 1) * 11
    ps = [(p, (2 * j + 1) * 11 - p) for p in range(max(lo, 2), hi) if pr[p] and p % 11]
    P(f"block [{lo},{hi}] " + "  ".join(f"{p}->{m}:{clean(m) if m % 2 == 0 else 'odd'}" for p, m in ps))

# ---------------- 4. the 11-line and 22-line ----------------
P("== 4. 11-line (place k at 11k) and 22-line ==")
from sympy import isprime
def doubles(L, lim=400):
    el = [L * m for m in range(1, lim) if m % L]
    def fs(n, mx, cur):
        if n == 1: yield tuple(cur); return
        for e in el:
            if e > mx or e > n: break
            if n % e == 0: yield from fs(n // e, e, cur + [e])
    for n in range(L, L * lim, L):
        f = list(fs(n, n, []))
        if len(f) >= 2: return n, f
for L in (11, 22):
    split = next(L * m for m in range(2, 99) if m % L and not isprime(m))
    d = doubles(L)
    assert d[0] == L * split
    P(f"L={L}: 1(x)1 = {L}; split (first L*m, L!|m, m composite) = {split}; first double factoring {d} = L x split")
P("u on 11*2^j:", [(11 << j, u[11 << j], str(Fr(u[11 << j], 11 << j))) for j in range(6)])
assert all(Fr(u[11 << j], 11 << j) == Fr(20, 11) for j in range(18))
P("u/n on 11-line places 11k, k=1..30:", " ".join(f"{k}:{Fr(u[11*k], 11*k)}" for k in range(1, 31)))
P("11-line places below the line (u < 2n), 11k < 10^6:", [11 * k for k in range(1, LIM // 11) if u[11 * k] < 22 * k][:40])
P("22-line places below the line, 22k < 10^6:", [22 * k for k in range(1, LIM // 22) if u[22 * k] < 44 * k][:40])
P("ladders: ", lad.short(11), " / ", lad.short(22), " / ", lad.short(5))

# ---------------- 5a. the strongest oddity: exact prime <-> composite swap ----------------
P("== 5a. offsets O where n <-> O - n swaps primes and composites exactly on [2, O-2] (0<->O, 1<->O-1 aside) ==")
sw = [O for O in range(5, 100001) if all(pr[n] != pr[O - n] for n in range(2, O - 1))]
assert sw == [11]
P("O in 5..100000:", sw, " (0 <-> 11: nothing <-> prime; 1 <-> 10: unit <-> composite; 2,3,5,7 <-> 9,8,6,4)")
eq = [x for x in range(2, 10001) if 2 * sum(pr[2:x + 1]) == x - 1]
assert eq == [9, 11, 13]
P("equal count of primes and composites on [2, x] only at x =", eq, "-> candidate O = x + 2 = 11, 13, 15; 13 and 15 fail at 2 <-> 11, 2 <-> 13")
P("binary analogue: O = 2^k+1 has prime -> prime exactly when 2^k - 1 is prime (pair 2 <-> 2^k - 1);",
  [2 ** k + 1 for k in range(2, 21) if pr[2 ** k - 1]])
P("first even that is not clean (not below the line, not 2p):", next(m for m in range(2, 999, 2) if clean(m) == "fray"))
P("== 5b. per-block tiling, first fray for odd O 3..99 (O, first fray prime, its mirror, odd primes clean before it), longest first ==")
ff = []
for O in range(3, 100, 2):
    c = 0
    for p in range(3, 20000):
        if not pr[p] or p % O == 0: continue
        m = (2 * (p // O) + 1) * O - p
        if clean(m) == "fray": ff.append((O, p, m, c)); break
        c += 1
ff.sort(key=lambda r: -r[1]); P(ff[:12]); P("O = 11:", [r for r in ff if r[0] == 11])

# ---------------- 5. oddity: u(n) + u(O - n) and the mirror deficit across the pair ----------------
P("== 5. pair sum u(n) + u(O-n) over the block, by offset (min, max, distinct count) ==")
for O in (9, 10, 11, 15, 16, 17, 99, 100, 101, 31, 32, 33, 63, 64, 65, 12, 13, 24, 25, 999, 1000, 1001):
    s = [u[n] + u[O - n] for n in range(0, O + 1)]
    sd = [(2 * n - u[n]) + (2 * (O - n) - u[O - n]) for n in range(0, O + 1)]
    P(f"O={O:<5} u(O)={u[O]:<5} sum u min {min(s)} max {max(s)} distinct {len(set(s))} | pair deficit min {min(sd)} max {max(sd)} ; n with sum == u(O): {sum(x == u[O] for x in s)}")

open(f"{HERE}/offset-eleven-table_v1.0_11-26-2026.txt", "w").write("\n".join(out) + "\n")
print("\n".join(out[:60]))

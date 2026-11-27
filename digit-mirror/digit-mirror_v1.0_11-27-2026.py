# Digit mirror and the offset-eleven crossings (11-27-2026), for tUrUq.
# His words: "it absolutely is, any time you see that mirror structure it is, but we need to nail that
# relationship down. all that weird digit stuff is what i want to explain."
# Uses his definitions unchanged: u (ladder build), strand/clean/"fray" from offset-eleven_v1.0_11-26-2026.py,
# block_mirror from standard-mirror-line_v1.0_11-26-2026.py (a multiple of O folds to the block below).
# Writes digit-mirror-table_v1.0_11-27-2026.txt beside this file. Runs in a few seconds.
N = 200_000
u = [0, 1, 2, 3] + [0] * (2 * N)
for n in range(4, 2 * N + 4):
    k = n >> 1
    u[n] = 2 * u[k] + (u[k + 1] if n & 1 else 0)
pr = bytearray([1]) * (2 * N + 4); pr[0] = pr[1] = 0
for i in range(2, int((2 * N + 4) ** .5) + 1):
    if pr[i]: pr[i * i::i] = bytearray(len(pr[i * i::i]))

ispow = lambda x: x > 0 and x & (x - 1) == 0
def core(m):
    while m % 2 == 0: m //= 2
    return m
def strand(c):  # copied from offset-eleven_v1.0_11-26-2026.py
    if c in (1, 3): return "self"
    if ispow(c - 1): return "2^a+1"
    if (c - 1) % 3 == 0 and ispow((c - 1) // 3): return "3*2^a+1"
    if c in (11, 15): return "11/15"
    return "above"
def clean(m):   # copied from offset-eleven_v1.0_11-26-2026.py
    s = strand(core(m))
    if s != "above": return s
    if m % 4 == 2 and pr[m // 2]: return "2p"
    return "fray"
def block_mirror(n, O=11):  # copied from standard-mirror-line_v1.0_11-26-2026.py, O general
    j = n // O if n % O else n // O - 1
    return (2 * j + 1) * O - n
def digits(n, b):
    d = []
    while n: d.append(n % b); n //= b
    return d[::-1] or [0]
def rev(n, b=10, width=None):
    d = digits(n, b)
    if width: d = [0] * (width - len(d)) + d
    r = 0
    for x in reversed(d): r = r * b + x
    return r

out = []; P = lambda *a: out.append(" ".join(str(x) for x in a))

# checks against his table rows (offset-eleven-table lines 327-346, blocks [0,11] .. [209,220])
his = {2: 9, 3: 8, 5: 6, 7: 4, 67: 76, 73: 70, 97: 90, 101: 108, 107: 102, 127: 126, 197: 188}
assert all(block_mirror(p) == m for p, m in his.items())
assert [clean(m) for m in (8, 6, 4, 20, 16, 14, 46, 60, 76, 70, 90, 108)] == \
    ["self", "self", "self", "2^a+1", "self", "3*2^a+1", "2p", "11/15", "fray", "fray", "fray", "fray"]
assert u[2 * 3] < 2 * 6 and all((u[m] < 2 * m) == (strand(core(m)) != "above") for m in range(2, 20000, 2))

# ---- 1. crossings on the per-block 11 mirror, odd n, both kinds ----
# kind P: a prime faces a frayed even (his "fray"; his ruling: 67 -> 76 IS a crossing).
# kind C: any other odd composite faces a doubled odd prime 2q (the paper's "odd composites face the evens that are not doubled primes", broken).
P("== 1. crossings on the per-block mirror n <-> (2j+1)*11 - n (multiples of 11 fold to the block below) ==")
P("kind P = prime n facing a fray even; kind C = other odd composite facing 2q")
cross = []
for n in range(3, N, 2):
    m = block_mirror(n)
    if m == 0: continue   # 11 <-> 0 (nothing), the mirror's own seat
    if pr[n] and clean(m) == "fray": cross.append((n, m, "P"))
    elif not pr[n] and m % 4 == 2 and pr[m // 2]: cross.append((n, m, "C"))
for lim in (100, 300):
    P(f"n < {lim}:", " ".join(f"{n}<->{m}{k}" for n, m, k in cross if n < lim))
P("first kind P:", [c[:2] for c in cross if c[2] == "P"][:10]); P("first kind C:", [c[:2] for c in cross if c[2] == "C"][:10])
assert cross[:6] == [(33, 22, "C"), (39, 38, "C"), (63, 58, "C"), (67, 76, "P"), (69, 74, "C"), (73, 70, "P")]
cP = sum(k == "P" for _, _, k in cross); cC = len(cross) - cP
P(f"counts odd n < {N}: kind P {cP}, kind C {cC}")

# ---- 2. the exact law: per-block mirror = digit reversal + whole elevens ----
P("== 2. two-digit law, base 10: M(n) = rev(n) + 11*((2j+1) - (a+b)), so M(n) = rev(n) exactly when a+b = 2j+1 ==")
same = []
for n in range(1, 100):
    a, b = divmod(n, 10); r = 10 * b + a
    j = n // 11 if n % 11 else n // 11 - 1
    assert n + r == 11 * (a + b) and n - r == 9 * (a - b)
    assert block_mirror(n) == r + 11 * ((2 * j + 1) - (a + b))
    assert (block_mirror(n) - r) % 11 == 0 and (block_mirror(n) + n) % 11 == 0
    if block_mirror(n) == r: same.append(n)
P("two-digit n (01..99) with M(n) = rev(n):", same)
assert same == [1, 10, 12, 21, 23, 32, 34, 43, 45, 54, 56, 65, 67, 76, 78, 87, 89, 98]
assert all(abs(n // 10 - n % 10) == 1 for n in same) and all(n in same for n in range(1, 100) if abs(n // 10 - n % 10) == 1)
P("= exactly the neighbour-digit pairs |a-b| = 1: nine pairs a(a+1) <-> (a+1)a, each sum 11(2a+1), each difference 9")
P("classes on the nine pairs:", " ".join(f"{x}<->{block_mirror(x)}:{'P' if pr[x] else 'c'}/{clean(block_mirror(x)) if block_mirror(x) % 2 == 0 else 'odd'}"
                                     for x in same if x % 2 == 1))

# ---- 3. every base B, two digits, mirror O = B + 1 ("the one of the base", |^1 = B + 1) ----
P("== 3. any base B, two digits (a,c), O = B+1: M(n) = rev(n) iff |a - c| = 1 (B - 1 pairs) ==")
for B in range(2, 41):
    hits = [n for n in range(1, B * B) if block_mirror(n, B + 1) == rev(n, B, 2)]
    want = [n for n in range(1, B * B) if abs(n // B - n % B) == 1]
    assert hits == want and len(hits) == 2 * (B - 1)
P("checked B = 2..40; base 2: 1 <-> 2 (01 <-> 10) on O = 3; base 100 is the scale-up 101: 1 <-> 100, 102 <-> 201, ..., 809 <-> 908 on O = 101")
hits101 = [n for n in range(1, 1000) if block_mirror(n, 101) == rev(n, 10, 3)]
P("three-digit decimal n with M_101(n) = rev(n):", hits101)
assert hits101 == sorted(x for a in range(9) for x in (100 * a + a + 1, 100 * (a + 1) + a))

# ---- 4. longer numbers on the 11 mirror (PalindromeInvolutionModulus: rev(n) = 10^(len-1) n mod 99) ----
P("== 4. longer numbers: rev(n) = -n mod 11 for even length, rev(n) = +n mod 11 for odd length; rev(n) = n mod 9 always ==")
for n in range(1, N):
    L = len(str(n)); r = int(str(n)[::-1])
    assert (r - n) % 9 == 0
    assert (r + n) % 11 == 0 if L % 2 == 0 else (r - n) % 11 == 0
hits11 = [n for n in range(100, 100000) if block_mirror(n) == int(str(n)[::-1])]
P(f"n in 100..99999 with M_11(n) = rev(n): {len(hits11)}; first 20:", hits11[:20])
P("three-digit ones all have n divisible by 11 (odd length: M = -n, rev = +n mod 11, they agree only when 11 | n):",
  all(n % 11 == 0 for n in hits11 if n < 1000))

# ---- 5. which crossings are digit mirrors ----
P("== 5. crossings that are digit mirrors (M(n) = rev(n)) below", N, "==")
dm = [(n, m, k) for n, m, k in cross if m == int(str(n)[::-1])]
P(dm[:40], "count", len(dm))
open(__file__.rsplit("/", 1)[0] + "/digit-mirror-table_v1.0_11-27-2026.txt", "w").write("\n".join(out) + "\n")
print("\n".join(out))

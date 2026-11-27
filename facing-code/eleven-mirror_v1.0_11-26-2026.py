# 11 and the missing mirror (tUrUq, 11-26-2026). Imports the build, does not change it.
# 1) decodes his 11 string, 2) a mark rule that never loses a unit, 3) the 11 <-> 15 pairing (anchor + 3),
# 4) decimal and base-3 mirrors in the build. Writes eleven-mirror-table_v1.0_11-26-2026.txt beside this file.
import importlib.util, sys
from fractions import Fraction as Fr
from sympy import isprime
HERE = __file__.rsplit("/", 1)[0]
sp = importlib.util.spec_from_file_location("fnl", f"{HERE}/facing-number-line_v1.0_11-26-2026.py")
fnl = importlib.util.module_from_spec(sp); sp.loader.exec_module(fnl)
sp = importlib.util.spec_from_file_location("fpm", f"{HERE}/facing-prime-mining_v1.0_11-26-2026.py")
fpm = importlib.util.module_from_spec(sp); sp.loader.exec_module(fpm)
u, B = fpm.u, fnl.B

# ---- 1. his string, read several ways --------------------------------------------------------
HIS = "10|,1|1,|01,,1|1,|0||0"

def word(tok, interior):
    """One token -> seats. Trailing | = fold on the last seat (shared), leading | = fold on the first seat.
    interior: what an inside mark 'a|b' is: 'unit' (mark sits on a 1 seat), 'zero' (mark sits in a 0 seat),
    'gap' (mark is between seats, takes none), 'eat' (every | takes a seat and holds nothing)."""
    if interior == "eat":
        return tok.replace("|", "0")
    if tok.endswith("|") and "|" not in tok[:-1]:
        h = tok[:-1]; return h + h[-2::-1]
    if tok.startswith("|") and "|" not in tok[1:]:
        h = tok[1:]; return h[:0:-1] + h
    if tok.count("|") == 1:
        a, b = tok.split("|")
        return a + {"unit": "1", "zero": "0", "gap": ""}[interior] + b
    return tok.replace("|", "")          # '|0||0': marks only, the zeros keep their seats ("place in the zero")

def decode(s, interior):
    return ",,".join(",".join(word(t, interior) for t in g.split(",")) for g in s.split(",,"))

HALF11 = fnl.short(11).replace(",", "").rstrip("|")      # build half form of 11, to the centre seat

# ---- 2. mark rule: a mark never takes a 1's seat ---------------------------------------------
# Each 3-seat word faces the centre of its own 9-seat block. Left word: xy| ; right word: |yx (| touches the
# shared seat). Centre word faces both ways: centre seat 0 -> the mark sits IN the zero (x|x);
# centre seat 1 -> the unit stays and is bracketed (x|1|x). Squeaker = a centre word whose seat is a unit.
def mark(n):
    s = B(n); out = []; squeak = 0
    for i in range(0, len(s), 3):
        w, pos = s[i:i + 3], (i // 3) % 3 if len(s) > 3 else 1
        if pos == 0: m = w[:2] + "|"
        elif pos == 2: m = "|" + w[1:]
        elif w[1] == "0": m = w[0] + "|" + w[2]
        else: m = w[0] + "|1|" + w[2]; squeak += 1
        if i:
            j = 0
            while i % 3 ** (j + 1) == 0: j += 1
            out.append("," * j)
        out.append(m)
    return "".join(out), squeak

def unmark(t):
    seats = []
    for m in [x for x in t.split(",") if x]:
        if m.endswith("|") and m.count("|") == 1: seats.append(m[:2] + m[0])
        elif m.startswith("|") and m.count("|") == 1: seats.append(m[2] + m[1:])
        elif m.count("|") == 2: seats.append(m[0] + "1" + m[-1])
        else: seats.append(m[0] + "0" + m[2])
    return "".join(seats)

# ---- 3. anchor + j: u(A + j) = s_j*A - t_j, deficit d = 2n - u ------------------------------
def slope(j, A):
    s = Fr(u(2 * A + j) - u(A + j), A); return s, s * A - u(A + j)

def b3(n):
    s = ""
    while n: s = str(n % 3) + s; n //= 3
    return s or "0"

if __name__ == "__main__":
    sys.setrecursionlimit(10000)
    out = []; say = lambda *a: (print(*a), out.append(" ".join(str(x) for x in a)))
    # self-checks
    assert decode(HIS, "unit").replace(",", "") == HALF11 == "10111110111100"
    for n in range(1, 400):
        t, _ = mark(n); assert unmark(t) == B(n), n
    for a in range(3, 40): assert 2 * (2 ** a + 3) - u(2 ** a + 3) == 10 - 2 ** a
    for a in range(2, 40): assert 2 * (3 * 2 ** a + 3) - u(3 * 2 ** a + 3) == 14 - 3 * 2 ** a
    N = 1 << 20
    assert [n for n in range(1, N) if u(n) == 2 * (n - 1)] == [2, 11, 15]
    assert [n for n in range(1, N, 2) if 0 < 2 * n - u(n) <= 2] == [1, 11, 15]

    say("== 1. his 11 string:", HIS, " build half of 11:", fnl.short(11))
    for r in ("unit", "zero", "gap", "eat"):
        d = decode(HIS, r); h = d.replace(",", ""); full = h + h[-2::-1]
        say(f"  inside-mark={r:5s} -> {d:28s} seats {len(full):2d} units {full.count('1'):2d}",
            "(= 11, no loss)" if h == HALF11 else f"(build 27 seats, 20 units; lost {20 - full.count('1')})")
    say("\n== 2. mark rule (mark never takes a 1's seat); squeakers = centre words holding a unit")
    for n in (1, 2, 3, 5, 6, 10, 11, 15, 22, 33):
        t, q = mark(n); say(f"  {n:3d} squeak {q:2d}  {t if len(t) < 200 else t[:200] + '...'}")
    say("\n== 3. anchor + j (P = 2^a, W = 3*2^a): u(A+j) = s*A - t once locked; deficit d = (2-s)A + 2j + t")
    for j in range(1, 34, 2):
        sP, tP = slope(j, 1 << 24); sW, tW = slope(j, 3 << 24)
        say(f"  j={j:2d} s={str(sP):6s} tP={str(tP):10s} tW={str(tW):10s} sW==sP {sW == sP}")
    say("  j=3: d(P+3) = 10 - P (P>=8), d(W+3) = 14 - W (W>=12): positive only at 11 = 8+3 and 15 = 12+3, both d = 2")
    say("  u(n) = 2(n-1) for n < 2^20 only at 2, 11, 15;  u(11)=20=2*10, u(15)=28=2*14")
    say("  binary 11 = 1011 (= 8+3), 15 = 1111 (= 12+3); base 3: 11 = 102, 15 = 120")
    say("\n== 4. decimal and base-3 mirrors: n u d=2n-u u/n path base3")
    pal = lambda s: s == s[::-1]
    for n in [n for n in range(10, 400) if pal(str(n))] + [1001, 1111, 2112, 4224, 8448]:
        say(f"  dec {n:5d} {u(n):6d} {2*n-u(n):7d} {str(Fr(u(n), n)):>10s} {fnl.centre_path(n):8s} {b3(n)}")
    say("  decimal mirrors below the line (u<2n) under 2^20:", [n for n in range(1, N) if u(n) < 2 * n and n > 9 and pal(str(n))])
    say("  base-3 mirrors below the line under 2^20:", [(n, b3(n), 2*n-u(n)) for n in range(1, N) if u(n) < 2 * n and pal(b3(n))])
    open(f"{HERE}/eleven-mirror-table_v1.0_11-26-2026.txt", "w").write("\n".join(out) + "\n")

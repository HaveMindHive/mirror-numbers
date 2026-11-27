# Prime mining on the facing number line (11-26-2026). Imports the build, does not change it.
# u(n) = units (1s) in B(n). Zoom keeps units, so u(2k) = 2u(k), u(2k+1) = 2u(k) + u(k+1), words u(1..3) = 1,2,3.
import importlib.util, sys
from functools import lru_cache
from fractions import Fraction as Fr
from sympy import isprime, factorint
from collections import Counter
HERE = __file__.rsplit("/", 1)[0]
sp = importlib.util.spec_from_file_location("fnl", f"{HERE}/facing-number-line_v1.0_11-26-2026.py")
fnl = importlib.util.module_from_spec(sp); sp.loader.exec_module(fnl)

@lru_cache(None)
def u(n):
    if n <= 3: return n
    k = n // 2
    return 2 * u(k) + (u(k + 1) if n % 2 else 0)

def delta(n):  # step defect: 2 units(n) - units(n+1); doubling keeps it
    return 2 * u(n) - u(n + 1)

def oddpart(n):
    while n % 2 == 0: n //= 2
    return n

def centre_land(n):  # odd n > 3: centre goes O^a then sits in the hinge of block oddpart(n-1)+1, a = v2(n-1)
    a, m = 0, n - 1
    while m % 2 == 0: m //= 2; a += 1
    return a, m + 1

def tag(n): return "P" if isprime(n) else "c"

if __name__ == "__main__":
    sys.setrecursionlimit(10000)
    out = []; say = lambda *a: (print(*a), out.append(" ".join(str(x) for x in a)))
    # self-checks against the build
    for n in range(1, 1500): assert u(n) == fnl.B(n).count("1")
    for n in range(5, 1500, 2):
        a, L = centre_land(n); p = fnl.centre_path(n)
        if L > 3: assert p == "O" * a + "E", n          # lands in the even hinge of block L
    N = 1 << 17
    assert [n for n in range(1, N) if u(n) % n == 0] == sorted([2**m for m in range(17)] + [3 * 2**m for m in range(16)])
    assert all(u(n) >= n for n in range(1, N))
    for n in range(2, 5000): assert delta(2 * n) == delta(n)
    for k in range(1, 120):
        W, P = 3 * 2**k, 2**k
        assert u(W + 1) == 2 * (W - 1) and u(W) == W and u(W - 1) == 2**(k - 1) * (3 * k + 4)
        assert u(P + 1) == 2 * P - 1 and u(P) == P and (k < 2 or u(P - 1) == 2**(k - 2) * (2 * k - 1))
    for c in range(2, 200):   # every line c*2^a+1 maps to the line u(c)*2^(a+1) - delta(c)
        for a in range(0, 30): assert u(c * 2**a + 1) == u(c) * 2**(a + 1) - delta(c)
    say("checks ok: u(n)>=n, n|u(n) only at 2^m and 3*2^m (n<131072); wall/power forms to k<120; line map c<200, a<30")

    say("\n== Mirror across the power 2^m: n = 2^m+1 (lit centre) carries u = 2^(m+1)-1 ==")
    for m in range(1, 130):
        n, U = 2**m + 1, 2**(m + 1) - 1
        if isprime(n) or isprime(U): say(f"m={m:3d} n=2^{m}+1 {tag(n)}  units=2^{m+1}-1 {tag(U)}")
    say("\n== Mirror across the wall W=3*2^k: u(W+1) = 2(W-1); u(W-1) = 2^(k-1)(3k+4) ==")
    for k in range(1, 200):
        W = 3 * 2**k
        if isprime(W - 1) or isprime(W + 1): say(f"k={k:3d} W-1 {tag(W-1)}  W+1 {tag(W+1)}  units(W+1)=2*(W-1)")
    say("\n== Lines c*2^a+1 -> units line u(c)*2^(a+1) - delta(c); self-mirror when units odd part = c*2^b - 1 ==")
    for c in range(1, 40, 2):
        if c == 1: say("c=1: u=2^(a+1)-1 (from 2^a+1, a>=1)"); continue
        say(f"c={c:2d}: u(c)={u(c)} delta(c)={delta(c)}  limit ratio 2u(c)/c = {Fr(2*u(c), c)}")

    say("\n== Ratio u/n inside each band [3*2^k+1, 3*2^(k+1)]: primes vs other odds (exact means) ==")
    for k in range(1, 15):
        W = 3 * 2**k
        rp = [Fr(u(n), n) for n in range(W + 1, 2 * W + 1, 2) if isprime(n)]
        ro = [Fr(u(n), n) for n in range(W + 1, 2 * W + 1, 2) if not isprime(n)]
        mp, mo = sum(rp) / len(rp), sum(ro) / len(ro)
        say(f"k={k:2d} band {W+1}..{2*W} primes {len(rp):5d} mean {float(mp):.6f}  other odds {len(ro):5d} mean {float(mo):.6f}  (float shown for reading only)")

    say("\n== Centre landing of odd n: depth a = v2(n-1), block L = oddpart(n-1)+1 ==")
    cp = Counter(centre_land(p)[0] for p in range(5, 100000) if isprime(p))
    co = Counter(centre_land(n)[0] for n in range(5, 100000, 2) if not isprime(n))
    say("primes depth:", sorted(cp.items())[:12]); say("other odds depth:", sorted(co.items())[:12])

    say("\n== Ratio-2 line: odd n with u(n) < 2n (n < 2^20); u(n) = 2n never ==")
    below = [n for n in range(1, 1 << 20, 2) if u(n) < 2 * n]
    lines = {2**a + 1 for a in range(1, 21)} | {3 * 2**a + 1 for a in range(1, 20)}
    assert [n for n in below if n not in lines] == [1, 11, 15] and not any(u(n) == 2 * n for n in range(1, 1 << 20))
    say("off the two strands:", [(n, 2 * n - u(n)) for n in below if n not in lines])
    say("strands: 2n-u = 3 on 2^a+1, 4 on 3*2^a+1:", [(n, tag(n), 2 * n - u(n)) for n in below if n in lines][:24])
    say("\n== Above an anchor A (2^a or 3*2^a): u(A+j) = s_j*A - t_j, same s_j, t_j(wall) = 2 t_j(power); a = 40 ==")
    for j in range(1, 34, 2):
        a = 40
        sp_ = Fr(u(2**(a + 1) + j) - u(2**a + j), 2**a); tp = sp_ * 2**a - u(2**a + j)
        sw = Fr(u(3 * 2**(a + 1) + j) - u(3 * 2**a + j), 3 * 2**a); tw = sw * 3 * 2**a - u(3 * 2**a + j)
        assert sp_ == sw and tw == 2 * tp
        first = next(b for b in range(1, 40) if all(u(2**c + j) == sp_ * 2**c - tp and u(3 * 2**c + j) == sw * 3 * 2**c - tw for c in range(b, 41)))
        say(f"j={j:2d} slope {sp_}  t_power {tp}  t_wall {tw}  holds from a={first}")
    for j in range(2, 12):
        for a in range(j, 40): assert u((2**j + 1) * 2**a + 1) == 2**(j + 1) * ((2**(j + 1) - 1) * 2**(a - j) - 1)
    open(f"{HERE}/facing-prime-mining-table_v1.0_11-26-2026.txt", "w").write("\n".join(out) + "\n")

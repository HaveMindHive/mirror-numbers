# Exact data for the PySR finds (11-27-2026). Integers and exact fractions only.
import importlib.util, os, json, math
from fractions import Fraction
from sympy import primerange
CODE = "/Users/paymore/HaveMindHive/PRIMES_Fold_v1.0_11-20-2026/unit-counting-paper_v1.0_11-24-2026/unit-counting-code_v5.3_11-27-2026/facing-code"
def load(name, f):
    sp = importlib.util.spec_from_file_location(name, os.path.join(CODE, f)); m = importlib.util.module_from_spec(sp); sp.loader.exec_module(m); return m
lad = load("lad", "ladder-shorthand_v1.0_11-26-2026.py")
ep = load("ep", "even-primes_v1.0_11-26-2026.py")
tm = load("tm", "two-mirrors_v1.0_11-26-2026.py")

def first_seat(c):  # first number past c off the walls 2 and 3 (c off 2 and 3)
    return c + 2 if c % 6 == 5 else c + 4

def above_share(r):
    """Row 109, one full turn of the 6r-run: off classes c mod 6r (c coprime to 6r) whose first seat is an r-seat."""
    off = [c for c in range(6 * r) if math.gcd(c, 6 * r) == 1]
    hit = [c for c in off if first_seat(c) % r == 0]
    return len(hit), len(off)

def stacked_share(blocks):
    """Row 109 stacked: over a full turn of 6*prod(blocks), share of off classes whose first seat is a seat of the last
    block and of no smaller block, among the classes whose first seat is on no smaller block."""
    M = 6 * math.prod(blocks); r, small = blocks[-1], blocks[:-1]
    left = hit = 0
    for c in range(M):
        if math.gcd(c, M) != 1: continue
        y = first_seat(c)
        if any(y % s == 0 for s in small): continue
        left += 1; hit += (y % r == 0)
    return Fraction(hit, left), hit, left

def v2(n):
    d = 0
    while n % 2 == 0: n //= 2; d += 1
    return d

if __name__ == "__main__":
    out = {}
    out["share"] = {r: above_share(r) for r in primerange(5, 1100)}
    out["stack"] = {str(b): [str(f), h, l] for b in ([5], [5, 7], [5, 7, 11], [5, 7, 11, 13]) for f, h, l in [stacked_share(b)]}
    out["ladder"] = {n: [len(lad.ladder(n)), lad.ladder(n)[-1][0]] for n in range(2, 20001)}
    cnt, run = {}, 0
    for X in range(2, 6001):
        run += ep.even_world_prime(X); cnt[X] = run
    out["evencount"] = cnt
    dp = {}
    for p in range(3, 200001, 2):
        dl, dr = v2(2 * p - 2), v2(2 * p + 2)
        dp[p] = [dl, dr, v2(p - 1 if p % 4 == 1 else p + 1)]
    out["depth"] = dp
    out["alenT"] = {k: len(tm.notation_a(tm.T(3 ** k))[0]) for k in range(1, 9)}
    json.dump(out, open("pysr-finds-data_v1.0_11-27-2026.json", "w"))
    print("share counts (hit, off) distinct:", sorted(set((h, l - 2 * (r - 1)) for r, (h, l) in out["share"].items())))
    print("stack:", out["stack"])
    print("alenT:", out["alenT"])
    bad = [p for p, (dl, dr, h) in dp.items() if not (max(dl, dr) == 1 + h and min(dl, dr) == 2 and ((dl > dr) == (p % 4 == 1)))]
    print("depth law fails (odd p, prime or not, 3..200001):", bad[:10], len(bad))

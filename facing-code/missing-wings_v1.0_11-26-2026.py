# Missing wings (tUrUq, 11-26-2026). A prime p = |w = w,1,w. A wing w goes missing when it is copies of an odd
# block m plus half of m: w = a*m + (m-1)/2 (a >= 1, m odd >= 3); strand of block m starts at m + (m-1)/2, steps by m.
# Open wings (on no strand) are the prime seats. Built by laying strands down; isprime only to check afterwards.
import math
from sympy import isprime

def lay_strands(W):
    hits = bytearray(W + 1)  # how many strands land on each wing (capped at 255)
    m = 3
    while m + (m - 1) // 2 <= W:
        for w in range(m + (m - 1) // 2, W + 1, m):
            if hits[w] < 255: hits[w] += 1
        m += 2
    return hits

def two_squares(p):
    a = 1
    while 2 * a * a <= p:
        b = math.isqrt(p - a * a)
        if b * b == p - a * a: return a, b
        a += 1

if __name__ == "__main__":
    W = 10 ** 6
    hits = lay_strands(W)
    opened = [w for w in range(1, W + 1) if hits[w] == 0]
    assert all(isprime(2 * w + 1) for w in opened[:5000]) and not any(isprime(2 * w + 1) for w in range(1, 20000) if hits[w])
    print("first open wings:", opened[:40])
    for top in (10 ** 2, 10 ** 3, 10 ** 4, 10 ** 5, 10 ** 6):
        o = sum(1 for w in opened if w <= top)
        ev = sum(1 for w in opened if w <= top and w % 2 == 0)
        print(f"wings to {top:>7}: open {o:6d} ({o/top:.4f}), missing {top-o:7d}; open even {ev}, open odd {o-ev}")
    run, best, at = 0, 0, 0
    for w in range(1, W + 1):
        run = run + 1 if hits[w] else 0
        if run > best: best, at = run, w
    print(f"longest run of missing wings to {W}: {best} (ends at wing {at}, prime gap {2*(best+1)})")
    twins = sum(1 for w in opened if w + 1 <= W and hits[w + 1] == 0)
    print("open wings side by side (twin seats):", twins)
    # how many strands land on a missing wing = how many equal-copy faces its seat has
    from collections import Counter
    c = Counter(min(hits[w], 9) for w in range(1, 20001) if hits[w])
    print("missing wings to 20000 by number of strands landing:", sorted(c.items()))
    print("imaginary side, even open wings (p = a^2 + b^2):", [(w, 2*w+1, two_squares(2*w+1)) for w in opened if w % 2 == 0][:12])
    assert all(two_squares(2 * w + 1) for w in opened if w % 2 == 0 and w < 50000)
    assert not any(two_squares(2 * w + 1) for w in opened if w % 2 == 1 and w < 50000)

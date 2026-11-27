# Short-range construction (tUrUq, 11-26-2026): from a prime seat |w, lay the strands only across a short window
# of wings ahead (blocks m with m*m <= 2*top+1; strand of m: start m + (m-1)//2, step m), and read the first open seat.
# isprime / nextprime only to score.
import math
from sympy import nextprime, primerange

def next_seat(w, span=200):
    lo, hi = w + 1, w + span
    hit = bytearray(span)
    m = 3
    while m * m <= 2 * hi + 1:
        s = m + (m - 1) // 2
        first = s if s >= lo else lo + ((s - lo) % m)
        for x in range(first, hi + 1, m):
            hit[x - lo] = 1
        m += 2
    for i, h in enumerate(hit):
        if not h: return lo + i
    return next_seat(w, 2 * span)

if __name__ == "__main__":
    ok = tot = 0
    for p in list(primerange(3, 10 ** 4)) + list(primerange(10 ** 9, 10 ** 9 + 20000)):
        w = (p - 1) // 2
        q = 2 * next_seat(w) + 1
        ok += q == nextprime(p); tot += 1
    print(f"named the next prime exactly for {ok} of {tot} primes (3..1e4 and 1e9..1e9+2e4)")
    assert ok == tot

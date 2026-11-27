# Left-out evens (tUrUq, 11-26-2026). Even line: place k at 2k; 2 is the 1 (place 1); even primes = prime places
# (4 = place 2 is the first, then 6, 10, 14, 22 ...). Left out: 8, 12, 16, 18, 20, 24, 28, 30, 32, 36, 40 ...
# Readings: halvings down to the odd core (depth), and the even neighbours on each side of an even prime.
from sympy import isprime

def depth(n):
    d = 0
    while n % 2 == 0:
        n //= 2; d += 1
    return d, n

def even_copy_faces(n):
    """Ways n folds into equal copies of an even block other than 2 (q copies of 2d, d >= 2)."""
    return [(n // b, b) for b in range(4, n, 2) if n % b == 0]

if __name__ == "__main__":
    ep = [n for n in range(4, 202, 2) if isprime(n // 2)]
    lo = [n for n in range(4, 202, 2) if not isprime(n // 2)]
    assert ep[:5] == [4, 6, 10, 14, 22] and lo[:11] == [8, 12, 16, 18, 20, 24, 28, 30, 32, 36, 40]
    print("even primes:", ep)
    print("left out:   ", lo)
    print("\nleft-out evens by their equal even-copy faces:")
    for n in lo[:16]:
        print(f"  {n:3d} depth {depth(n)[0]}  core {depth(n)[1]:3d}  faces {even_copy_faces(n)}")
    print("\neach even prime between its two left-out neighbours (depth = halvings to the odd core):")
    for n in ep[1:16]:
        dl, dr = depth(n - 2)[0], depth(n + 2)[0]
        p = n // 2
        print(f"  {n-2:3d} (d{dl}) | {n:3d} | {n+2:3d} (d{dr})   p = {p} = {p % 4} mod 4   deep side {'left' if dl > dr else 'right'}")
    # check: the deep side is left exactly when p = 1 mod 4, and its depth is 1 + v2(p -+ 1)
    for p in range(3, 200000, 2):
        if not isprime(p): continue
        dl, dr = depth(2 * p - 2)[0], depth(2 * p + 2)[0]
        assert (dl > dr) == (p % 4 == 1) and min(dl, dr) == 2
        assert max(dl, dr) == 1 + depth(p - 1 if p % 4 == 1 else p + 1)[0]
    print("\nchecked for odd primes p < 200000: deep side left exactly when p = 1 mod 4; shallow side depth 2; deep side depth = 1 + halvings of p-1 (or p+1)")

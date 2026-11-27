# Spine shorthand (tUrUq, 11-26-2026): the wings from the outside in, then the centre.
# Odd n: wing n//2, go into the middle n//2+1. Even n: wing n//2, centre is the hinge |0|. n <= 3: centre |n|.
from functools import lru_cache
from sympy import primerange

@lru_cache(None)
def u(n):
    return {0: 0, 1: 1, 2: 2, 3: 3}[n] if n <= 3 else (2 * u(n // 2) if n % 2 == 0 else 2 * u(n // 2) + u(n // 2 + 1))

def spine(n):
    wings = []
    while n > 3:
        wings.append(n // 2)
        if n % 2 == 0:
            return wings, 0
        n = n // 2 + 1
    return wings, n

def selfcount(m):
    while m % 2 == 0: m //= 2
    return m in (1, 3)

if __name__ == "__main__":
    assert spine(33) == ([16, 8, 4, 2], 3) and spine(11) == ([5, 3], 0)
    for n in range(2, 3000):
        w, c = spine(n)
        assert u(n) == 2 * sum(u(x) for x in w) + u(c)  # units = wings twice + centre
    for p in primerange(11, 100):
        w, c = spine(p)
        tag = "".join("s" if selfcount(x) else "." for x in w)
        print(f"{p:3d} = {','.join(map(str, w))},|{c}|   folds {len(w)}  self-count wings {tag:<6s} u {u(p):3d}  2p-u {2*p-u(p):4d}  p mod 4 = {p % 4}  root {'2|3' if (p >> (p.bit_length()-2)) == 2 else '1|2'}")

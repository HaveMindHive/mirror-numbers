# Split-centre tell (tUrUq, 11-26-2026): for consecutive primes p < q the centre of the split is m = (p+q)/2,
# the mirror seat of the pair (7 and 11 -> 9). Read m in the build: ones (units), zeros, commas (zoom levels),
# and its mirrors, and see what carries the half gap h = (q-p)/2.
import math
from functools import lru_cache
from collections import defaultdict
from sympy import primerange, divisor_count, factorint

@lru_cache(None)
def u(n):
    return {0: 0, 1: 1, 2: 2, 3: 3}[n] if n <= 3 else (2 * u(n // 2) if n % 2 == 0 else 2 * u(n // 2) + u(n // 2 + 1))

def width(n):  # equal-width build: 3^levels; levels step after the walls 3*2^k
    L = 1
    while n > 3 * 2 ** (L - 1): L += 1
    return 3 ** L

def feats(m):
    W = width(m)
    f = factorint(m)
    return dict(ones=u(m), zeros=W - u(m), levels=round(math.log(W, 3)), imb=u(m) - m,
                tau=divisor_count(m), v2=f.get(2, 0), v3=f.get(3, 0), mod6=m % 6, mod30=m % 30,
                smallest=min(f) if f else 1)

if __name__ == "__main__":
    assert width(9) == 27 and width(6) == 9 and width(13) == 81 and u(9) == 15
    ps = list(primerange(3, 2 * 10 ** 6))
    rows = [((p + q) // 2, (q - p) // 2, p) for p, q in zip(ps, ps[1:])]
    print("first splits: " + ", ".join(f"{p}|{2*m-p}: centre {m} half {h}" for m, h, p in rows[:12]))
    for key in ("mod6", "mod30", "tau", "v2", "v3", "smallest"):
        acc = defaultdict(list)
        for m, h, p in rows:
            acc[feats(m)[key]].append(h)
        top = sorted(acc.items(), key=lambda kv: -len(kv[1]))[:8]
        print(f"\nmean half-gap by {key}:", "; ".join(f"{k}: {sum(v)/len(v):.3f} (n={len(v)})" for k, v in sorted(top)))
    # does the centre's own reading equal the half gap anywhere often?
    hits = defaultdict(int)
    for m, h, p in rows:
        F = feats(m)
        for k in ("v2", "v3", "tau", "smallest", "levels"):
            if F[k] == h: hits[k] += 1
    print("\nexact matches feature == half gap:", dict(hits), "of", len(rows))

def allowed(m, h, mirrors):
    """The mirror rule at a split centre: a mirror r through the centre (r | m) forbids only h = 0 mod r;
    a mirror off the centre forbids the two mirrored classes h = +m and h = -m mod r."""
    for r in mirrors:
        if (m % r == 0 and h % r == 0) or (m % r and h % r in (m % r, (-m) % r)):
            return False
    return True

def tell(m, mirrors):
    h = 1
    while not allowed(m, h, mirrors): h += 1
    return h

if __name__ == "__main__":
    assert tell(9, [2, 3]) == 2  # 7 | 9 | 11
    for R in ([2, 3], [2, 3, 5], [2, 3, 5, 7], [2, 3, 5, 7, 11, 13], [2, 3, 5, 7, 11, 13, 17, 19, 23]):
        big = [(m, h) for m, h, p in rows if p > R[-1] ** 2]
        exact = sum(tell(m, R) == h for m, h in big)
        print(f"mirrors up to {R[-1]}: the first allowed half-gap is the real one for {exact} of {len(big)} splits ({exact/len(big):.4f})")

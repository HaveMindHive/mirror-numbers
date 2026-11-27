# Ladder shorthand (tUrUq, 11-26-2026): every zoom level of n holds only two neighbours k, k+1.
# n is written as its ladder of pairs from the top down; units climb the ladder by
# u(2k) = 2u(k), u(2k+1) = 2u(k) + u(k+1), u(2k+2) = 2u(k+1).
from functools import lru_cache

@lru_cache(None)
def u(n):
    return {0: 0, 1: 1, 2: 2, 3: 3}[n] if n <= 3 else (2 * u(n // 2) if n % 2 == 0 else 2 * u(n // 2) + u(n // 2 + 1))

def ladder(n):
    """Pairs (k, k+1) at each zoom level, top first, until the pair is made of words (<= 3)."""
    out, k = [], n // 2
    while True:
        out.append((k, k + 1))
        if k + 1 <= 3: return out
        k //= 2

def short(n):
    mid = "0" if n % 2 == 0 else str(n // 2 + 1)
    return f"{n} = {n // 2},{mid},{n // 2} | " + " : ".join(f"{a}|{b}" for a, b in ladder(n))

if __name__ == "__main__":
    assert u(19) == 44 and ladder(19) == [(9, 10), (4, 5), (2, 3)]
    for n in (11, 15, 17, 19, 33, 97, 1000):
        print(short(n), "   units", u(n), "  pair units", [(u(a), u(b)) for a, b in ladder(n)])

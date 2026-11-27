# Unit counting, fold notation, orders and the divisor build (Turaq Rayn-McLean, 11-24-2026, v2.1). MIT licence.
from functools import lru_cache
from itertools import permutations

WORD = {0: "000", 1: "010", 2: "101", 3: "111"}


def unit_product(*factors):
    """Product in which no unit is lost.
    All factors bare ones -> count of ones. Otherwise ones drop out, rest multiply as usual."""
    if all(f == 1 for f in factors):
        return len(factors)
    out = 1
    for f in factors:
        if f != 1:
            out *= f
    return out


@lru_cache(None)
def B(n):
    """Halving build at order 0: B(2k) = B(k),0,B(k); B(2k+1) = B(k),B(k+1),B(k)."""
    if n <= 3:
        return WORD[n]
    k = n // 2
    return B(k) + WORD[0] + B(k) if n % 2 == 0 else B(k) + B(k + 1) + B(k)


def rewrite(s):
    """One order: 0 -> 000, 1 -> 010, every digit at once."""
    return "".join("010" if ch == "1" else "000" for ch in s)


def order(n, k):
    s = B(n)
    for _ in range(k):
        s = rewrite(s)
    return s


def prime_factors(n):
    f, d = [], 2
    while d * d <= n:
        while n % d == 0:
            f.append(d)
            n //= d
        d += 1
    return f + ([n] if n > 1 else [])


def leaf(p):
    """1, 2, 3 by their words; a prime above 3 cannot be split into equal copies: p units."""
    return WORD[p] if p in WORD else WORD[0].join([WORD[1]] * p)


def face(factors):
    """Divisor build for one arrangement: outermost factor first; the zero between copies grows one order per level."""
    s, level = leaf(factors[-1]), 1  # first gap one order above the zero inside a prime
    for d in reversed(factors[:-1]):
        s = ("000" * 3 ** level).join([s] * d)
        level += 1
    return s


def faces(n):
    return {arr: face(list(arr)) for arr in sorted(set(permutations(prime_factors(n))))}


if __name__ == "__main__":
    assert unit_product(1, 1) == 2 and unit_product(1, 1, 1) == 3
    assert unit_product(1, 3) == 3 and unit_product(1, 1, 3) == 3 and unit_product(2, 3) == 6
    assert B(5) == "101111101" and B(4) == "101000101"
    assert rewrite(WORD[2]) == "010000010" and rewrite(WORD[0]) == "000000000"
    for n in range(1, 300):
        assert B(n) == B(n)[::-1]
        for k in (1, 2):
            s0, sk = B(n), order(n, k)
            assert sk.count("1") == s0.count("1")  # units fixed across orders
        if n >= 2:
            for s in faces(n).values():
                assert s.count("1") == n and s == s[::-1]  # no unit lost; mirror
    assert face([2, 2, 3]) == "111" + "0" * 9 + "111" + "0" * 27 + "111" + "0" * 9 + "111"
    for n in range(2, 300):
        fs = faces(n)
        assert len(set(fs.values())) == len(fs)  # every arrangement its own string
        if len(prime_factors(n)) > 1:
            assert leaf(n) not in fs.values()  # no composite reads like a prime
    print("all checks pass")

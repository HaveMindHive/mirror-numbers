# Facing number line (tUrUq, 11-26-2026). One build for every number, odd and even alike.
# Words 0=000, 1=010, 2=101, 3=111. n = k, middle, mirror(k): middle is the hinge (zeros) for even n, k+1 for odd n.
# All blocks at one zoom level are the same width (narrower ones zoom in: 0->000, 1->010), so width is a power of 3.
# Commas: the number of commas at a boundary = how many zoom levels end there.
# Short form: everything up to the centre digit, then | (fold back on that digit).
from functools import lru_cache
from sympy import isprime

W = {0: "000", 1: "010", 2: "101", 3: "111"}

def zoom(s):
    return "".join("010" if c == "1" else "000" for c in s)

@lru_cache(None)
def B(n):
    if n <= 3:
        return W[n]
    k = n // 2
    a = B(k)
    b = B(k + 1) if n % 2 else "0" * len(a)
    while len(b) < len(a): b = zoom(b)
    while len(a) < len(b): a = zoom(a)
    return a + b + a[::-1]

def commas(s):
    out = []
    for i, c in enumerate(s):
        if i and i % 3 == 0:
            j = 0
            while i % 3 ** (j + 1) == 0: j += 1
            out.append("," * j)
        out.append(c)
    return "".join(out)

def short(n):
    s = B(n)
    return commas(s[: len(s) // 2 + 1]) + "|"

def unfold(sh):
    h = sh.replace(",", "").rstrip("|")
    return h + h[-2::-1]

def centre_path(n):
    """Which block holds the centre at each zoom: O = a filled middle (odd), E = the hinge (even, centre is zero below)."""
    p = ""
    while n > 3:
        if n % 2 == 0:
            return p + "E"
        p += "O"; n = n // 2 + 1
    return p + str(n)

def row(n):
    s = B(n)
    return dict(n=n, prime=isprime(n), width=len(s), units=s.count("1"), centre=s[len(s) // 2],
                path=centre_path(n), short=short(n))

if __name__ == "__main__":
    assert B(9) == "101000101" + "101111101" + "101000101"
    assert commas(B(8)) == "101,000,101,,000,000,000,,101,000,101"
    for n in range(1, 600):
        s = B(n)
        assert s == s[::-1] and unfold(short(n)) == s and len(s) == 3 ** round(__import__("math").log(len(s), 3))
        assert (s[len(s) // 2] == "1") == (n in (1, 3) or (n > 3 and n % 2 == 1 and ((n - 1) & (n - 2)) == 0))
    for n in range(1, 41):
        r = row(n)
        print(f"{n:3d} {'P' if r['prime'] else ' '} w{r['width']:<4d} units {r['units']:3d} centre {r['centre']} path {r['path']:<6s} {r['short'] if r['width'] <= 81 else ''}")

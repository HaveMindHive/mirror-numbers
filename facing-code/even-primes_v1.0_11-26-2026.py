# Even primes in the facing code (tUrUq, 11-26-2026).
# | = where the mirror sits. |0,X = mirror on the hinge 0 (even). |a,b = mirror on block a, wing b (odd).
from sympy import isprime

def code(n):
    """Nested facing shorthand by halving: 2k = |0,(k); 2k+1 = |(k+1),(k). Words 0..3 stay as numbers."""
    if n <= 3:
        return str(n)
    k = n // 2
    return f"|0,({code(k)})" if n % 2 == 0 else f"|{code(k + 1)},({code(k)})"

def even_mirrors(n):
    """How many gap mirrors (|0) the code opens with before reaching an odd: the halving depth."""
    d = 0
    while n % 2 == 0 and n > 3:
        n //= 2; d += 1
    return d, n

def even_world_prime(n):
    """Prime inside the evens alone: even, not 2 (the 1 of evens), and not a product of two evens."""
    return n % 2 == 0 and n != 2 and not any(n % a == 0 and (n // a) % 2 == 0 for a in range(2, n, 2))

def even_world_factorings(n):
    """All ways to write n as a product of even-world primes (unordered)."""
    ps = [p for p in range(4, n + 1, 2) if even_world_prime(p)] + [2]
    ps = sorted(set(ps))
    out = []
    def go(m, start, acc):
        if m == 1:
            out.append(tuple(acc)); return
        for i in range(start, len(ps)):
            p = ps[i]
            if p > m: break
            if m % p == 0:
                go(m // p, i, acc + [p])
    go(n, 0, [])
    return [f for f in out if f != (n,) or even_world_prime(n)]

if __name__ == "__main__":
    # self-checks
    assert code(7) == "||0,(2),(3)" and code(14) == "|0,(" + code(7) + ")"
    assert all(even_world_prime(n) == (n % 4 == 2 and n != 2) for n in range(2, 400))
    rows = []
    for n in range(4, 61, 2):
        k = n // 2
        d, core = even_mirrors(n)
        tag = ("2p " if isprime(k) else "   ") + ("E " if even_world_prime(n) else "  ")
        rows.append(f"{n:3d}  pos {k:2d}  {tag}  depth {d}  core {core:2d}  {code(n)}")
    print("n   even-line pos   2p=prime position  E=prime in the evens alone")
    print("\n".join(rows))
    print("\nFirst E that is not 2p:", next(n for n in range(4, 400, 2) if even_world_prime(n) and not isprime(n // 2)))
    print("Evens with two different even-world factorings (pairs), up to 200:")
    for n in range(4, 201, 4):
        two = [(a, n // a) for a in range(2, int(n ** 0.5) + 1, 2)
               if n % a == 0 and (n // a) % 2 == 0 and (a == 2 or even_world_prime(a)) and (n // a == 2 or even_world_prime(n // a))]
        if len(two) > 1:
            print(f"  {n} = " + " = ".join(f"{x}x{y}" for x, y in two))

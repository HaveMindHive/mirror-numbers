# All mirrors (tUrUq, 11-26-2026). Every prime becomes its own mirror the moment it appears.
# n with an equal split takes its first mirror q (the smallest q that splits it into q equal copies of n/q):
#   q = 2:  <k,0,k>             two observers around the hinge
#   q odd:  k>,<k>,...,<k       q copies: operator past, observers, operator future (all copies count)
# n with no equal split is a prime: it can only take the odd halving  k>,k+1,<k  (operators on the centre).
# The operator chain of a prime: step into its centre (p+1)/2 while the centre is again a prime.
from sympy import isprime, primerange
from collections import Counter

def first_mirror(n):
    q = 2
    while q * q <= n:
        if n % q == 0: return q
        q += 1
    return None  # no equal split: prime

def top(n):
    q = first_mirror(n)
    if q is None:
        k = n // 2
        return f"{k}>,{k + 1},<{k}"
    k = n // q
    if q == 2: return f"<{k},0,{k}>"
    return ",".join([f"{k}>"] + [f"<{k}>"] * (q - 2) + [f"<{k}"])

def chain(p):
    out = [p]
    while p > 3 and isprime((p + 1) // 2):
        p = (p + 1) // 2; out.append(p)
    return out

if __name__ == "__main__":
    for n in range(4, 20000):
        assert (first_mirror(n) is None) == isprime(n)
    assert top(25) == "5>,<5>,<5>,<5>,<5" and top(13) == "6>,7,<6" and chain(73) == [73, 37, 19]
    print("\n".join(f"{n:3d} {'P' if isprime(n) else ' '} {top(n)}" for n in range(15, 61)))
    N = 10 ** 6
    met = Counter()
    for p in primerange(5, N):
        met[first_mirror((p + 1) // 2) or "prime"] += 1
    print("\nfirst mirror met inside a prime's centre (p+1)/2, primes 5..1e6:", sorted(met.items(), key=lambda x: -x[1])[:10])
    longest = sorted((chain(p) for p in primerange(5, N)), key=len, reverse=True)[:8]
    print("longest operator chains (upward reading from the small end):", [c[::-1] for c in longest])

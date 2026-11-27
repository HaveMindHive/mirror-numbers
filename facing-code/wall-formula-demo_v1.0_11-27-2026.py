# One formula for the primes in wall coordinates (tUrUq, 11-27-2026). Lean: WallFormula.wall_formula, nth_prime_formula.
# A seat n = 6k + f (f = +-1) is prime exactly when no block 6j + g (j >= 1, g = +-1, (6j+g)^2 <= n) divides k - f*g*j.
# No list of primes: every block is named by its own wall j and wing g.
from sympy import prime, primepi

def is_prime_wall(n):
    if n < 5: return n in (2, 3)
    k, f = (n + 1) // 6, None
    f = n - 6 * k
    if f not in (1, -1): return False
    j = 1
    while (6 * j - 1) ** 2 <= n:
        for g in (-1, 1):
            r = 6 * j + g
            if r * r <= n and (k - f * g * j) % r == 0: return False
        j += 1
    return True

def pi(a): return sum(is_prime_wall(x) for x in range(a))            # primes below a
def p(n): return sum(1 for a in range(2 ** (n + 1) + 1) if pi(a) <= n) - 1  # nth_prime_formula, p_0 = 2

assert all(is_prime_wall(n) == (primepi(n) - primepi(n - 1) == 1) for n in range(2, 200000))
print("wall formula agrees with sympy on every n from 2 to 199,999")
print("p_n by the one formula, n = 0..11:", [p(n) for n in range(12)])
assert [p(n) for n in range(12)] == [prime(n + 1) for n in range(12)]
print("matches sympy.prime")

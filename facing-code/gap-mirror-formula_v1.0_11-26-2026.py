# Gap mirror formula (tUrUq, 11-26-2026). Each odd mirror r that sits in the gap (r | g) cannot block the centre,
# so it lets more splits through: weight (r-1)/(r-2). Mirror weight of a gap: M(g) = product over odd primes r | g.
# Splits of gap g:  N(g) ~ A * M(g) * exp(-g / L)   (A, L fitted once; L is the mean gap scale).
import math
from fractions import Fraction
from collections import Counter
from sympy import primerange, primefactors

def M(g):
    w = Fraction(1)
    for r in primefactors(g):
        if r > 2: w *= Fraction(r - 1, r - 2)
    return w

if __name__ == "__main__":
    assert M(6) == 2 and M(10) == Fraction(4, 3) and M(30) == Fraction(8, 3) and M(2) == 1
    for top in (2 * 10 ** 6, 2 * 10 ** 7):
        ps = list(primerange(3, top))
        N = Counter(q - p for p, q in zip(ps, ps[1:]))
        gs = [g for g in range(2, 61, 2) if N[g] > 50]
        # fit log(N/M) = log A - g/L by least squares
        xs = gs; ys = [math.log(N[g] / float(M(g))) for g in gs]
        n = len(xs); mx = sum(xs) / n; my = sum(ys) / n
        b = sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / sum((x - mx) ** 2 for x in xs)
        a = my - b * mx
        print(f"\nprimes below {top}: L = {-1/b:.3f}, mean gap = {(ps[-1]-ps[0])/(len(ps)-1):.3f}")
        worst = 0
        for g in gs:
            pred = math.exp(a + b * g) * float(M(g))
            worst = max(worst, abs(N[g] / pred - 1))
            if g <= 36: print(f"  gap {g:2d}: mirror weight {str(M(g)):>5s}  real {N[g]:7d}  formula {pred:9.1f}  ratio {N[g]/pred:.3f}")
        print(f"  worst ratio off by {worst:.3f} over gaps {gs[0]}..{gs[-1]}")

# Predict, then confirm (tUrUq, 11-26-2026): from p alone, use the rule of how primes change to rank where the next
# prime can sit, then confirm candidates in that order with the short-range construction.
# Rule of change used (from p only): the 6-facing hand-off (q stays off the 2 and 3 mirrors given p's seat) and the
# gap weights M(g) * exp(-g/L) (each odd mirror r in the gap lifts it by (r-1)/(r-2)); L from p's size (mean gap ~ ln p).
import math
from fractions import Fraction
from sympy import primerange, primefactors

def M(g):
    w = 1.0
    for r in primefactors(g):
        if r > 2: w *= (r - 1) / (r - 2)
    return w

def ranked_gaps(p, top=400):
    L = math.log(p)
    cands = [g for g in range(2, top, 2) if (p + g) % 3 != 0]          # facing: p+g off the 3 mirror (from p's seat)
    return sorted(cands, key=lambda g: -M(g) * math.exp(-g / L))

if __name__ == "__main__":
    assert ranked_gaps(7)[0] in (4, 6) and all((7 + g) % 3 for g in ranked_gaps(7))
    for lo, hi in ((10 ** 3, 10 ** 4), (10 ** 4, 10 ** 5), (10 ** 5, 10 ** 6)):
        ps = list(primerange(lo, hi + 2000))
        ranks, walks = [], []
        for p, q in zip(ps, ps[1:]):
            if p >= hi: break
            order = ranked_gaps(p)
            ranks.append(order.index(q - p) + 1)                          # confirmations needed in predicted order
            walks.append(sum(1 for g in range(2, q - p + 1, 2) if (p + g) % 3 != 0))   # walking up, same facing rule
        n = len(ranks)
        cover = {k: sum(r <= k for r in ranks) / n for k in (1, 2, 3, 5, 10)}
        print(f"p in [{lo},{hi}): {n} gaps | first guess right {cover[1]:.4f}, in top 2 {cover[2]:.4f}, top 3 {cover[3]:.4f}, "
              f"top 5 {cover[5]:.4f}, top 10 {cover[10]:.4f} | mean confirmations: predicted order {sum(ranks)/n:.3f}, walking up {sum(walks)/n:.3f}")

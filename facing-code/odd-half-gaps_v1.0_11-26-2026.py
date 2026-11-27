# Odd half gaps (tUrUq, 11-26-2026): splits whose half gap h is 3, 5, 7, 9, 11 (gaps 6, 10, 14, 18, 22), and gap 10 / gap 20.
# For each h: how many splits, and where the centre m sits on the mirrors 2, 3, 5, 7 (through the centre = r | m).
from collections import Counter
from sympy import primerange

if __name__ == "__main__":
    ps = list(primerange(3, 2 * 10 ** 6))
    rows = [((p + q) // 2, (q - p) // 2) for p, q in zip(ps, ps[1:])]
    for m, h in rows:  # exact: a mirror through the centre never divides the half gap
        for r in (2, 3, 5, 7):
            assert not (m % r == 0 and h % r == 0) or m - h == r
    total = Counter(h for _, h in rows)
    print("splits by half gap h (gap 2h):", ", ".join(f"h{h}: {total[h]}" for h in range(1, 16)))
    for h in (1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 15):
        ms = [m for m, hh in rows if hh == h]
        through = {r: sum(m % r == 0 for m in ms) / len(ms) for r in (2, 3, 5, 7)}
        mod30 = Counter(m % 30 for m in ms).most_common(4)
        print(f"h={h:2d} (gap {2*h:2d}) n={len(ms):6d}  share of centres on mirror 2: {through[2]:.3f}  3: {through[3]:.3f}  5: {through[5]:.3f}  7: {through[7]:.3f}   top centre mod 30: {mod30}")

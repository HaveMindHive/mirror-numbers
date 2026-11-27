# The wall walk taken far (tUrUq's method, 11-27-2026). Author of the method: Turaq Rayn-McLean.
# Every number past 3 that can be prime sits on a wing of a wall of 6: seat 6k-1 or 6k+1 (Lean: TwoZero.stacked_six).
# A prime block r = 6kr + fr (fr = +-1) closes wing f of wall k exactly when k = f*fr*kr (mod r)
# (Lean: PrimeHandOff.wall_law_prime). The walk names primes in order and each one it names becomes a block
# for the walls further out; no outside prime list is used to build anything.
# Checks, kept apart from the build: every closed seat carries the block that closed it, and that block must
# divide the seat (so the seat is shown not prime); the open seats are then counted against sympy.primepi,
# so no prime can be missing. Far windows (10^12, 10^15, 10^18) are built the same way and every open seat
# there is checked with sympy.isprime.
import sys, time
import numpy as np
from sympy import primepi, isprime

TOP = int(float(sys.argv[1])) if len(sys.argv) > 1 else 1_500_000_000   # walk every seat up to here
KEEP = 1_000_001_000                                                     # blocks kept for the far windows
SEG = 10_000_000                                                         # walls per stretch
t0 = time.time()
say = lambda *a: print(*a, flush=True)


def close_stretch(K0, K1, blocks):
    """Lay every block's closings over walls K0..K1-1. Returns, per wing, the smallest closing block (0 = open)."""
    L = K1 - K0
    lo = np.zeros(L, np.int64); hi = np.zeros(L, np.int64)       # wing -1 (6k-1) and wing +1 (6k+1)
    r = blocks[::-1]                                              # largest first, so the smallest block is written last
    kr = (r + 1) // 6; fr = r - 6 * kr
    for f, arr in ((-1, lo), (1, hi)):
        first = (f * fr * kr - K0) % r                            # first wall in the stretch this block closes
        own = (K0 + first == kr) & (f == fr)                      # the block's own seat is not closed by itself
        first = np.where(own, first + r, first)
        small = r < L
        for b, s in zip(r[small], first[small]):
            arr[s::b] = b
        big = (~small) & (first < L)
        arr[first[big]] = r[big]
    return lo, hi


def seats(K0, lo, hi):
    k = np.arange(K0, K0 + len(lo), dtype=np.int64)
    return 6 * k - 1, 6 * k + 1


# ---- 1. the walk from the start ----
blocks = np.array([], np.int64)
named = 2                      # 2 and 3, the two mirrors
K0, KMAX = 1, (TOP + 1) // 6
kept = []
while K0 <= KMAX:
    top_named = int(blocks[-1]) if len(blocks) else 3
    K1 = min(K0 + SEG, KMAX + 1, (top_named ** 2 + 1) // 6 + 1 if len(blocks) else 4)
    need = blocks[blocks * blocks <= 6 * (K1 - 1) + 1]
    lo, hi = close_stretch(K0, K1, need) if len(need) else (np.zeros(K1 - K0, np.int64),) * 2
    a, b = seats(K0, lo, hi)
    for s, c in ((a, lo), (b, hi)):                              # certificate: the closing block divides the seat
        cl = c > 0
        assert np.all(s[cl] % c[cl] == 0) and np.all(c[cl] < s[cl])
    opened = np.sort(np.concatenate((a[lo == 0], b[hi == 0])))
    opened = opened[opened <= TOP]
    named += len(opened)
    blocks = np.concatenate((blocks, opened))
    if len(blocks) and blocks[-1] > KEEP and K0 > 1:
        blocks = blocks[blocks <= max(KEEP, int(np.sqrt(6 * KMAX + 1)) + 1)]
    K0 = K1
    if K1 % (SEG * 5) < SEG: say(f"  walked to {6 * (K1 - 1) + 1:,}: {named:,} named ({time.time() - t0:.0f}s)")

key = int(primepi(TOP))
say(f"WALK: every seat from 2 to {TOP:,}. Named {named:,}; answer key (sympy.primepi) {key:,}; "
    f"{'EXACT, no prime missed, no composite let through' if named == key else 'MISMATCH'}")
assert named == key
blocks = blocks[blocks <= KEEP]
say(f"  blocks kept for the far windows: {len(blocks):,} (largest {int(blocks[-1]):,}) ({time.time() - t0:.0f}s)")

# ---- 2. far windows: walls far out, blocks from the walk ----
for N in (10 ** 12, 10 ** 15, 10 ** 18):
    WALLS = 50_000
    K0 = N // 6
    need = blocks[blocks * blocks <= 6 * (K0 + WALLS) + 1]
    assert int(need[-1]) ** 2 <= 6 * (K0 + WALLS) + 1 < (int(blocks[blocks * blocks > 6 * (K0 + WALLS) + 1][0]) ** 2)
    lo, hi = close_stretch(K0, K0 + WALLS, need)
    a, b = seats(K0, lo, hi)
    bad = 0
    for s, c in ((a, lo), (b, hi)):
        cl = c > 0
        assert np.all(s[cl] % c[cl] == 0)
    opened = sorted(int(x) for x in np.concatenate((a[lo == 0], b[hi == 0])))
    bad = sum(1 for x in opened if not isprime(x))
    # consecutive: no prime between named neighbours (every other seat in the window is closed by a dividing block)
    say(f"WINDOW at {N:.0e}: walls {K0:,} to {K0 + WALLS - 1:,} ({2 * WALLS:,} seats), blocks up to {int(need[-1]):,}. "
        f"Named {len(opened):,} primes in order, first {opened[0]:,}, last {opened[-1]:,}; "
        f"sympy.isprime disagrees on {bad}. ({time.time() - t0:.0f}s)")
    assert bad == 0
say(f"done in {time.time() - t0:.0f}s")

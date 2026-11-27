"""Turn roots (tUrUq, 11-26-2026).
A build = its turn set T: odd t >= 3 written as t equal unit copies (t = 1,1,...,1), so u(t) = t.
Everything else is halving: u(1)=1, u(2)=2, u(2k)=2u(k), u(2k+1)=2u(k)+u(k+1).
T={3}: the halving build with 3 = 1,1,1.  T={}: pure halving (3 = 1,2,1).  T={5}: 5 = 1,1,1,1,1.
For each build: self-count points (u=n), the line u=2n, strands, and odd points below the line off the strands.
Odd n = 2k+1 below the line (n not a turn) comes in three kinds:
  strand    : k self-count and k+1 below the line            (n = c*2^a+1)
  pair point: n = 4j+3 with j, j+1 both self-count, 2j+1 not (wings 2j+1 = j+(j+1), centre 2(j+1)); u = 2n-2
  near-turn : k+1 = a turn t, n = 2t-1, with 2u(t-1) < 3t-2
Lean (any turn set): PRIMES_Fold_v1.0_11-20-2026/lean-turn-roots_v1.0_11-26-2026/TurnRoots.lean
"""
from itertools import combinations
import sys

def build(T, N):
    T = set(T); u = [0] * (N + 2)
    for n in range(1, N + 2):
        if n <= 2 or n in T: u[n] = n
        elif n % 2 == 0: u[n] = 2 * u[n // 2]
        else: k = n // 2; u[n] = 2 * u[k] + u[k + 1]
    return u

def core(n):
    while n % 2 == 0: n //= 2
    return n

def analyse(T, N):
    u = build(T, N); C = (1,) + tuple(T)
    S = {n for n in range(1, N + 1) if u[n] == n}
    assert S == {c << a for c in C for a in range(N.bit_length()) if c << a <= N}, T   # self-count = c*2^a
    assert all(u[n] != 2 * n for n in range(1, N + 1)), T                               # nothing on the line
    below = [n for n in range(1, N + 1, 2) if u[n] < 2 * n]
    off = [n for n in below if not (n > 2 and core(n - 1) in C)]
    kinds = {}
    for n in off:
        k = n // 2
        if n == 1 or n in T: kinds[n] = 'root' if n == 1 else 'turn'
        elif k % 2 == 1 and (k - 1) // 2 in S and (k + 1) // 2 in S: kinds[n] = 'pair'; assert u[n] == 2 * n - 2
        elif k + 1 in T: kinds[n] = 'near-turn'
        else: raise AssertionError(('unexplained', T, n))
        if n > 1 and n not in T: assert k in S or k + 1 in S                           # never neither
    dead = sorted({c for c in C if c > 1 and u[(c << 1) + 1] >= 2 * ((c << 1) + 1)})  # strand c*2^a+1 absent
    for c in dead:  # whole strand absent iff c+1 above the line
        assert all(u[(c << a) + 1] >= 2 * ((c << a) + 1) for a in range(1, 12) if (c << a) + 1 <= N)
        assert u[c + 1] >= 2 * (c + 1)
    return u, off, kinds, dead

def predicted_pairs(T):
    """Pair points from neighbouring self-count points j, j+1 (one is odd: 1 or a turn)."""
    C = (1,) + tuple(T); S = {c << a for c in C for a in range(12)}
    return sorted(4 * j + 3 for j in S if j + 1 in S and 2 * j + 1 not in S and 4 * j + 3 not in T)

if __name__ == '__main__':
    out = []; N = 1 << 20
    named = [(), (3,), (5,), (7,), (3, 5), (3, 7), (5, 7), (3, 5, 7), (9,), (13,), (15,)]
    out.append('build | self-count cores | line | off-strand odd points below u=2n (kind, deficit 2n-u) to 2^20')
    for T in named:
        u, off, kinds, dead = analyse(T, N)
        assert sorted(n for n in off if kinds[n] == 'pair') == predicted_pairs(T)
        rows = ', '.join(f'{n}({kinds[n]},{2*n-u[n]})' for n in off)
        out.append(f'T={set(T) or "{}"} | {sorted((1,)+T)} | u=2n never | {rows}' + (f' | strands absent: {dead}' if dead else ''))
    exp = {(): [1, 7], (3,): [1, 11, 15], (5,): [1, 7, 19], (7,): [1, 7, 13, 31], (3, 5): [1, 15, 19, 23],
           (3, 7): [1, 11, 27, 31], (5, 7): [1, 7, 13, 19, 31], (3, 5, 7): [1, 19, 23, 27, 31]}
    for T, e in exp.items(): assert analyse(T, N)[1] == e, T
    # sweep: every single turn t < 64, every pair < 32, every triple < 16 (to 2^15)
    sets = [(t,) for t in range(3, 64, 2)] + list(combinations(range(3, 32, 2), 2)) + list(combinations(range(3, 16, 2), 3))
    for T in sets:
        _, off, kinds, _ = analyse(T, 1 << 15)
        assert sorted(n for n in off if kinds[n] == 'pair') == predicted_pairs(T)
    out.append(f'sweep {len(sets)} turn sets to 2^15: self-count = c*2^a, u=2n never, every off-strand point is root/turn/pair/near-turn, pair points match prediction.')
    # single-turn rule: t = 2^b+1 -> 4t-1 (11-type), t = 2^b-1 -> 4t+3 (15-type); 3 is both
    for t in range(3, 200, 2):
        p = predicted_pairs((t,)); own = [n for n in p if n != 7]
        want = ([4 * t - 1] if (t - 1) & (t - 2) == 0 else []) + ([4 * t + 3] if (t + 1) & t == 0 else [])
        assert own == sorted(want), (t, p)
    out.append('single turn t: own pair points = {4t-1 if t-1 is a power of 2} + {4t+3 if t+1 is a power of 2}; root pair 7 stays unless 3 is a turn. Checked t < 200.')
    txt = '\n'.join(out); print(txt)
    open(__file__.replace('.py', '.txt'), 'w').write(txt + '\n')

"""Many turns (tUrUq, 11-26-2026): "there will be more turns ... another brick mortored in on the pattern".
Builds (halving u(2k)=2u(k), u(2k+1)=2u(k)+u(k+1) wherever no turn/face is set):
  A(B): turns at every odd 3..B (u(t)=t).
  B   : every odd composite n is q equal copies of n/q, q its smallest block: u(n) = q*u(n/q);
        odd primes keep the halving k, k+1, k.
  C   : turns at the odd primes (bakes primality into the leaves; contrast only).
Odd n = 2k+1 below the line (u < 2n), not a turn, is read as
  strand (k self-count) | pair (k = 2j+1, j, j+1 self-count) | near-turn (k+1 self-count) | sporadic (none).
Lean, every turn set T (A, C, pure halving, 3-turn alike): line_never, no_sporadic, below_classify,
  three_quarter, strand_deficit in PRIMES_Fold_v1.0_11-20-2026/lean-many-turns_v1.0_11-26-2026/ManyTurns.lean
Imports turn-roots_v1.0_11-26-2026.py unchanged.
"""
import importlib.util, os
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location('tr', os.path.join(HERE, 'turn-roots_v1.0_11-26-2026.py'))
tr = importlib.util.module_from_spec(spec); spec.loader.exec_module(tr)
N = 1 << 20
LOG = N.bit_length()

SP = list(range(N + 2))                       # smallest block
for i in range(2, int((N + 1) ** .5) + 1):
    if SP[i] == i:
        for j in range(i * i, N + 2, i):
            if SP[j] == j: SP[j] = i
isp = lambda n: n > 2 and SP[n] == n          # odd primes

def build_B(N):
    u = [0] * (N + 2)
    for n in range(1, N + 2):
        if n <= 2: u[n] = n
        elif n % 2 == 0: u[n] = 2 * u[n // 2]
        elif not isp(n): q = SP[n]; u[n] = q * u[n // q]
        else: k = n // 2; u[n] = 2 * u[k] + u[k + 1]
    return u

def read(u, N, leaf):
    """leaf(n): n is a turn (A, C) or a copy face (B composite): not read by halving."""
    S = {n for n in range(1, N + 1) if u[n] == n}
    assert all(u[n] != 2 * n for n in range(1, N + 1))                     # the line
    kinds = {}
    for n in range(3, N + 1, 2):
        if u[n] >= 2 * n or leaf(n): continue
        k = n // 2
        if k in S: c = 'strand'
        elif k % 2 == 1 and (k - 1) // 2 in S and (k + 1) // 2 in S: c = 'pair'; assert u[n] == 2 * n - 2   # Lean pair_point
        elif k + 1 in S: c = 'near'
        else: c = 'sporadic'
        kinds[n] = c
    return S, kinds

def blocks(ns):
    c = Counter(n.bit_length() - 1 for n in ns)
    return [c.get(m, 0) for m in range(LOG)]

def core(n):
    while n % 2 == 0: n //= 2
    return n

out = []
def say(s): out.append(s); print(s)

# ---------- A: every odd up to B is a turn ----------
say('A. turns at every odd 3..B (to 2^20)')
for B in (9, 15, 31, 63, 127):
    T = set(range(3, B + 1, 2)); u = tr.build(T, N)
    S, kinds = read(u, N, lambda n: n in T)
    assert S == {n for n in range(1, N + 1) if core(n) <= B}                  # self-count = core <= B
    pairs = sorted(n for n in kinds if kinds[n] == 'pair')
    assert pairs == [4 * j + 3 for j in range((B + 1) // 2, B + 1)]           # pair law for A
    assert not any(c in ('near', 'sporadic') for c in kinds.values())
    strands = [n for n in kinds if kinds[n] == 'strand']
    assert all(core(n - 1) <= B for n in strands)
    for c in range(1, B + 1, 2):   # strand deficit constant: largest c*2^b+1 <= B+1 (a turn, or c+1)
        D = max((c << b) + 1 for b in range(LOG) if (c << b) + 1 <= B + 1)
        assert all(2 * n - u[n] == D for n in strands if core(n - 1) == c)
    per = blocks(strands)
    m0 = (2 * B).bit_length()
    assert all(per[m] == (B + 1) // 2 for m in range(m0, LOG - 1))           # (B+1)/2 strand points per block
    assert min(n for n in range(1, N, 2) if u[n] != n) == B + 2
    assert u[B + 2] == B + 1 + (B + 3) // 2
    say(f' B={B}: self-count = c*2^a, c odd <= {B}; line untouched; first non-self odd {B+2}, u = {u[B+2]} '
        f'(ratio {u[B+2]}/{B+2}); pair points {(B+1)//2}: {pairs[0]}..{pairs[-1]} step 4 (= 4j+3, j = {(B+1)//2}..{B}); '
        f'near-turn 0, sporadic 0; strands: one per core c <= {B}, deficit constant = largest c*2^b+1 <= {B+1}, {(B+1)//2} per dyadic block from 2^{m0}; '
        f'u/n at 2^20-1 = {u[N-1]/(N-1):.4f}')

# ---------- B: composites as equal-copy faces, primes keep halving ----------
say('B. odd composite n = q copies of n/q (q smallest block); odd primes halve (to 2^20)')
u = build_B(N)
assert all(u[n] >= n for n in range(1, N + 1))
S, kinds = read(u, N, lambda n: n > 2 and n % 2 and not isp(n))
assert S == {1 << a for a in range(LOG)}                                    # self-count = powers of 2 only
def top(n):  # largest odd prime block, 1 for a power of 2
    n = core(n); p = 1
    while n > 1: p = SP[n]; n //= SP[n]
    return p
for n in range(1, N + 1):                                                   # ratio law u(n)/n = u(P)/P
    P = top(n); assert u[n] * P == n * u[P]
below_odd = [n for n in range(3, N + 1, 2) if u[n] < 2 * n]
below_primes = [n for n in below_odd if isp(n)]
assert below_primes == [3, 5, 7, 17]
assert below_odd == [n for n in range(3, N + 1, 2) if top(n) in (3, 5, 7, 17)]   # {3,5,7,17}-smooth odds
assert kinds == {3: 'strand', 5: 'strand', 7: 'pair', 17: 'strand'}
# 2^a+1 chain: prime 2^a+1 below iff 2^(a-1)+1 below; chain 3,5,9,17 then 33 = 3*11 copies an above-line block
ch = [(1 << a) + 1 for a in range(1, 8)]
assert [u[n] < 2 * n for n in ch] == [True, True, True, True, False, False, False]
pr = [p for p in range(3, N, 2) if isp(p)]
minr = []
for m in range(2, LOG):
    rs = [u[p] / p for p in pr if p.bit_length() - 1 == m]
    if rs: minr.append(f'{m}:{min(rs):.3f}-{max(rs):.3f}')
say(f' self-count = 2^a only; line untouched; u(n)/n = u(P)/P exactly, P = largest odd prime block (n <= 2^20).')
say(f' below the line: n = 2^a * m, m odd with blocks only from {{3,5,7,17}}: {len(below_odd)} odd numbers 3..2^20.')
say(f' primes below the line: 3, 5, 17 (strand 2^a+1) and 7 (pair, the pure-halving root pair); every other prime to 2^20 above.')
say(f' prime u/p per dyadic block (min-max): ' + ' '.join(minr))

# ---------- C: turns at the odd primes ----------
say('C. turns at the odd primes (contrast; to 2^20)')
T = {p for p in range(3, N + 2, 2) if isp(p)}
u = tr.build(T, N)
S, kinds = read(u, N, lambda n: n in T)
assert S == {n for n in range(1, N + 1) if core(n) == 1 or isp(core(n))}
assert 'sporadic' not in kinds.values()
cnt = Counter(kinds.values())
for n, c in kinds.items():
    if c == 'near': assert isp(n // 2 + 1) and 2 * u[n // 2] + 2 < 3 * (n // 2 + 1)
pc = blocks([n for n in kinds if kinds[n] == 'pair']); nc = blocks([n for n in kinds if kinds[n] == 'near'])
sc = blocks([n for n in kinds if kinds[n] == 'strand'])
say(f' self-count = 2^a and p*2^a; line untouched; below-line odd non-turns: {dict(cnt)}; sporadic 0.')
say(f' first pairs {[n for n in kinds if kinds[n]=="pair"][:10]}; first near-turns {[n for n in kinds if kinds[n]=="near"][:10]}')
say(f' per dyadic block m=4..19  strand {sc[4:LOG-1]}')
say(f'                          pair   {pc[4:LOG-1]}')
say(f'                          near   {nc[4:LOG-1]}')

# ---------- across turn sets ----------
for T in [(), (3,), (5,), (7,), (3, 5, 7), (9,), (15,)]:
    u = tr.build(set(T), 1 << 18); _, k = read(u, 1 << 18, lambda n: n in T)
    assert 'sporadic' not in k.values()
say('Across builds (A for every B, C, {}, {3}, {5}, {7}, {3,5,7}, {9}, {15}): line u = 2n untouched, no sporadic point; '
    'proven for every turn set in ManyTurns.lean (line_never, no_sporadic, below_classify).')

open(__file__.replace('.py', '.txt'), 'w').write('\n'.join(out) + '\n')

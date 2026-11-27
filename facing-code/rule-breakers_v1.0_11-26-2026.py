# Rule-breakers (tUrUq, 11-26-2026): "find weird numbers that dont seem to play by anyones rules ... crowded near 0
# and then hugely and quickly thin out ... they will hug together with their even counterparts."
# Every rule found today is run over n <= N and each n where it breaks / needs a special case is recorded.
# Imports today's code for the pictures and the units; does not change it.
import importlib.util, math, random, sys, numpy as np
from collections import Counter, defaultdict
HERE = __file__.rsplit("/", 1)[0]
def load(name, tag):
    sp = importlib.util.spec_from_file_location(tag, f"{HERE}/{name}"); m = importlib.util.module_from_spec(sp)
    sp.loader.exec_module(m); return m
fpm = load("facing-prime-mining_v1.0_11-26-2026.py", "fpm")       # u(n) recursive (checked against the build there)
dual = load("dual-forms_v1.0_11-26-2026.py", "dual")              # r_top, t_top (R / T pictures)
spn = load("spine-two-digit-primes_v1.0_11-26-2026.py", "spn")    # spine(n)
sml = load("standard-mirror-line_v1.0_11-26-2026.py", "sml")      # block_mirror(n)

N = 10**6
out = []
def pr(*a): s = " ".join(str(x) for x in a); print(s); out.append(s)

# ---------- arrays ----------
M = N + 8
u = np.zeros(M, dtype=np.int64); u[1:4] = [1, 2, 3]
v = np.zeros(M, dtype=np.int64); v[1:3] = [1, 2]                  # pure halving: 3 = 1,2,1
for arr in (u, v):
    lo = 4 if arr is u else 3
    for n in range(lo, M):
        k = n >> 1
        arr[n] = 2 * arr[k] + (arr[k + 1] if n & 1 else 0)
for n in range(1, 3000): assert u[n] == fpm.u(n)
isP = np.ones(M, dtype=bool); isP[:2] = False
for i in range(2, int(M ** 0.5) + 1):
    if isP[i]: isP[i * i::i] = False
primes = np.nonzero(isP[:N + 1])[0]
pow2 = {1 << a for a in range(21)}; walls = {3 << a for a in range(20)}
def v2(x): return (x & -x).bit_length() - 1
def ispow2(x): return x > 0 and x & (x - 1) == 0

RULES = {}   # name -> (tier, provenance, statement, set of exceptions)
def rule(name, tier, prov, text, exc):
    RULES[name] = (tier, prov, text, {int(x) for x in exc if 1 <= x <= N})

n_all = np.arange(1, N + 1); odd = n_all[n_all % 2 == 1]

# 1 units word: 3 = 111 is where the recursion from 1,2 is replaced by the word (u and v split first at 3)
first_split = int(np.nonzero(u[1:N + 1] != v[1:N + 1])[0][0] + 1); assert first_split == 3
rule("units word root", "A", "[L]", "u(2k)=2u(k), u(2k+1)=2u(k)+u(k+1) from 1,2; 3 is set by the word 111", {1, 3})
# 2 self-count u = n
sc = n_all[u[1:N + 1] == n_all]; assert set(sc.tolist()) == {x for x in pow2 | walls if x <= N}
rule("self-count", "A", "[L]", "u(n) > n except at the self-count points", sc)
# 3 ratio-two line: odd n with u < 2n (strands + sporadic)
below = odd[u[odd] < 2 * odd]
strandP = {(1 << a) + 1 for a in range(1, 21)}; strandW = {(3 << a) + 1 for a in range(0, 20)}
spor = sorted(set(below.tolist()) - strandP - strandW); assert spor == [1, 11, 15], spor
assert not np.any(u[1:N + 1] == 2 * n_all)
rule("ratio-two line", "A", "[L]", "odd n has u(n) >= 2n except the strands 2^a+1, 3*2^a+1 and 1, 11, 15", below)
rule("ratio-two sporadic", "A", "[L]", "below the line only on a strand, except 1, 11, 15", spor)
dbl = n_all[u[1:N + 1] == 2 * (n_all - 1)]; assert dbl.tolist() == [2, 11, 15]
rule("counts n-1 twice", "A", "[C 1e6]", "u(n) = 2(n-1) is not met except at 2, 11, 15", dbl)
# 4 mod-4 law (odd and even sides)
m4o = odd[u[odd] % 4 != 0]
m4e = n_all[(n_all % 2 == 0) & (u[1:N + 1] % 4 == 2)]
assert set(m4e.tolist()) == {2} | {(1 << a) + 2 for a in range(2, 21) if (1 << a) + 2 <= N}
rule("mod-4 law (odd)", "A", "[L]", "odd n: 4 | u(n) except 1, 2^a+1 (u odd), 3*2^a+1 (u = 2 mod 4)", m4o)
rule("mod-4 law (even)", "A", "[L]", "even n: u(n) = 2 mod 4 only at 2 and 2^a+2 (the even halves of the lit strand doubled)", m4e)
# 5 step law d(2k)=d(k), d(2k+1)=4u(k)
d = 2 * u[:M - 1] - u[1:M]
ks = np.arange(1, N // 2)
bad = set((2 * ks[d[2 * ks] != d[ks]]).tolist()) | set((2 * ks[d[2 * ks + 1] != 4 * u[ks]] + 1).tolist())
assert bad == {2, 3}, sorted(bad)[:10]   # k = 1: d(2) != d(1) and d(3) != 4u(1)
rule("step law (k=1)", "A", "[L]", "d(2k)=d(k), d(2k+1)=4u(k) except k = 1 (n = 2, 3)", bad)
# 6 class by 8
k8 = np.arange(0, N // 8)
f8 = {1: 14 * u[k8] + u[k8 + 1], 3: 16 * u[k8] + 4 * u[k8 + 1], 5: 12 * u[k8] + 8 * u[k8 + 1], 7: 8 * u[k8] + 12 * u[k8 + 1]}
c8 = set()
for r, f in f8.items(): c8 |= set((8 * k8[u[8 * k8 + r] != f] + r).tolist())
rule("class by 8", "A", "[C 1e6]", "u(8k+r) by the four class formulas", c8)
# 7 pure halving v
vfix = n_all[v[1:N + 1] == n_all]; assert set(vfix.tolist()) == {x for x in pow2 if x <= N}
vbel = odd[v[odd] < 2 * odd]; vspor = sorted(set(vbel.tolist()) - strandP); assert vspor == [1, 7], vspor
rule("pure halving fixed", "A", "[L]", "v(n) > n except at 2^a (walls drop out when 3 = 1,2,1)", vfix)
rule("pure halving sporadic", "A", "[L]", "odd n below 2n in v only on 2^a+1, except 1, 7", vspor)
# 8 shared wings and same picture (computed from the imported pictures)
shw = [n for n in range(1, 20001) if dual.r_top(n)[0] == dual.t_top(n)[0]]
same = [n for n in range(1, 20001) if dual.r_top(n) == dual.t_top(n)]
rule("shared wings", "A", "[L n>=2]", "halving wing n//2 differs from the thirding wing", shw)
rule("same picture both mirrors", "A", "[C 2e4]", "R and T pictures differ", same)
# 9 prime faces: a prime above 3 has only k,k+1,k:2 (filled centre); 2 (hinge) and 3 (turn face) are the special cases
pf = [int(p) for p in primes if p % 2 == 0 or p % 3 == 0]
rule("prime face", "A", "[C 1e6]", "prime has one face k,k+1,k:2 with a filled centre", pf)
# 10 unified code w,c,w and picture rule b+(s-1)a: no break (checked), even hinge is the built-in special case
for n in range(2, 5000):
    a, b, _ = dual.r_top(n); assert dual.value(a, b, 2) == n
    a, b, _ = dual.t_top(n); assert dual.value(a, b, 3) == n
# 11 spine folds = v2(p-1)+1 for odd n
spx = [n for n in range(5, 200001, 2) if len(spn.spine(n)[0]) != v2(n - 1) + 1]
assert set(spx) <= strandP, spx[:10]
rule("spine folds", "A", "[C 2e5]", "odd n folds v2(n-1)+1 times; 2^a+1 ends on |3| one fold sooner", spx)
# 12 gap hand-off law and facing-keep law (consecutive primes)
P, Q = primes[:-1], primes[1:]
m, h = (P + Q) // 2, (Q - P) // 2
ok2 = ((m % 2 == 0) ^ (h % 2 == 0)); ok3 = ((m % 3 == 0) ^ (h % 3 == 0))
hand = set()
for i in np.nonzero(~(ok2 & ok3))[0]: hand |= {int(P[i]), int(Q[i])}
both5 = 0
for r in (5, 7, 11, 13): both5 += int(np.sum((m % r == 0) & (h % r == 0) & (h > 0)))
assert both5 == 0
keep = ((P % 6) == (Q % 6)); bad6 = np.nonzero(keep != ((Q - P) % 6 == 0))[0]
for i in bad6: hand |= {int(P[i]), int(Q[i])}
rule("gap hand-off", "A", "[C 1e6]", "one of m,h even; one a multiple of 3; facing kept iff 6 | gap", hand)
# 13 missing-wing strands (laid as strands, start m+(m-1)/2, step m) vs open = prime seat
W = N // 2
miss = np.zeros(W, dtype=bool)
for mm in range(3, 2 * int(W ** 0.5) + 3, 2):
    miss[mm + (mm - 1) // 2::mm] = True
openw = ~miss
mw = [2 * w + 1 for w in np.nonzero(openw != isP[2 * np.arange(W) + 1])[0]]; assert mw == [1]
rule("missing-wing strands", "A", "[C 1e6]", "open wing w <-> 2w+1 prime seat", mw)
# 14 imaginary side: even open wing <-> sum of two squares
s2 = np.zeros(M, dtype=bool)
for a in range(0, int(M ** 0.5) + 1):
    b = np.arange(a, int(math.isqrt(M - 1 - a * a)) + 1); s2[a * a + b * b] = True
ims = [int(p) for p in primes if s2[p] != (p % 2 == 1 and ((p - 1) // 2) % 2 == 0)]
assert ims == [2]
rule("imaginary side", "A", "[C 1e6]", "prime is two squares <-> its wing is even", ims)
# 15 even-prime seat law: E1 = {2p} equals {4w+2 : wing w open}
E1 = {2 * int(p) for p in primes if 2 * p <= N}
seat = {4 * w + 2 for w in np.nonzero(openw)[0] if 4 * w + 2 <= N}
sl = sorted(E1 ^ seat); assert sl == [2, 4]
rule("even-prime seat law", "A", "[C 1e6]", "2p is the E2 seat 4w+2 of an open wing", sl)
# 16 deep/shallow left-out axis
def leftout(x): return x > 2 and x % 2 == 0 and not (x % 4 == 2 and isP[x // 2]) and x != 4
dsx = set()
for p in primes[1:]:
    p = int(p); a, b = 2 * p - 2, 2 * p + 2
    if b > N: break
    good = leftout(a) and leftout(b) and sorted([v2(a), v2(b)])[0] == 2 and max(v2(a), v2(b)) >= 3
    if good:
        deep_left = v2(a) > v2(b)
        good = deep_left == (p % 4 == 1) and max(v2(a), v2(b)) == 1 + v2(p - 1 if deep_left else p + 1)
    if not good: dsx |= {2 * p, p}
rule("deep/shallow axis", "A", "[C 1e6]", "2p sits between a shallow (4*odd) and a deep left-out; deep side left iff p = 1 mod 4", dsx)
# 17 offset mirror swap n <-> O-n (primes <-> composites on [2, O-2])
OMAX = 20000
sw = [O for O in range(5, OMAX + 1) if np.all(isP[2:O - 1] != isP[O - 2:1:-1])]
assert sw == [11], sw
rule("offset swap", "A", "[C O<=2e4]", "n <-> O-n swaps primes and composites on [2,O-2] for no offset except 11", sw)
pi = np.cumsum(isP[:N + 1]); xs = np.arange(2, N + 1)
bal = xs[pi[2:N + 1] == (xs - 1) - pi[2:N + 1]].tolist(); assert bal == [9, 11, 13], bal
rule("prime/composite balance", "A", "[C 1e6]", "primes and composites on [2,x] unequal except x = 9, 11, 13", bal)
# 18 decimal mirrors below the line
dm = [n for n in range(10, N + 1) if str(n) == str(n)[::-1] and u[n] < 2 * n]
rule("decimal mirrors below line", "A", "[C 1e6]", "two-digit-plus palindromes sit above u = 2n except these", dm)
# 19 3,5,7 picture: three primes stepping by 2
t357 = [int(p) for p in primes if p + 4 <= N and isP[p + 2] and isP[p + 4]]; assert t357 == [3]
rule("3,5,7 run", "A", "[C 1e6]", "p, p+2, p+4 are not all prime except 3", [3, 5, 7])
# 20 gap-4 balance D = u(m-2)+u(m+2)-2u(m) = 0 <-> m = 5 mod 8 (m >= 21)
mo = np.arange(3, N - 2, 2); D = u[mo - 2] + u[mo + 2] - 2 * u[mo]
g4 = sorted(set(mo[(D == 0) != (mo % 8 == 5)].tolist()))
rule("gap-4 balance", "A", "[C 1e6]", "odd m: D = 0 iff m = 5 mod 8, except these", g4)
# 21 E2 even primes: consecutive E2 gap 4 (2 excluded); first E2 not 2p (18); first double factoring (36)
rule("E2 split points (first)", "A", "[C]", "E2 = 2p, first split 18; first double factoring 36", [18, 36])
# ---- tier B (dense: thin like sqrt or like n/log^2, kept apart) ----
psq = [int(p) * int(p) for p in primes if p * p <= N]
rule("mirror walk break (prime squares)", "B", "[C 1e6]", "walk with mirrors below q names primes up to q^2", psq)
tw = [int(p) for p in primes[1:] if p + 2 <= N and isP[p + 2]]
rule("broken side absent (twin lower)", "B", "[C 1e6]", "p+2 is a missing seat (the left side is broken) except twin lower primes", tw)

# ---------- score ----------
score = Counter(); which = defaultdict(list)
for name, (tier, prov, text, exc) in RULES.items():
    if tier != "A": continue
    for x in exc: score[x] += 1; which[x].append(name)
S = set(score)
def family(n):
    if n == 1: return "unit 1"
    if ispow2(n): return "power of 2"
    if n in walls: return "wall 3*2^a"
    if isP[n]: return "prime"
    if n % 2 == 1: return "odd composite"
    if n % 4 == 2 and isP[n // 2]: return "even prime 2p"
    if n % 4 == 2: return "E2-only (2 mod 4)"
    return "left-out 4k"
def strand(n):
    if n in strandP: return "2^a+1"
    if n in strandW: return "3*2^a+1"
    if n - 2 in pow2 and n % 2 == 0 and n > 4: return "2^a+2"
    return ""

pr("RULE-BREAKERS v1.0 11-26-2026  (n <= 1,000,000; tier A rules scored, tier B listed apart)")
pr("\n== CATALOGUE (rule, provenance, exceptions to 1e6: count and first ones) ==")
for name, (tier, prov, text, exc) in RULES.items():
    e = sorted(exc); pr(f"[{tier}] {name} {prov}: {text}\n      {len(e)} exceptions: {e[:24]}{' ...' if len(e) > 24 else ''}")
pr("No exceptions found (not scored): unified code w,c,w (bottom holds n units, n<200, earlier script); picture rule b+(s-1)a")
pr("  (n<5000; the even hinge b=a is its built-in special case); imbalance u=n+imb [L]; R/T forms read n (n<3000);")
pr("  mirror at the walker R1 (78495/78495 gaps from p=5; 2,3 outside its range); E2 gap 4 from 6 on.")
pr("Not sparse (left out of the score): centre tell (first allowed h right 46-89%), left-out window LW(L) (misses 18-64%).")

pr("\n== RANKED (tier A score >= 2) ==")
rank = sorted(S, key=lambda x: (-score[x], x))
for x in rank:
    if score[x] < 2: break
    pr(f"{x:7d} score {score[x]:2d}  {family(x):18s} {strand(x):8s} {', '.join(which[x])}")
pr("score-1 numbers:", len([x for x in S if score[x] == 1]), "first:", sorted(x for x in S if score[x] == 1)[:30])

pr("\n== THINNING (count of rule-breakers per range; sum of scores) ==")
edges = [1, 10, 100, 1000, 10**4, 10**5, 10**6]
rows = []
for i in range(len(edges) - 1):
    lo = 1 if i == 0 else edges[i] + 1; hi = edges[i + 1] if i else 10
    lo, hi = (1, 10) if i == 0 else (edges[i] + 1, edges[i + 1])
    c = [x for x in S if lo <= x <= hi]; sc_ = sum(score[x] for x in c)
    c2 = len([x for x in c if score[x] >= 2])
    rows.append((lo, hi, len(c), sc_, c2)); pr(f"  {lo:>7d}-{hi:<8d} breakers {len(c):4d}  score sum {sc_:4d}  score>=2 {c2:3d}  share of range {len(c)/(hi-lo+1):.6f}")
# fit: cumulative count C(x) = a + b*log2(x) (plain least squares)
xsf = [2 ** j for j in range(1, 20)]; Sarr = np.array(sorted(S))
C = np.array([np.searchsorted(Sarr, x, side="right") for x in xsf]); L2 = np.log2(xsf)
b, a = np.polyfit(L2, C, 1); res = C - (a + b * L2)
pr(f"  fit C(x) = {a:.3f} + {b:.4f}*log2(x), max |residual| {np.max(np.abs(res)):.2f} (x = 2..2^19); C(2^19) = {C[-1]}")
pr("  tier B for contrast:", {k: [len([x for x in RULES[k][3] if lo <= x <= hi]) for lo, hi, *_ in rows] for k in RULES if RULES[k][0] == "B"})

pr("\n== HUGGING (partners that are also breakers) vs random numbers of the same size ==")
def partners(n):
    p = {"2n": 2 * n, "n-1": n - 1, "n+1": n + 1, "block mirror": sml.block_mirror(n)}
    if n % 2 == 0: p["n/2"] = n // 2
    if n < 11: p["11-n"] = 11 - n
    return {k: x for k, x in p.items() if 1 <= x <= N and x != n}
def rates(pop, Sset):
    tot = Counter(); hit = Counter(); anyh = 0
    for n in pop:
        ps = partners(n); got = False
        for k, x in ps.items():
            tot[k] += 1
            if x in Sset: hit[k] += 1; got = True
        anyh += got
    return anyh / len(pop), {k: hit[k] / tot[k] for k in tot}
br = sorted(S); ra, rk = rates(br, S)
random.seed(1729); rnd = [random.randint(max(1, n // 2), max(2, 2 * n)) for n in br for _ in range(200)]
ba, bk = rates(rnd, S)
pr(f"  breakers with at least one breaker partner: {ra:.4f}   random same-size: {ba:.4f}")
for k in rk: pr(f"    {k:13s} breakers {rk[k]:.4f}   random {bk.get(k, 0):.4f}")
# even counterpart for odd breakers: the even neighbour that halves cleanly
oddb = [n for n in br if n % 2 == 1 and n > 1]
evn = [n for n in oddb if (n - 1) in S or (n + 1) in S]
pr(f"  odd breakers > 1: {len(oddb)}; with an even breaker beside them: {len(evn)}; without: {sorted(set(oddb) - set(evn))[:20]}")

pr("\n== FAMILIES ==")
fam = Counter(family(x) for x in S); fs = Counter();
for x in S: fs[family(x)] += score[x]
for f, c in fam.most_common(): pr(f"  {f:18s} breakers {c:4d}  score sum {fs[f]:4d}")
pr("  relativity (same number, rule it breaks vs rule it fits):")
fits = {"ratio-two line": lambda n: n % 2 == 1 and n not in RULES["ratio-two line"][3],
        "mod-4 law (odd)": lambda n: n % 2 == 1 and n not in RULES["mod-4 law (odd)"][3],
        "pure halving sporadic": lambda n: n % 2 == 1 and n not in RULES["pure halving sporadic"][3],
        "self-count": lambda n: n not in RULES["self-count"][3]}
for x in (1, 2, 3, 5, 7, 11, 15, 17, 18, 25, 36, 121, 257, 65537):
    f = [k for k, t in fits.items() if t(x)]
    pr(f"    {x:6d} {family(x):16s} breaks: {', '.join(which.get(x, [])) or '-'}   fits: {', '.join(f) or '-'}")

pr("\n== STRONGEST ODDITY: sporadic breakers (off every strand, not a power or wall) ==")
spor_all = [x for x in br if not strand(x) and not ispow2(x) and x not in walls]
pr("  ", [(x, score[x]) for x in spor_all])
for x in spor_all:
    pr(f"   {x:7d} {family(x):16s} u={int(u[x])} u/n={u[x]/x:.4f} neighbours: {x-1}:{'B' if x-1 in S else '.'} {x+1}:{'B' if x+1 in S else '.'} 2n:{'B' if 2*x in S else '.'}  rules: {', '.join(which[x])}")

pr("\n== HUGGING away from 0 (breakers > 100 only, so small-number crowding does not lift the baseline) ==")
big = [n for n in br if n > 100]; ra2, rk2 = rates(big, S)
rnd2 = [random.randint(n // 2, 2 * n) for n in big for _ in range(200)]; ba2, bk2 = rates(rnd2, S)
pr(f"  {len(big)} breakers > 100: with a breaker partner {ra2:.4f}   random same-size {ba2:.6f}")
for k in rk2: pr(f"    {k:13s} breakers {rk2[k]:.4f}   random {bk2.get(k, 0):.6f}")
pr("  note: n+-1 and 2n hugging is partly built in (a strand is an anchor + 1; anchors double into anchors).")

pr("\n== FOLLOW: the even counterparts of the below-line odds ==")
ev = n_all[(n_all % 2 == 0) & (u[1:N + 1] < 2 * n_all)]
core = lambda x: x >> v2(x)
assert all(u[core(x)] < 2 * core(x) for x in ev.tolist())          # an even is below the line iff its odd core is
pr(f"  evens below u = 2n to 1e6: {len(ev)}; every one has its odd core below the line (asserted)")
for c in (11, 15, 1, 7):
    pr(f"  core {c:2d}: doublings below the line {[c << j for j in range(1, 7)]}  u/n = {u[c]}/{c}" + ("" if c > 1 else "  (2^a are self-count)"))
dec_cores = Counter(core(x) for x in dm)
pr(f"  decimal mirrors below the line by odd core: {dict(dec_cores)}  (11, 33 = 2^5+1, 17 = 2^4+1, 33*64 = 2112)")
pr("  11 and 15 are the only odd cores below the line that sit off both strands; 11 = 5,6,5 (wall 6 inside) and 15 = 7,8,7 (power 8 inside).")
pr(f"  11's even neighbours 10 (2*5, 5 = 2^2+1) and 12 (wall) are both breakers; 15's are 14 (fits) and 16 (power).")

assert score[1] >= 6 and score[3] >= 5 and 11 in S and 15 in S and 7 in S
assert RULES["offset swap"][3] == {11} and RULES["prime/composite balance"][3] == {9, 11, 13}
open(f"{HERE}/rule-breakers_v1.0_11-26-2026.txt", "w").write("\n".join(out) + "\n")

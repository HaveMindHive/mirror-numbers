# PySR on the mirror build (tUrUq, 11-26-2026). Exploration: what fits, what frays.
# Stage 1 (numpy answer key, exact counts) always runs; stage 2 runs PySR one job at a time:  python pysr-mirrors... pysr
import sys, os, shutil
from fractions import Fraction as F
from collections import Counter
import numpy as np
from sympy import isprime, primerange

HERE = os.path.dirname(os.path.abspath(__file__))
N = 10 ** 7
spf = np.zeros(N // 2 + 2, dtype=np.int32)            # smallest prime factor up to N/2+1 (centres)
for r in range(2, int(len(spf) ** 0.5) + 1):
    if spf[r] == 0:
        blk = spf[r * r::r]; blk[blk == 0] = r
spf[spf == 0] = np.arange(len(spf))[spf == 0]           # 0 -> itself (primes)
prime_key = np.ones(N + 1, bool); prime_key[:2] = False
for r in range(2, int(N ** 0.5) + 1):
    if prime_key[r]: prime_key[r * r::r] = False
P = np.nonzero(prime_key)[0]
P5 = P[P >= 5]

def law(q):
    """f(q) = (1/(q-1)) * prod_{r<q prime} (1 - 1/(r-1)), r = 2 term read as 1/2 (p mod 4 has two faces)."""
    if q == 2: return F(1, 2)
    out = F(1, 2) / (q - 1)
    for r in primerange(3, q): out *= F(r - 2, r - 1)
    return out

def shares(c):
    """Count of first mirror q of the centre c (q = spf(c) if c composite, else 'prime')."""
    s = spf[c]; isp = s == c
    cnt = Counter({int(k): int(v) for k, v in zip(*np.unique(s[~isp], return_counts=True))})
    return cnt, int(isp.sum())

def u_array(n):
    u = np.zeros(n + 2, dtype=np.int64); u[1:4] = [1, 2, 3]
    lo = 4
    while lo <= n + 1:                                   # block [lo, 2lo) from [lo/2, lo]
        hi = min(2 * lo, n + 2); m = np.arange(lo, hi); k = m // 2
        u[lo] = 2 * u[lo // 2]                           # lo is even; odd m = 2lo-1 needs u[lo]
        u[m] = np.where(m % 2 == 0, 2 * u[k], 2 * u[k] + u[k + 1]); lo = hi
    return u

def chain_len(q):
    L = 1
    while True:
        q = 2 * q - 1
        if not (prime_key[q] if q <= N else isprime(int(q))): return L
        L += 1

if __name__ == "__main__":
    out = []; pr = lambda *a: (print(*a), out.append(" ".join(map(str, a))))
    # ---- Target 1: first mirror of the centre
    for name, c in (("(p+1)/2", (P5 + 1) // 2), ("(p-1)/2", (P5 - 1) // 2)):
        cnt, cprime = shares(c); T = len(c)
        if name == "(p+1)/2":
            cs, cp = shares((P5[P5 < 10 ** 6] + 1) // 2)
            assert [cs[q] for q in (2, 3, 5, 7, 11, 13, 17, 19, 23)] == [39321, 19610, 4868, 2478, 1237, 922, 625, 543, 397] and cp == 4299
            T1 = [(q, cnt[q]) for q in primerange(2, 102)]
        pr(f"\nTarget 1, centre {name}, primes 5..1e7 ({T} primes); centre prime: {cprime} = {cprime / T:.6f}")
        pr(" q   count    share       law f(q)         share/law   z")
        for q in primerange(2, 102):
            f = law(q); e = T * float(f); z = (cnt[q] - e) / (e * (1 - float(f))) ** 0.5
            pr(f"{q:3d} {cnt[q]:7d}  {cnt[q] / T:.7f}  {str(f):>14s}  {cnt[q] / e:.5f}  {z:+.2f}")
    assert law(5) == F(1, 16) and law(7) == F(1, 32) and law(11) == F(1, 64) and law(13) == F(3, 256)
    # ---- Target 2: operator chains q -> 2q-1
    allL = Counter(chain_len(int(q)) for q in P)                       # every prime, its upward run
    startL = Counter(chain_len(int(q)) for q in P if not (q > 2 and (q + 1) % 2 == 0 and prime_key[(q + 1) // 2]) or q == 2)
    pr("\nTarget 2, operator chains q -> 2q-1, q <= 1e7")
    pr(" L  N_all(L)  ratio  | N_start(L)  ratio")
    for L in sorted(allL):
        ra = allL[L] / allL[L - 1] if L - 1 in allL else float("nan")
        rs = startL[L] / startL[L - 1] if startL.get(L - 1) else float("nan")
        pr(f"{L:2d} {allL[L]:8d}  {ra:.4f} | {startL[L]:8d}  {rs:.4f}")
    Ls = np.array(sorted(allL)); fit = np.polyfit(Ls[:-2], np.log(np.array([allL[L] for L in Ls[:-2]])), 1)
    pr(f"plain fit log N_all = {fit[1]:.4f} {fit[0]:+.4f} L -> ratio {np.exp(fit[0]):.4f}/step (L<= {Ls[-3]})")
    # ---- Target 3: unit count u(p)/p
    u = u_array(N)
    from functools import lru_cache
    ur = lru_cache(None)(lambda n: n if n <= 3 else 2 * ur(n // 2) + (0 if n % 2 == 0 else ur(n // 2 + 1)))
    assert all(u[n] == ur(n) for n in range(1, 5000))
    ratio = u[P5] / P5; qq = spf[(P5 + 1) // 2]; qq = np.where(qq == (P5 + 1) // 2, 0, qq)
    pr("\nTarget 3, u(p)/p for primes 5..1e7: overall mean %.5f" % ratio.mean())
    pr(" by first mirror q of (p+1)/2 (0 = centre prime): q  n  mean  std")
    T3 = []
    for q in [0] + list(primerange(2, 50)):
        m = ratio[qq == q]; T3.append((q, m.mean())); pr(f"  {q:3d} {len(m):7d} {m.mean():.5f} {m.std():.5f}")
    cl = np.array([chain_len(int(p)) for p in P5])
    pr(" by chain length L:")
    for L in sorted(set(cl)): m = ratio[cl == L]; pr(f"  L={L} {len(m):7d} {m.mean():.5f} {m.std():.5f}")
    nn = np.arange(N + 1); nn[0] = 1; key = np.floor(np.log2(nn)).astype(int) * 8 + nn % 8
    ref = np.bincount(key[1:], weights=u[1:N + 1] / nn[1:]) / np.maximum(np.bincount(key[1:]), 1)
    zr = ratio / ref[key[P5]]                            # u(p)/p over the mean of u(n)/n, same dyadic block and n mod 8
    pr(" normalised (size + mod 8):", {int(q): round(float(zr[qq == q].mean()), 4) for q in (0, 2, 3, 5, 7, 11, 13)},
       {f"L={L}": f"{zr[cl == L].mean():.4f}+-{zr[cl == L].std() / (cl == L).sum() ** .5:.4f}" for L in sorted(set(cl))})
    # p mod 4 / mod 8 split (q = 2 means p = 3 mod 4)
    pr(" by p mod 8:", {int(r): round(float(ratio[P5 % 8 == r].mean()), 5) for r in (1, 3, 5, 7)})
    pr(" all odd n <= 1e7 by n mod 8:", {r: round(float((u[np.arange(r, N, 8)] / np.arange(r, N, 8)).mean()), 5) for r in (1, 3, 5, 7)})
    open(os.path.join(HERE, "pysr-mirrors-table_v1.0_11-26-2026.txt"), "w").write("\n".join(out) + "\n")
    # ---- Target 4 (oddity): exact mod-8 law of u, and the dyadic block sum
    # u(8k+1) = 14u(k)+u(k+1); u(8k+3) = 16u(k)+4u(k+1); u(8k+5) = 12u(k)+8u(k+1); u(8k+7) = 8u(k)+12u(k+1)
    ks = np.arange(2, N // 8 - 1)                       # k >= 2 (leaf 3 = 1,1,1 breaks k = 1)
    for r, (x, y) in {1: (14, 1), 3: (16, 4), 5: (12, 8), 7: (8, 12)}.items():
        assert (u[8 * ks + r] == x * u[ks] + y * u[ks + 1]).all()
    for a in range(4, 23):
        n8 = np.arange(2 ** a, min(2 ** (a + 1), N + 1)); S = {r: int(u[n8[n8 % 8 == r]].sum()) for r in (1, 3, 5, 7)}
        if n8[-1] < 2 ** (a + 1) - 1: break
        K = 2 ** (a - 3)
        assert S[5] - S[3] == S[7] - S[5] == 4 * K and 4 * S[1] == 3 * S[3] - 8 * K
    Sblk = [int(u[2 ** a:2 ** (a + 1)].sum()) for a in range(1, 23)]
    assert all(15 * s == 17 * 5 ** a - 5 * 2 ** a for a, s in zip(range(1, 23), Sblk))
    pr("\nTarget 4: odd classes mod 8 carry weights (14,1),(16,4),(12,8),(8,12) on (u(k),u(k+1)): totals 15,20,20,20.")
    pr("  per dyadic block [2^a,2^(a+1)): S5-S3 = S7-S5 = 2^(a-1), 4*S1 = 3*S3 - 2^a (asserted a=4..22)")
    pr("  block sum S(a) = (17*5^a - 5*2^a)/15, a>=1 (asserted to a=22):", Sblk[:8])
    pr("  so mean u(p)/p, p=1 mod 8 : others -> 3/4 ; q odd : q=2 -> 7/8. Size-and-class normalised u(p)/p is flat in q and L (see notes).")
    open(os.path.join(HERE, "pysr-mirrors-table_v1.0_11-26-2026.txt"), "w").write("\n".join(out) + "\n")

    if "pysr" in sys.argv:
        from pysr import PySRRegressor
        def run(tag, X, y, names, w=None, **kw):
            mdl = PySRRegressor(niterations=40, timeout_in_seconds=120, populations=15, maxsize=20,
                                binary_operators=["+", "-", "*", "/"], unary_operators=kw.pop("un", []),
                                output_directory=os.path.join(HERE, "pysr-runs"), run_id=tag, progress=False,
                                verbosity=0, random_state=0, deterministic=True, parallelism="serial", **kw)
            mdl.fit(X, y, weights=w, variable_names=names)
            shutil.copy(os.path.join(HERE, "pysr-runs", tag, "hall_of_fame.csv"), os.path.join(HERE, f"pysr-hof-{tag}_v1.0_11-26-2026.csv"))
            pr(f"\nPySR {tag}:"); pr(mdl.equations_[["complexity", "loss", "equation"]].to_string())
        qs = np.array([t[0] for t in T1 if t[0] >= 3], float); fobs = np.array([t[1] for t in T1 if t[0] >= 3]) / len(P5)
        Pq = np.array([float(law(int(q)) * (q - 1)) for q in qs])   # running product, r=2 term 1/2
        run("first-mirror", np.c_[qs, 1 / (qs - 1), Pq], fobs, ["q", "iq", "Pq"], w=1 / fobs ** 2)
        run("chains", Ls[:, None].astype(float), np.log(np.array([allL[L] for L in Ls], float)), ["L"],
            w=np.array([allL[L] for L in Ls], float), un=["exp"])
        run("block-sum", np.arange(1, 13, dtype=float)[:, None], np.array(Sblk[:12], float), ["a"],
            w=1 / np.array(Sblk[:12], float) ** 2)
        open(os.path.join(HERE, "pysr-mirrors-table_v1.0_11-26-2026.txt"), "w").write("\n".join(out) + "\n")

# PySR on the even primes (tUrUq, 11-26-2026): make them and break them in his system.
# E1 = 2p (p odd prime: the prime places on the even line, 2 = the unit of the evens).
# E2 = prime inside the evens = 2 mod 4, n != 2 (not a product of two evens).
# E3 = even mirrors of odd primes under offset 11, per block: n <-> (2j+1)*11 - n (standard-mirror-line block_mirror).
# Places on the even line: n = 2k <-> k, and the even product on places is a (x) b = 2ab (1 (x) 1 = 2, his 1x1 = 2).
# Stage 1 (exact integer work, asserts) always runs. Stage 2 (PySR, one short fit at a time) runs with arg "pysr".
import sys, os, math, shutil, subprocess, time, importlib.util
from fractions import Fraction as F
from functools import lru_cache
from collections import Counter
import numpy as np
from sympy import divisors, divisor_count, isprime

HERE = os.path.dirname(os.path.abspath(__file__))
def load(name):
    spec = importlib.util.spec_from_file_location(name.replace("-", "_"), os.path.join(HERE, name + ".py"))
    mod = importlib.util.module_from_spec(spec); spec.loader.exec_module(mod); return mod
EP = load("even-primes_v1.0_11-26-2026")          # even_world_prime, even_world_factorings, even_mirrors
MW = load("missing-wings_v1.0_11-26-2026")        # lay_strands
SM = load("standard-mirror-line_v1.0_11-26-2026") # block_mirror
UC = load("unified-code_v1.0_11-26-2026")         # write

W = 10 ** 6                       # wings to 1e6 -> E2 numbers n = 4w + 2 up to 4,000,002
hits = MW.lay_strands(W)          # strands landing on wing w (missing-wing construction)
N = 4 * W + 2
prime_key = np.ones(N + 1, bool); prime_key[:2] = False
for r in range(2, int(N ** 0.5) + 1):
    if prime_key[r]: prime_key[r * r::r] = False

def E2(n): return n % 4 == 2 and n != 2
def E1(n): return n % 2 == 0 and n > 4 and bool(prime_key[n // 2])
def seat(n): return (n - 2) // 4               # E2 number n -> wing w of its odd half m = n/2 = 2w + 1

@lru_cache(None)
def ways(m, k, lo):
    """Multisets of k odd factors >= lo (nondecreasing) with product m."""
    if k == 0: return int(m == 1)
    if k == 1: return int(m >= lo)
    return sum(ways(m // d, k - 1, d) for d in divisors(m) if d >= lo and d ** k <= m)

def split(n):
    k = 0
    while n % 2 == 0: n //= 2; k += 1
    return k, n
def f2(n):  # factorings into E2 primes WITH 2 counted (2 = 2*1): the (x) rule on places
    k, m = split(n); return ways(m, k, 1) if k else 0
def f0(n):  # factorings into E2 primes WITHOUT 2 (2 read as the unit of the evens)
    k, m = split(n); return ways(m, k, 3) if k else 0
def h(m): return int(divisor_count(m)) - 2      # strand hits on the wing of odd m >= 3 (asserted below)
def sq(m): return int(math.isqrt(m) ** 2 == m)
def stirling2(n, k):
    return sum((-1) ** (k - j) * math.comb(k, j) * j ** n for j in range(k + 1)) // math.factorial(k)

out = []
def pr(*a): s = " ".join(map(str, a)); print(s); out.append(s)

if __name__ == "__main__":
    # ---------- MAKE 0: the seat law. Every wing w is an E2 number 4w+2; E1 = the open seats.
    assert all(EP.even_world_prime(n) == E2(n) for n in range(2, 400))
    assert all(hits[w] == min(h(2 * w + 1), 255) for w in range(1, 30001))
    e1_open = all((hits[w] == 0) == bool(prime_key[2 * w + 1]) for w in range(1, W + 1))
    assert e1_open
    pr("MAKE 0. Seat law: E2 numbers are n = 4w+2 (w >= 1), one per wing; n is E1 exactly when wing w is open")
    pr("  (no strand lands on it). Checked every wing w <= 1,000,000 (n <= 4,000,002). Strand hits on wing w = tau(2w+1) - 2.")
    pr("  E2\\E1 = the missing seats, carrying h >= 1 strand hits: " +
       ", ".join(f"{4*w+2}(h{hits[w]})" for w in range(1, 40) if hits[w]))

    # ---------- MAKE 1: f(n), the number of E2 factorings
    for n in range(4, 301, 2):
        assert f2(n) == len(EP.even_world_factorings(n)), n
    for m in range(3, 250001, 2):
        k4 = 4 * m
        if m < 60001: assert f0(k4) == (h(m) + sq(m)) // 2 and (h(m) + sq(m)) % 2 == 0 and f2(k4) == f0(k4) + 1, m
    pr("\nMAKE 1. Depth 2 (n = 4m, m odd >= 3): f0(n) = (h + s)/2, f2(n) = f0(n) + 1, h = strand hits on m's wing,")
    pr("  s = 1 if m is a square. Exact for m < 60,001 (asserted); proven by pairing divisors d <-> m/d.")
    pr("  Same fact reached by a different route in the divisor-pair count of the standard line.")
    primes_odd = [3, 5, 7, 11, 13, 17]
    for om in range(1, 6):
        m = math.prod(primes_odd[:om])
        assert h(m) + 2 == 2 ** om
        for k in range(1, 6):
            n = 2 ** k * m
            assert f0(n) == stirling2(om, k) and f2(n) == sum(stirling2(om, j) for j in range(1, k + 1)), (om, k)
    pr("  Squarefree core with w odd primes (h + 2 = 2^w): depth k gives f0 = S(w,k), f2 = S(w,1)+...+S(w,k)")
    pr("  (asserted w <= 5, k <= 5; same fact reached by a different route: Stirling's set-partition numbers).")
    pr("  e.g. core 3*5*7 = 105 (h = 6): f0 at depth 1..5 =", [f0(2 ** k * 105) for k in range(1, 6)],
       " f2 =", [f2(2 ** k * 105) for k in range(1, 6)])
    firsts0, firsts2 = {}, {}
    for n in range(4, 200001, 2):
        a, b = f0(n), f2(n)
        firsts0.setdefault(a, n); firsts2.setdefault(b, n)
    pr("  first n with f0 = j (no 2):", {j: firsts0[j] for j in sorted(firsts0) if j <= 8})
    pr("  first n with f2 = j (2 counted):", {j: firsts2[j] for j in sorted(firsts2) if j <= 8})
    assert firsts2[2] == 36 and firsts0[2] == 180

    # ---------- MAKE 2: what an E2-but-not-E1 number carries
    for n in range(6, 200001, 4):
        m = n // 2
        assert (f2(2 * n) >= 2) == (not E1(n)) and f2(2 * n) == (h(m) + 2 + sq(m)) // 2
    pr("\nMAKE 2. For E2 n = 2m: f2(2n) = (h + 2 + s)/2, so 2n splits two or more ways exactly when n is E2 but not E1")
    pr("  (asserted n < 200,000). 18 -> 36 = 2x18 = 6x6; 30 -> 60 = 2x30 = 6x10; E1 22 -> 44 = 2x22 only.")
    pr("  In the unified code n = w,c,w the E2 numbers are the ones with exactly one hinge 0 before an odd centre:",
       UC.write(18, 1), UC.write(22, 1), "; E1 vs E2\\E1 is not visible there (the core's wing, one level down).")
    # imbalance u - n does not carry it
    @lru_cache(None)
    def u(n): return n if n <= 3 else 2 * u(n // 2) + (0 if n % 2 == 0 else u(n // 2 + 1))
    assert all(u(2 * k) == 2 * u(k) for k in range(2, 5000))
    rr = {True: [], False: []}
    for m in range(2 ** 16 + 1, 2 ** 17, 2): rr[bool(prime_key[m])].append((u(2 * m) - 2 * m) / (2 * m))
    pr("  Imbalance (u-n)/n in [2^17, 2^18), E1 mean %.5f range [%.4f, %.4f]; E2\\E1 mean %.5f range [%.4f, %.4f]: overlapping, no tell."
       % (np.mean(rr[True]), min(rr[True]), max(rr[True]), np.mean(rr[False]), min(rr[False]), max(rr[False])))

    # ---------- MAKE 3: densities and gaps
    for X in (10, 100, 12345, 10 ** 6):
        assert sum(1 for n in range(1, X + 1) if E2(n)) == (X + 2) // 4 - 1
    pr("\nMAKE 3. Count of E2 <= X = floor((X+2)/4) - 1 (asserted X = 10, 100, 12345, 1e6): a fixed quarter, they never thin.")
    E1s = [n for n in range(6, N + 1, 4) if prime_key[n // 2]]
    g = np.diff(E1s)
    assert (g % 4 == 0).all()
    pr(f"  E1 to {N}: {len(E1s)}. E1 gaps are multiples of 4 (proven: odd primes differ by an even number), so")
    pr("  E1 gaps in E2 steps = half the prime gaps:", [int(x) for x in g[:20] // 4])
    share, gapmean = [], []
    pr("  dyadic block a: [2^a, 2^(a+1)), E2 count, E1 count, E1/E2 share, mean E1 gap in E2 steps")
    arr = np.array(E1s)
    for a in range(4, 21):
        lo, hi = 2 ** a, 2 ** (a + 1)
        ne2 = (hi - 1 + 2) // 4 - (lo - 1 + 2) // 4
        sel = arr[(arr >= lo) & (arr < hi)]
        ne1 = len(sel); gm = float(np.diff(sel).mean() / 4)
        share.append((a, F(ne1, ne2))); gapmean.append((a, gm))
        pr(f"   a={a:2d}  E2 {ne2:7d}  E1 {ne1:6d}  share {ne1/ne2:.6f}  gap {gm:.4f}")

    # ---------- BREAK 1: depth-2 law at depth 3
    seen, brk = {}, None
    for m in range(3, 20001, 2):
        key = (h(m), sq(m)); v = f0(8 * m)
        if key in seen and seen[key][1] != v: brk = (seen[key], (m, v), key); break
        seen.setdefault(key, (m, v))
    pr(f"\nBREAK 1. At depth 3 (n = 8m) f0 is no longer a function of (h, s): first clash m = {brk[0][0]} (f0 {brk[0][1]})")
    pr(f"  vs m = {brk[1][0]} (f0 {brk[1][1]}), same h = {brk[2][0]}, s = {brk[2][1]}: n = {8*brk[0][0]} vs {8*brk[1][0]}.")
    pr("  The count needs the core's full build (the exponents), not its strand-hit total. Depth 2 m = 1 (n = 4): f0 = 0, f2 = 1 (2x2).")

    # ---------- BREAK 2: the splits
    splits = [n for n in range(6, 400, 4) if not E1(n)]
    pr("\nBREAK 2. E1 and E2 split at (E2 not E1, n < 400):", splits[:30])
    pr("  What changes at each split: the core m = n/2 gains strand hits h = tau(m) - 2 >= 1, and 2n gains (h + s)/2 extra factorings.")
    pr("  by kind:", ", ".join(f"{n}=2x{n//2}(h{h(n//2)},+{(h(n//2)+sq(n//2))//2})" for n in splits[:14]))
    assert [next(n for n in splits if h(n // 2) == t) for t in (1, 2, 4)] == [18, 30, 90]
    pr("  First split with h = 1 (core p^2): 18; h = 2 (core pq): 30; h = 4: 90 (core 45 = 3^2*5) -> 180 is also the first double with 2 left out.")

    # ---------- BREAK 3: make E2 factor like the odd primes
    odot = lambda a, b: a * b // 2
    ev = list(range(2, 2001, 2))
    assert all(odot(2, n) == n for n in ev) and odot(2, 2) == 2
    irr = [n for n in range(4, 2001, 2) if not any((2 * n) % a == 0 and (2 * n // a) % 2 == 0 and 2 * n // a > 2
                                                    for a in range(4, n, 2))]
    assert irr == [n for n in range(4, 2001, 2) if isprime(n // 2)]
    @lru_cache(None)
    def odfact(n, lo):  # factorings under a (.) b = ab/2 into (.)-primes >= lo
        if n == 2: return 1
        return sum(odfact(2 * n // p, p) for p in irr if p >= lo and p <= n and (2 * n) % p == 0 and (2 * n // p) % 2 == 0)
    assert all(odfact(n, 4) == 1 for n in range(4, 1001, 2))
    reach = [n for n in range(4, 401, 2) if split(n)[0] >= sum(e for _, e in __import__("sympy").factorint(split(n)[1]).items())]
    unreach = [n for n in range(4, 401, 2) if n not in reach]
    pr("\nBREAK 3. Making the even primes factor like odd primes:")
    pr("  (i) 2 as the unit, a (.) b = ab/2 (on places a (x) b = ab, the doubling removed): 2 (.) n = n; the (.)-primes are")
    pr("      exactly E1 = 2p (asserted n <= 2000) and every even 4..1000 factors in exactly one way. E2 collapses to E1.")
    pr("      Cost: 2 (.) 2 = 2, not 4; his 1u x 1u = 2u is gone.")
    pr("  (ii) keep a (x) b = 2ab but adjoin the odd 1 as unit: still 36 = 2x18 = 6x6 (unit adds nothing; the unit of (x) on places is 1/2 = n 1, odd).")
    pr("  (iii) keep 2ab but allow only E1 and 2 as letters: factoring is unique where it exists, but", len(unreach),
       "of the 199 evens 4..400 cannot be written; first:", unreach[:12])
    pr("  So: unique factoring comes back only when the doubling in 1 (x) 1 = 2 is taken out, and then the E2-only primes vanish.")

    # ---------- E3: offset-11 mirrors of odd primes
    rows = Counter(); first_split = None; law_ok = True
    for p in range(3, 100001, 2):
        if not prime_key[p] or p == 11: continue
        e = SM.block_mirror(p); j = (p // 11 if p % 11 else p // 11 - 1)
        law_ok &= ((e % 4 == 2) == (p % 4 == (1 if j % 2 == 0 else 3)))
        kind = "0mod4" if e % 4 == 0 else ("E1" if E1(e) else "E2notE1")
        rows[kind] += 1
        if kind == "E2notE1" and first_split is None: first_split = (p, e)
    assert law_ok
    pr("\nE3. Offset-11 per-block mirrors of odd primes 3..1e5 (11 left out, it faces 0):", dict(rows))
    pr("  Proven (asserted): the mirror lands in E2 exactly when p = 1 mod 4 in an even block j, or p = 3 mod 4 in an odd block.")
    pr(f"  First decade 3,5,7 -> 8,6,4: one E1 (6), two 0 mod 4. First mirror landing on E2 but not E1: {first_split[0]} -> {first_split[1]}.")

    open(os.path.join(HERE, "pysr-even-primes_v1.0_11-26-2026.txt"), "w").write("\n".join(out) + "\n")

    # ---------- STAGE 2: PySR, one short fit at a time
    if "pysr" in sys.argv:
        def others():
            r = subprocess.run(["pgrep", "-fl", "julia|pysr"], capture_output=True, text=True).stdout.splitlines()
            me = {str(os.getpid()), str(os.getppid())}
            return [l for l in r if l.split()[0] not in me and "pysr-even-primes" not in l and "pgrep" not in l]
        def wait_free():
            for _ in range(20):
                o = others()
                if not o: return True
                print("waiting, other julia/pysr:", o); time.sleep(30)
            return False
        from pysr import PySRRegressor
        import sympy as sp
        def run(tag, X, y, names, w=None):
            if not wait_free(): pr(f"PySR {tag}: skipped, another job held Julia for 10 min"); return None
            mdl = PySRRegressor(niterations=25, timeout_in_seconds=120, populations=12, maxsize=15,
                                binary_operators=["+", "-", "*", "/"], unary_operators=["log"],
                                output_directory=os.path.join(HERE, "pysr-runs"), run_id="even-" + tag, progress=False,
                                verbosity=0, random_state=0, deterministic=True, parallelism="serial")
            mdl.fit(X, y, weights=w, variable_names=names)
            shutil.copy(os.path.join(HERE, "pysr-runs", "even-" + tag, "hall_of_fame.csv"),
                        os.path.join(HERE, f"pysr-hof-even-{tag}_v1.0_11-26-2026.csv"))
            pr(f"\nPySR {tag}:"); pr(mdl.equations_[["complexity", "loss", "equation"]].to_string())
            return mdl
        # fit 1: depth-2 count from strand hits (exact check with integers)
        ms = [m for m in range(3, 3001, 2)]
        X1 = np.array([[h(m), sq(m)] for m in ms], float); y1 = np.array([f0(4 * m) for m in ms], float)
        m1 = run("depth2", X1, y1, ["h", "s"])
        if m1 is not None:
            hs, ss = sp.symbols("h s"); best = None
            for _, row in m1.equations_.iterrows():
                ex = sp.nsimplify(row["sympy_format"], rational=True, tolerance=1e-6)
                fn = sp.lambdify((hs, ss), ex, "sympy")
                okx = all(sp.Rational(fn(sp.Integer(h(m)), sp.Integer(sq(m)))) == f0(4 * m) for m in range(3, 20001, 2))
                if okx: best = ex; break
            pr(f"  depth2 exact (integers, m odd 3..20000): {best}")
        # fit 2: E1 share by dyadic block
        a2 = np.array([a for a, _ in share], float); y2 = np.array([float(s) for _, s in share])
        m2 = run("e1-share", a2[:, None], y2, ["a"], w=1 / y2 ** 2)
        # fit 3: mean E1 gap (E2 steps) by block
        y3 = np.array([gm for _, gm in gapmean])
        m3 = run("e1-gap", a2[:, None], y3, ["a"], w=1 / y3 ** 2)
        for tag, mdl, yy in (("e1-share", m2, y2), ("e1-gap", m3, y3)):
            if mdl is None: continue
            pred = mdl.predict(a2[:, None])
            pr(f"  {tag} best: {mdl.sympy()}  max rel. error over a=4..20: {np.max(np.abs(pred / yy - 1)):.4f}"
               f"  (a=20: {pred[-1]:.5f} vs {yy[-1]:.5f})")
        open(os.path.join(HERE, "pysr-even-primes_v1.0_11-26-2026.txt"), "w").write("\n".join(out) + "\n")

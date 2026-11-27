# PySR consistent forms (tUrUq, 11-26-2026): "have pysr controlled by an agent try to find versions of the formula that are most
# consistent and also show any insights that may show any thing they may have missed."
# Stage 1 (numpy answer key to 1e8, exact counts) always runs; stage 2 runs PySR one job at a time:  python3 <this> pysr
# Fit bands below 1e7, hold out [1e7, 1e8). Imports today's code (mapped-out places_needed), does not change it.
import importlib.util, math, os, sys, json, shutil, functools, numpy as np
from collections import Counter
HERE = os.path.dirname(os.path.abspath(__file__))
out = []
def pr(*a): s = " ".join(str(x) for x in a); print(s, flush=True); out.append(s)
def save(): open(os.path.join(HERE, "pysr-consistent_v1.0_11-26-2026.txt"), "w").write("\n".join(out) + "\n")

TOP = 10 ** 8
isP = np.ones(TOP + 1, dtype=bool); isP[:2] = False; isP[4::2] = False
for i in range(3, int(TOP ** 0.5) + 1, 2):
    if isP[i]: isP[i * i::2 * i] = False
P = np.flatnonzero(isP).astype(np.int64)
assert len(P) == 5761455 and np.searchsorted(P, 10 ** 7) == 664579
SMALL = [int(r) for r in P[P < 100]]
BANDS = [(10 ** a, 10 ** (a + 1)) for a in range(3, 8)]
HELD = BANDS[-1]
C2 = 0.6601618158468696          # twin product prod_{r>2} (1 - 1/(r-1)^2) (same fact by a different route: Hardy-Littlewood)
def tail(R):                     # prod over r > R of (1 - 1/(r-1)^2)
    t = C2
    for r in SMALL:
        if 2 < r <= R: t /= (1 - 1 / (r - 1) ** 2)
    return t
def stackprod(R): return math.prod(r / (r - 1) for r in SMALL if r <= R)

# ============ 1. RANGE z(x, R): first-named share, 90/99 seats ============
pr("1. RANGE FOR THE NEXT PRIME. Stack = blocks 2..R; seats = odd y = p + 2h off every laid block; rank of q among them, nearest first.")
pr("   z_old = (1/ln x) prod_{r<=R} r/(r-1);  z_new = z_old * T(R),  T(R) = prod_{r>R} (1 - 1/(r-1)^2) (the pair weight of the blocks not laid).")
H = 120; HS = np.arange(1, H + 1)
RANGE = []          # rows: band lo, R, family, ln x, z_meas, q90, q99, n
REC = {}            # (lo) -> per-hop arrays for residuals
for lo, hi in BANDS:
    i0, i1 = np.searchsorted(P, lo), np.searchsorted(P, hi)
    idx = np.arange(i0, i1 - 1); idx = idx[:: max(1, len(idx) // 80000)]
    pb, qb = P[idx], P[idx + 1]; ht = (qb - pb) // 2; assert ht.max() <= H
    Y = pb[:, None] + 2 * HS[None, :]
    alive = (Y % 3 != 0); lnx = float(np.mean(np.log(pb))); fam = pb % 6
    for R in SMALL[1:]:
        if R > 3: alive &= (Y % R != 0)
        if R > math.sqrt(lo) / 3: break
        rank = np.cumsum(alive, axis=1)[np.arange(len(pb)), ht - 1]
        for f, m in (("all", slice(None)), ("6k+1", fam == 1), ("6k-1", fam == 5)):
            rk = rank[m]
            RANGE.append(dict(lo=lo, R=R, fam=f, L=lnx, z=float((rk == 1).mean()), q90=int(np.percentile(rk, 90, method="higher")),
                              q99=int(np.percentile(rk, 99, method="higher")), n=int(len(rk))))
        if R in (3, 13, 23): REC[(lo, R)] = (pb.copy(), ht.copy(), rank.copy())
def seats(z, s): return math.ceil(math.log(s) / math.log(1 - z))
pr(f"   {'band':>10} {'R':>3} | {'z meas':>7} {'z_old':>6} {'z_new':>6} | 90/99 meas | 90/99 from z_old | from z_new")
eo, en, hold = [], [], []
for row in RANGE:
    if row["fam"] != "all": continue
    zo = stackprod(row["R"]) / row["L"]; zn = zo * tail(row["R"])
    row["zo"], row["zn"] = zo, zn
    eo.append(abs(zo - row["z"])); en.append(abs(zn - row["z"]))
    if row["lo"] == HELD[0]: hold.append((abs(zo - row["z"]), abs(zn - row["z"]), row))
    if row["R"] in (3, 7, 13, 23, 47, 97):
        pr(f"   {row['lo']:>10} {row['R']:>3} | {row['z']:.4f} {zo:.4f} {zn:.4f} | {row['q90']:3d}/{row['q99']:3d}    | "
           f"{seats(zo, .1):3d}/{seats(zo, .01):3d}         | {seats(zn, .1):3d}/{seats(zn, .01):3d}")
pr(f"   all bands: mean |z - z_old| {np.mean(eo):.4f} (max {max(eo):.4f});  mean |z - z_new| {np.mean(en):.4f} (max {max(en):.4f})")
pr(f"   held-out [1e7,1e8): mean |err| old {np.mean([h[0] for h in hold]):.4f}, new {np.mean([h[1] for h in hold]):.4f}")
assert np.mean(en) < np.mean(eo) / 2 and max(en) < 0.01
# per family
pr("   per family (held-out band, R = 3, 13, 23): z meas 6k+1 / 6k-1 vs z_new")
FAMR = {}
for row in RANGE:
    if row["lo"] == HELD[0] and row["fam"] != "all": FAMR[(row["R"], row["fam"])] = row["z"]
for R in (3, 5, 7, 13, 23, 47, 97):
    zn = stackprod(R) / RANGE[[i for i, r in enumerate(RANGE) if r["lo"] == HELD[0] and r["R"] == R][0]]["L"] * tail(R)
    pr(f"     R={R:2d}: 6k+1 {FAMR[(R,'6k+1')]:.4f}  6k-1 {FAMR[(R,'6k-1')]:.4f}  (z_new {zn:.4f}; ratio +1/-1 {FAMR[(R,'6k+1')]/FAMR[(R,'6k-1')]:.4f})")
save()

# ============ 2. PACKED PLACES B(X) ============
pr("\n2. PACKED PLACES B(X) needed to name every prime up to X (mapped-out table).")
tab = []
for line in open(os.path.join(HERE, "mapped-out-table_v1.0_11-26-2026.txt")):
    if "works for every prime below" in line:
        b = int(line.split("B =")[1].split(":")[0]); X = int(line.split("below")[1])
        if b >= 1: tab.append((b + 1, X))          # at X the next hop first needs b+1 places
sp = importlib.util.spec_from_file_location("mo", os.path.join(HERE, "mapped-out_v1.0_11-26-2026.py"))
mo = importlib.util.module_from_spec(sp); sp.loader.exec_module(mo)
def prevprime(n):
    j = np.searchsorted(P, n, side="right") - 1; return int(P[j])
def pi(n): return int(np.searchsorted(P, n, side="right"))
def perplace(X):                 # blocks-per-place law: primes in (X^(1/(k+1)), X^(1/k)] pack k to a place, r <= sqrt X
    s = 0.0
    for k in range(2, 60):
        a, b = X ** (1 / (k + 1)), X ** (1 / k)
        if b < 2: break
        s += (pi(int(b)) - pi(int(a))) / k
    return s
exact = 0; rowsB = []
for b, X in tab:
    q = int(P[np.searchsorted(P, X, side="right")])
    pkB = mo.places_needed(X, prevprime(math.isqrt(q)))
    exact += (pkB == b)
    rowsB.append((X, b, pkB, perplace(X), math.sqrt(X) / math.log(X)))
pr(f"   packing the blocks up to sqrt(next prime) into places under X gives B exactly at {exact} of {len(tab)} record points")
for X, b, pk, pp, s in rowsB:
    if b in (2, 3, 6, 11, 30, 79, 150, 213):
        pr(f"     X {X:>9d}: B {b:3d}  pack(sqrt) {pk:3d}  per-place law {pp:7.2f}  sqrtX/lnX {s:7.2f}")
B_arr = np.array([r[1] for r in rowsB], float); X_arr = np.array([r[0] for r in rowsB], float)
PP = np.array([r[3] for r in rowsB]); SL = np.array([r[4] for r in rowsB])
m = X_arr > 10 ** 5
for nm, F in (("per-place law", PP), ("sqrtX/lnX", SL)):
    c = np.sum(B_arr[~m] * F[~m]) / np.sum(F[~m] ** 2)      # one scale fitted below 1e5, held out above
    pr(f"   {nm}: B ~ {c:.4f} x law (fit X<1e5); held-out X>1e5 mean |rel err| {np.mean(np.abs(c*F[m]/B_arr[m]-1)):.4f}, max {np.max(np.abs(c*F[m]/B_arr[m]-1)):.4f}")
save()

# ============ 3. GAP COUNTS N(g) ============
pr("\n3. GAP COUNTS N(g) per band with mirror weight M(g) = prod_{odd r | g} (r-1)/(r-2).")
def Mw(g):
    w = 1.0
    for r in SMALL + [int(x) for x in P[(P >= 100) & (P < 300)]]:
        if r > 2 and g % r == 0: w *= (r - 1) / (r - 2)
    return w
GAPS = []
for lo, hi in BANDS[1:]:
    i0, i1 = np.searchsorted(P, lo), np.searchsorted(P, hi)
    g = np.diff(P[i0:i1]); n = len(g); cnt = Counter(g.tolist()); lnx = float(np.mean(np.log(P[i0:i1])))
    for gg in range(2, 200, 2):
        if cnt[gg] >= 50: GAPS.append(dict(lo=lo, g=gg, N=cnt[gg], n=n, L=lnx, M=Mw(gg)))
def gap_old(rows):             # earlier form: per band A, L fitted
    res = {}
    for lo in sorted({r["lo"] for r in rows}):
        rr = [r for r in rows if r["lo"] == lo and r["g"] <= 60]
        x = np.array([r["g"] for r in rr]); y = np.log([r["N"] / r["M"] for r in rr])
        b, a = np.polyfit(x, y, 1)
        res[lo] = max(abs(r["N"] / (math.exp(a + b * r["g"]) * r["M"]) - 1) for r in rr)
    return res
pr("   earlier form A M(g) exp(-g/L), A and L fitted per band, worst ratio error over g <= 60:", {k: round(v, 3) for k, v in gap_old(GAPS).items()})
# no-free-constant form: N(g)/n = (2 C2 / ... ) -> use HL pair weight with the exponential in u = g / ln x
def gap_new(r, a=0.0):
    u = r["g"] / r["L"]
    return r["n"] * (2 * C2 * r["M"] / r["L"]) * math.exp(-u) * math.exp(a * u / r["L"]) if r["g"] > 0 else 0
for nm in ("2 C2 M(g)/ln x * exp(-g/ln x) (no fitted constant)",):
    for lo in sorted({r["lo"] for r in GAPS}):
        rr = [r for r in GAPS if r["lo"] == lo and r["g"] <= 60]
        pr(f"   {nm}: band {lo}: worst |ratio-1| {max(abs(r['N']/gap_new(r)-1) for r in rr):.3f}, mean {np.mean([abs(r['N']/gap_new(r)-1) for r in rr]):.3f}")
save()

# ============ 4. 6k-1 LEAD ============
pr("\n4. THE 6k-1 LEAD L(x) = #(p = 5 mod 6) - #(p = 1 mod 6), p <= x.")
xs = np.unique(np.logspace(3, 8, 241).astype(np.int64))
c5 = np.cumsum(P % 6 == 5); c1 = np.cumsum(P % 6 == 1)
j = np.searchsorted(P, xs, side="right") - 1
LEAD = (c5[j] - c1[j]).astype(float)
SQ = np.sqrt(xs) / np.log(xs); PIS = np.array([pi(math.isqrt(int(x))) for x in xs], float)
for x in (10 ** 4, 10 ** 5, 10 ** 6, 10 ** 7, 10 ** 8):
    k = np.searchsorted(xs, x);
    pr(f"   x {xs[k]:>10d}: lead {int(LEAD[k]):+6d}   sqrt x/ln x {SQ[k]:8.1f}   pi(sqrt x)/2 {PIS[k]/2:7.1f}   lead/(sqrt x/ln x) {LEAD[k]/SQ[k]:.3f}")
mh = xs >= 10 ** 7
pr(f"   lead/(sqrt x/ln x): mean {np.mean(LEAD[~mh]/SQ[~mh]):.3f} (x<1e7), held-out {np.mean(LEAD[mh]/SQ[mh]):.3f}; sd {np.std(LEAD/SQ):.3f}; lead > 0 at {int(np.sum(LEAD>0))}/{len(xs)} points")
# per stacked-zero class: deviation from the class mean vs square count c(a) = #{t mod W : t^2 = a}
pr("   per stacked-zero class at x = 1e8: dev(a) = count(a) - mean; square count c(a); predicted dev = -(c(a)-1) sqrt x/(phi(W) ln x)")
CLS = {}
for W in (6, 30, 210):
    units = [a for a in range(1, W) if math.gcd(a, W) == 1]; ph = len(units)
    sqc = Counter((t * t) % W for t in units)
    cnt = Counter((P[P > 7] % W).tolist())
    mean = np.mean([cnt[a] for a in units]); s = math.sqrt(TOP) / math.log(TOP) / ph
    dev = np.array([cnt[a] - mean for a in units]); pred = np.array([-(sqc[a] - 1) * s for a in units])
    slope = float(np.sum(dev * pred) / np.sum(pred ** 2)); corr = float(np.corrcoef(dev, pred)[0, 1])
    upper = sum(cnt[a] for a in units if a > W // 2) - sum(cnt[a] for a in units if a < W // 2)
    up_sq = sum(sqc[a] for a in units if a > W // 2) - sum(sqc[a] for a in units if a < W // 2)
    CLS[W] = (slope, corr, upper, up_sq)
    pr(f"     W={W:3d}: corr(dev, -(c-1)) = {corr:.3f}, scale {slope:.3f}; upper-half minus lower-half {upper:+d}; square count upper-lower {up_sq:+d}")
    if W == 30:
        for a in units: pr(f"        a={a:2d} c(a)={sqc[a]} dev {cnt[a]-mean:+8.1f} pred {-(sqc[a]-1)*s:+8.1f}")
assert np.all(LEAD > 0) and CLS[30][1] > 0.3 and CLS[210][1] > 0.2
save()

# ============ 5. RULE-BREAKERS C(x) ============
pr("\n5. RULE-BREAKER COUNT C(x) (set from rule-breakers_v1.0, n <= 1e6).")
import io, contextlib
sp = importlib.util.spec_from_file_location("rb", os.path.join(HERE, "rule-breakers_v1.0_11-26-2026.py"))
rb = importlib.util.module_from_spec(sp)
with contextlib.redirect_stdout(io.StringIO()): sp.loader.exec_module(rb)
S = sorted(rb.S)
STR = {"2^a": lambda a: 2 ** a, "2^a+1": lambda a: 2 ** a + 1, "2^a+2": lambda a: 2 ** a + 2, "3*2^a": lambda a: 3 * 2 ** a, "3*2^a+1": lambda a: 3 * 2 ** a + 1}
strand_set = {f(a) for f in STR.values() for a in range(0, 21)}
spor = [x for x in S if x not in strand_set]
pr(f"   {len(S)} breakers; on the five 2-scale strands 2^a, 2^a+1, 2^a+2, 3*2^a, 3*2^a+1: {len(S)-len(spor)}; off them: {spor}")
covered = {}
for nm, f in STR.items():
    mem = [f(a) for a in range(0, 21) if f(a) <= 10 ** 6]; covered[nm] = (sum(x in rb.S for x in mem), len(mem))
pr("   strand members that are breakers / strand members <= 1e6:", covered)
def C_exact(x):  # every breaker on the 5 strands, plus the off-strand list
    return sum(1 for s in S if s <= x)
def C_law(x):
    l = math.log2(x)
    return (math.floor(l) + 1) + math.floor(math.log2(max(x - 1, 1))) + 1 + math.floor(math.log2(max(x - 2, 1))) + math.floor(math.log2(x / 3)) + 1 + math.floor(math.log2(max((x - 1) / 3, 1))) + 1
xs5 = [2 ** j for j in range(1, 20)]
Cv = np.array([C_exact(x) for x in xs5]); L2 = np.log2(xs5)
pr("   C(2^j), j=1..19:", Cv.tolist())
b5, a5 = np.polyfit(L2[:15], Cv[:15], 1)
pr(f"   straight line fit j<=15: C = {a5:.3f} + {b5:.4f} log2 x; held-out j=16..19 max |err| {np.max(np.abs(Cv[15:] - (a5 + b5 * L2[15:]))):.2f}")
off_strand_upto = lambda x: sum(1 for s in spor if s <= x)
pr("   per-strand reading: slope = number of strands that keep breaking; off-strand breakers <= 2^j:", [off_strand_upto(x) for x in xs5])
save()

# ============ 6. RESIDUALS by family (range) ============
pr("\n6. RESIDUALS of z_new by family on the held-out band (first-named share per class minus z_new).")
RES = {}
for (lo, R), (pb, ht, rank) in REC.items():
    if lo != HELD[0]: continue
    zn = stackprod(R) / float(np.mean(np.log(pb))) * tail(R)
    for nm, key in (("p mod 6", pb % 6), ("p mod 4", pb % 4), ("p mod 12", pb % 12), ("p mod 30", pb % 30)):
        cells = {int(k): float((rank[key == k] == 1).mean()) - zn for k in np.unique(key)}
        RES[(R, nm)] = cells
        pr(f"   R={R:2d} {nm:8s}: " + "  ".join(f"{k}:{v:+.4f}" for k, v in cells.items()))
save()

# ============ 7. EXPLORATORY data (his readings of p) ============
@functools.lru_cache(maxsize=None)
def u(n):
    if n <= 3: return n
    k = n >> 1; return 2 * u(k) + (u(k + 1) if n & 1 else 0)
lo, hi = 10 ** 6, 10 ** 7
i0, i1 = np.searchsorted(P, lo), np.searchsorted(P, hi)
rng = np.random.default_rng(0); idx = np.sort(rng.choice(np.arange(i0, i1 - 1), 4000, replace=False))
pe, qe = P[idx], P[idx + 1]
def feats(p):
    p = int(p); f = 1 if p % 6 == 1 else -1; k = (p + 1) // 6 if f == -1 else (p - 1) // 6
    d30 = min(p % 30, 30 - p % 30); d210 = min(p % 210, 210 - p % 210)
    return [f, (p % 4 == 1) * 2 - 1, d30, d210, u(p) / p, (u(p) - p) / p, bin(p).count("1"), k % 5, p % 30, math.log(p)]
EXN = ["f", "side", "d30", "d210", "ur", "imb", "nbits", "k5", "c30", "lnp"]
EX = np.array([feats(p) for p in pe], float); hE = ((qe - pe) // 2).astype(float)
flipE = ((qe % 6) != (pe % 6)).astype(float)
# grouped targets (mean h and flip share per p mod 210 class) - less noise for the search
cls = (P[i0:i1] % 210); hh = np.diff(P[i0:i1 + 1])[: i1 - i0] // 2; nxt = P[i0 + 1:i1 + 1] % 6; cur = P[i0:i1] % 6
G = []
for c in sorted(set(cls.tolist())):
    msk = cls == c; c = int(c)
    G.append([1 if c % 6 == 1 else -1, 1 if c % 4 in (1,) else -1, min(c % 30, 30 - c % 30), min(c, 210 - c),
              c % 5, c % 7, float(hh[msk].mean()), float((nxt[msk] != cur[msk]).mean())])
G = np.array(G, float)
pr(f"\n7. EXPLORATORY: {len(G)} classes mod 210 in [1e6,1e7): mean half gap ranges {G[:,6].min():.3f}..{G[:,6].max():.3f}; facing-flip share {G[:,7].min():.3f}..{G[:,7].max():.3f}")
# simple check: mean h per class vs its first-seat structure: count of open seats in h=1..6 (off 5,7 relative to class)
open6 = np.array([sum(1 for h in range(1, 7) if all(((c + 2 * h) % r) for r in (2, 3, 5, 7))) for c in sorted(set(cls.tolist()))], float)
pr(f"   corr(mean h per class, open seats among h=1..6 off 2,3,5,7) = {np.corrcoef(G[:,6], open6)[0,1]:.3f}")
save()
json.dump(dict(range=RANGE, gaps=GAPS, B=rowsB, lead=dict(x=xs.tolist(), L=LEAD.tolist()), C=Cv.tolist()),
          open(os.path.join(HERE, "pysr-consistent-data_v1.0_11-26-2026.json"), "w"))

# ============ PySR stage ============
if "pysr" in sys.argv:
    import subprocess, time
    from pysr import PySRRegressor
    def run(tag, X, y, names, w=None, un=(), iters=60, t=90, maxsize=18):
        if tag in os.environ.get("SKIP", "").split(","): return None
        while subprocess.run(["pgrep", "-f", "julia"], capture_output=True).stdout.strip(): time.sleep(5)
        mdl = PySRRegressor(niterations=iters, timeout_in_seconds=t, populations=15, maxsize=maxsize,
                            binary_operators=["+", "-", "*", "/"], unary_operators=list(un),
                            output_directory=os.path.join(HERE, "pysr-runs"), run_id=f"consistent-{tag}", progress=False,
                            verbosity=0, random_state=0, deterministic=True, parallelism="serial")
        mdl.fit(X, y, weights=w, variable_names=names)
        shutil.copy(os.path.join(HERE, "pysr-runs", f"consistent-{tag}", "hall_of_fame.csv"),
                    os.path.join(HERE, f"pysr-hof-consistent-{tag}_v1.0_11-26-2026.csv"))
        pr(f"\nPySR {tag}:"); pr(mdl.equations_[["complexity", "loss", "equation"]].to_string()); save()
        return mdl
    def heldout(mdl, X, y, rel=True):
        if mdl is None: return
        e = []
        for i in range(len(mdl.equations_)):
            pv = mdl.predict(X, index=i); e.append(float(np.max(np.abs(pv / y - 1) if rel else np.abs(pv - y))))
        pr("   held-out max error per complexity: " + ", ".join(f"c{int(c)}:{v:.4f}" for c, v in zip(mdl.equations_["complexity"], e))); save()
    # T1: z from (S = stack product, T = tail, L = ln x, R); fit < 1e7, held out 1e7..1e8
    R1 = [r for r in RANGE if r["fam"] == "all"]
    X1 = np.array([[stackprod(r["R"]), tail(r["R"]), r["L"], r["R"]] for r in R1]); y1 = np.array([r["z"] for r in R1])
    tr = np.array([r["lo"] < HELD[0] for r in R1])
    m1 = run("range-z", X1[tr], y1[tr], ["Sp", "Tt", "Lx", "R"], w=1 / y1[tr] ** 2)
    heldout(m1, X1[~tr], y1[~tr])
    # T2: B(X) from s = sqrtX, L = lnX, Pq = pi(sqrtX), PP = per-place law
    X2 = np.c_[np.sqrt(X_arr), np.log(X_arr), [pi(math.isqrt(int(x))) for x in X_arr], PP]
    m2 = run("packed-B", X2[~m], B_arr[~m], ["s", "L", "Pq", "PP"], w=1 / B_arr[~m] ** 2)
    heldout(m2, X2[m], B_arr[m])
    # T3: gap shape: y = N/(n M/L) against u = g/L and L
    tr3 = np.array([r["lo"] < HELD[0] for r in GAPS])
    X3 = np.array([[r["g"] / r["L"], r["L"], r["g"]] for r in GAPS]); y3 = np.array([r["N"] * r["L"] / (r["n"] * r["M"]) for r in GAPS])
    m3 = run("gap-shape", X3[tr3], y3[tr3], ["u", "L", "g"], w=np.array([r["N"] for r in GAPS])[tr3] / y3[tr3] ** 2, un=("exp",))
    heldout(m3, X3[~tr3], y3[~tr3])
    # T4: lead from sqrt x, ln x, pi(sqrt x)
    X4 = np.c_[np.sqrt(xs), np.log(xs), PIS]
    m4 = run("lead", X4[~mh], LEAD[~mh], ["s", "L", "Pq"], t=75)
    heldout(m4, X4[mh], LEAD[mh], rel=False)
    # T5: rule-breakers C vs j = log2 x (fit j<=15)
    m5 = run("breakers", L2[:15, None], Cv[:15].astype(float), ["j"], t=60, iters=40)
    heldout(m5, L2[15:, None], Cv[15:].astype(float), rel=False)
    # EXPLORE a: per-hop h from his readings of p (open feature set)
    tr7 = np.arange(len(hE)) < 3000
    m6 = run("explore-h", EX[tr7], hE[tr7], EXN, t=75)
    heldout(m6, EX[~tr7], hE[~tr7], rel=False)
    pr(f"   baseline: predict mean h ({hE[tr7].mean():.3f}) -> held-out mean |err| {np.mean(np.abs(hE[~tr7]-hE[tr7].mean())):.3f}")
    # EXPLORE b: per class mod 210 mean h and flip share
    m7 = run("explore-class-h", G[:, :6], G[:, 6], ["f", "side", "d30", "d210", "c5", "c7"], t=60)
    m8 = run("explore-class-flip", G[:, :6], G[:, 7], ["f", "side", "d30", "d210", "c5", "c7"], t=60)
    save()

# ============ GEMS (exact identities; checked by computer, PySR asked to recover them from his readings) ============
@functools.lru_cache(maxsize=None)
def v(n):                       # pure halving count: 3 = 1,2,1 (v(1), v(2) = 1, 2; same recursion, no word)
    if n <= 2: return n
    k = n >> 1; return 2 * v(k) + (v(k + 1) if n & 1 else 0)
def dstep(c): return 2 * u(c) - u(c + 1)
if "gems" in sys.argv or "pysr" in sys.argv:
    pr("\nGEMS (exact on every case checked):")
    n1 = 0
    for c in range(2, 400):
        for a in range(0, 12):
            for j in range(0, 2 ** a + 1):
                assert u(c * 2 ** a + j) == u(c) * v(2 ** a + j) - dstep(c) * v(j); n1 += 1
    pr(f"   G1 two-point law: u(c 2^a + j) = u(c) v(2^a + j) - d(c) v(j), d(c) = 2u(c) - u(c+1); c >= 2, 0 <= j <= 2^a: {n1} cases (c<400, a<12)")
    assert any(u(2 ** a + j) != v(2 ** a + j) for a in range(1, 4) for j in range(1, 2 ** a))   # c = 1 is the word exception
    n2 = 0
    for c in range(2, 300):
        for a in range(0, 10):
            assert 3 * sum(u(c * 2 ** a + j) for j in range(2 ** a)) == u(c) * (4 * 5 ** a - 2 ** a) - dstep(c) * (5 ** a - 2 ** a); n2 += 1
    for a in range(0, 14):
        assert 3 * sum(v(2 ** a + j) for j in range(2 ** a)) == 4 * 5 ** a - 2 ** a and 3 * sum(v(j) for j in range(2 ** a)) == 5 ** a - 2 ** a
    pr(f"   G2 block sum: 3 sum_(j<2^a) u(c 2^a + j) = u(c)(4*5^a - 2^a) - d(c)(5^a - 2^a), c >= 2: {n2} cases; v sums (4*5^a-2^a)/3, (5^a-2^a)/3 for a < 14")
    pr(f"   G3 record block: B at each of the {len(tab)} record points = places_needed(X, prevprime(isqrt(nextprime(X)))) exactly ({exact}/{len(tab)}), X < 1e7")
    assert exact == len(tab)
    save()
if "pysr" in sys.argv:
    rng = np.random.default_rng(1)
    rows = [(int(c), int(a), int(rng.integers(0, 2 ** a + 1))) for c, a in zip(rng.integers(2, 200, 400), rng.integers(1, 10, 400))]
    XG = np.array([[u(c), dstep(c), v(2 ** a + j), v(j)] for c, a, j in rows], float)
    yG = np.array([u(c * 2 ** a + j) for c, a, j in rows], float)
    mg = run("gem-two-point", XG[:300], yG[:300], ["uc", "dc", "vA", "vj"], t=60, iters=40)
    heldout(mg, XG[300:], yG[300:], rel=False)
    rowsS = [(c, a) for c in range(2, 60) for a in range(0, 8)]
    XS = np.array([[u(c), dstep(c), 5.0 ** a, 2.0 ** a] for c, a in rowsS]); yS = np.array([sum(u(c * 2 ** a + j) for j in range(2 ** a)) for c, a in rowsS], float)
    ms = run("gem-block-sum", XS[::2], yS[::2], ["uc", "dc", "F", "Tw"], t=60, iters=40)
    heldout(ms, XS[1::2], yS[1::2], rel=False)
    save()

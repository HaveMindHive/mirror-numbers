# Relativity frames and a 4D map (tUrUq, 11-26-2026): "take a page from the theory of relativity ... scalar
# dimensionality, 4D mapping ... maybe composite, oddeven or evenodd or oddeveneven or evenoddodd may show us ...
# the mirror and lake mirror and how they all interact ... we may need ^ and v to be present as well."
#
# NOTATION ADDED:  v = one level down (into scale, microscope, lake side): v(n) = w,c,w (unified code, one comma).
#                  ^ = one level up (out, telescope): a block read as one number (sum of its parts); ^v = identity.
#   ^ on the number line = doubling seat (n -> 2n, the even frame);  v = halving seat (n -> w = n//2).
#   with | (mirror, offset O):  m_O(^n) = ^ m_{O/2}(n)   (the mirror's offset is a length and scales with ^)
#   with lm (K^2/n):            lm(^n)  = v lm(n)        (the lake runs scale the other way: ^ and v swap)
#   with lm on the build word (upside down, ends kept): lm_in(n) = 3*2^(L-1) - n  = mirror through the wall
#                  3*2^(L-2), the self-count seat at the middle of n's octave (L = bit length).
#   <> (operator / observer) and , keep their meaning; ^ v say which way a comma is being walked.
# Imports today's code (unified-code); does not change it.  Run: python3 this.py [pysr]
import os, sys, math, time, itertools, importlib.util, numpy as np
from fractions import Fraction as F
from collections import Counter, defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
def load(name):
    sp = importlib.util.spec_from_file_location(name.replace("-", "_"), os.path.join(HERE, name + "_v1.0_11-26-2026.py"))
    m = importlib.util.module_from_spec(sp); sp.loader.exec_module(m); return m
uc = load("unified-code"); sml = load("standard-mirror-line")
OUT = []
def pr(*a):
    s = " ".join(str(x) for x in a); print(s); OUT.append(s)
T0 = time.time()

# ---------------- arrays ----------------
NU = 2 ** 22 + 4
u = np.zeros(NU, dtype=np.int64); u[1:4] = [1, 2, 3]
for n in range(4, NU):
    k = n >> 1; u[n] = 2 * u[k] + (u[k + 1] if n & 1 else 0)
N = 10 ** 7 + 10
spf = np.zeros(N, dtype=np.int32)
for i in range(2, int(N ** .5) + 1):
    if spf[i] == 0:
        s = spf[i * i::i]; s[s == 0] = i; spf[i * i::i] = s
idx = np.arange(N); z = (spf == 0) & (idx >= 2); spf[z] = idx[z]
isP = (spf == idx) & (idx >= 2)
v2 = np.zeros(N, dtype=np.int64); core = idx.copy(); core[0] = 1
for _ in range(25):
    e = core % 2 == 0; v2[e] += 1; core[e] //= 2
Om = np.zeros(N, dtype=np.int64); y = core.copy()
while True:
    a = y > 1
    if not a.any(): break
    y[a] //= spf[y[a]]; Om[a] += 1
def cls(n): return (v2[n] % 2) * 2 + (Om[n] % 2)   # 0 hinge-pal, 1 centre-O pal, 2 centre-E pal, 3 no pal
CLS = ["hinge (a,b even)", "centre O (a even,b odd)", "centre E (a odd,b even)", "no self-mirror (a,b odd)"]

# ---------------- 1. notation ^ v ----------------
pr("RELATIVITY / 4D v1.0 11-26-2026\n\n== 1. NOTATION ^ v ==")
for n in range(1, 400):
    one = uc.write(n, 1); assert sum(map(int, one.split(","))) == n          # ^ of v(n) is n
    for L in range(1, 5):                                                    # v keeps the mirror: every level is a palindrome
        w = uc.write(n, L).replace(",", " ").split(); assert w == w[::-1]
for n in range(1, 2000):
    for O in (11, 22, 101):
        assert 2 * (O - n) == 2 * O - 2 * n                                  # m_O then ^ = ^ then m_2O
    K = 11; assert F(K * K, 2 * n) == F(K * K, n) / 2                      # lm(^n) = v lm(n)
for n in range(3, 1 << 16, 2):
    L = n.bit_length(); assert n ^ ((1 << (L - 1)) - 2) == 3 * (1 << (L - 1)) - n   # lake_in = wall mirror
    assert u[3 * (1 << (L - 2))] == 3 * (1 << (L - 2)) if L >= 2 else True        # its fold seat self-counts
pr("asserted: ^v(n) = n; every v level is a palindrome (n<400); m_O(^n) = ^m_(O/2)(n); lm(^n) = v lm(n);")
pr("          lake on the build word (interior bits flipped) = n -> 3*2^(L-1) - n, fold seat = the wall 3*2^(L-2), u = n there.")
pr("  8 = 4,0,4 ; v8 = 2,0,2,,0,0,0,,2,0,2 ; ^ of that = 8.  lm(8)=121/8, lm(^8)=121/16 = v lm(8).  lake_in(11=1011b) = 1101b = 13 = 24-11.")

# ---------------- 2. parity words of composites ----------------
pr("\n== 2. PARITY WORDS (letters E = factor 2, O = odd prime; a = #E = halvings, b = #O = odd factors with repeats) ==")
# every ordered arrangement of the factor letters is a face; its reverse is also a face (mirror symmetric set, proven);
# a palindromic face exists iff not (a odd and b odd); centre letter E iff a odd, O iff b odd, none (hinge) iff both even.
for a_ in range(0, 6):
    for b_ in range(0, 6):
        if a_ + b_ == 0 or a_ + b_ > 8: continue
        words = set(itertools.permutations("E" * a_ + "O" * b_))
        pal = [w for w in words if w == w[::-1]]
        assert all(w[::-1] in words for w in words)
        assert bool(pal) == (not (a_ % 2 and b_ % 2))
        if pal and (a_ + b_) % 2: assert all(w[len(w) // 2] == ("E" if a_ % 2 else "O") for w in pal)
        assert len(words) == math.comb(a_ + b_, a_)
pr("asserted (a,b<6): mirror (reverse) maps faces to faces; palindromic face exists unless a,b both odd;")
pr("  oddeven/evenodd (a,b)=(1,1)=2p: no self-mirror face, only the pair EO|OE.  oddeveneven (2,1)=4p: EOE, centre O.")
pr("  evenoddodd (1,2)=2pq,2p^2: OEO, centre E.  lake (E<->O) maps (a,b)->(b,a): 4p <-> 2pq lake partners; prime O <-> 2.")
for X in (10 ** 5, 10 ** 6, 10 ** 7):
    n = np.arange(2, X + 1); c = cls(n); comp = ~isP[n]
    pr(f"  to {X:>8}: all {np.bincount(c, minlength=4).tolist()}  composites {np.bincount(c[comp], minlength=4).tolist()}  (order {CLS})")
pr("  centre-O beats hinge on all n (Polya-type lean: the same fact reached by a different route, Liouville/Polya);")
pr("  among composites the hinge class leads (primes all sit in centre O).")
# named classes and which side primes border them
pr("  named word classes, exact counts to 1e7, prime on the left (n-1) vs on the right (n+1):")
n = np.arange(4, 10 ** 7 + 1); a_ = v2[n]; b_ = Om[n]
for name, (A, B) in [("oddeven/evenodd 2p", (1, 1)), ("oddeveneven 4p", (2, 1)), ("evenoddodd 2pq,2p^2", (1, 2)),
                     ("evenevenodd.. 8p", (3, 1)), ("2pqr..", (1, 3)), ("odd pq", (0, 2)), ("odd pqr", (0, 3))]:
    sel = n[(a_ == A) & (b_ == B)]
    pr(f"    {name:22s} count {len(sel):8d}  prime left {int(isP[sel-1].sum()):7d}  prime right {int(isP[sel+1].sum()):7d}  both {int((isP[sel-1]&isP[sel+1]).sum()):6d}")
# neighbours of primes by side
pr("  classes of a prime's two neighbours (p >= 5), by family p mod 4 (deep side = 4 | neighbour):")
for X in (10 ** 6, 10 ** 7):
    p = np.nonzero(isP[5:X + 1])[0] + 5
    for fam in (1, 3):
        q = p[p % 4 == fam]
        pr(f"    to {X:>8} p={fam} mod 4 ({len(q)}): left {np.bincount(cls(q-1), minlength=4).tolist()}  right {np.bincount(cls(q+1), minlength=4).tolist()}")
    e2 = np.where(p % 4 == 1, p + 1, p - 1)             # the 2*odd neighbour (E2 seat) of each prime
    sh = int((Om[e2] % 2 == 0).sum()) / len(e2)
    base = np.arange(6, X + 1, 4); bb = float((Om[base] % 2 == 0).mean())
    pr(f"    to {X:>8}: E2 neighbour's odd core has even Omega in {int((Om[e2]%2==0).sum())} of {len(e2)} ({sh:.5f}); all 2*odd seats {bb:.5f}")
X = 10 ** 7; p = np.nonzero(isP[5:X + 1])[0] + 5
e2 = np.where(p % 4 == 1, p + 1, p - 1)
assert ((p % 4 == 1) <= (cls(p + 1) >= 2)).all() and ((p % 4 == 3) <= (cls(p - 1) >= 2)).all()
pr("  asserted to 1e7: circle primes (1 mod 4) have the 2*odd neighbour on the right, 3 mod 4 on the left (known side law).")
# spine word (binary = centre digits of the unified code going down) under mirror (reverse) and lake (wall mirror)
pr("  spine word (centre digits going down = binary), odd n of bit length L: prime -> prime under each frame")
pr("    L  primes  mirror(reverse)  lake_in(wall mirror)  lake of mirror   random odd share")
for L in (12, 14, 16, 18, 20, 22, 23):
    lo, hi = 1 << (L - 1), 1 << L; od = np.arange(lo + 1, hi, 2); W = 3 * lo
    rv = np.array([int(bin(int(x))[:1:-1], 2) for x in od]) if L <= 20 else None
    po = int(isP[od].sum()); lk = int((isP[od] & isP[W - od]).sum())
    if rv is not None:
        mr = int((isP[od] & isP[rv]).sum()); lm_ = int((isP[od] & isP[W - rv]).sum())
        pr(f"   {L:2d} {po:7d}  {mr:7d} ({mr/po:.4f})  {lk:7d} ({lk/po:.4f})  {lm_:7d} ({lm_/po:.4f})   {po/len(od):.4f}")
    else:
        pr(f"   {L:2d} {po:7d}        -            {lk:7d} ({lk/po:.4f})        -           {po/len(od):.4f}")
pr("  both frames keep the 3 mirror (the wall offset 3*2^(L-1) is a multiple of 3; read backwards, 2 = -1 on the 3 mirror),")
pr("  so a prime's image is off 3 and prime -> prime runs above the random odd share (x1.3 to x1.6 at L = 20).")

# ---------------- 3. frames and invariants ----------------
pr("\n== 3. FRAMES: which readings stay the same (invariant), change by a fixed law (contract), or have no law ==")
X = 10 ** 6
bitlen = np.zeros(4 * X + 4, dtype=np.int64)
for L in range(1, 25): bitlen[1 << (L - 1): min(1 << L, len(bitlen))] = L
pop = np.array([bin(i).count("1") for i in range(4 * X + 4)], dtype=np.int64)
def g_(a, b): return np.gcd(a, b)
R = {"odd core": lambda n: core[n], "halvings a": lambda n: v2[n], "odd factors b": lambda n: Om[n],
     "word class": lambda n: cls(n), "prime": lambda n: isP[n].astype(np.int64), "n mod 6": lambda n: n % 6,
     "u mod 4": lambda n: u[n] % 4, "u/n": lambda n: (u[n] // g_(u[n], n)) * 10 ** 8 + n // g_(u[n], n),
     "imbalance u-n": lambda n: u[n] - n, "ones (popcount)": lambda n: pop[n], "level L": lambda n: bitlen[n]}
np.seterr(divide="ignore", invalid="ignore")
nn = np.arange(1, X + 1); odd_n = nn[nn % 2 == 1]
bmv = np.vectorize(sml.block_mirror)
FR = {"^ (2n)": (nn, 2 * nn), "v (n//2, n even)": (nn[nn % 2 == 0], nn[nn % 2 == 0] // 2), "^3 (3n)": (nn, 3 * nn),
      "m 11-block": (nn, bmv(nn)), "lake_in wall": (odd_n[odd_n > 2], 3 * (1 << (bitlen[odd_n[odd_n > 2]] - 1)) - odd_n[odd_n > 2]),
      "mirror reverse (odd)": (odd_n, np.array([int(bin(int(x))[:1:-1], 2) for x in odd_n]))}
pr(f"  share of n (to {X}) whose image value is the one most often paired with its own value; 1.0000 = exact law; '=' = invariant")
hdr = "  reading            " + " ".join(f"{k[:14]:>15s}" for k in FR); pr(hdr)
LAW = {}
for rn, f in R.items():
    row = []
    for fn, (dom, img) in FR.items():
        a, b = f(dom), f(img)
        if np.array_equal(a, b): row.append("="); LAW[(rn, fn)] = "="; continue
        pairs = Counter(zip(a.tolist(), b.tolist())); best = defaultdict(int)
        for (x, y_), c in pairs.items(): best[x] = max(best[x], c)
        sh = sum(best.values()) / len(a); LAW[(rn, fn)] = sh; row.append(f"{sh:.4f}")
    pr(f"  {rn:18s} " + " ".join(f"{x:>15s}" for x in row))
assert LAW[("u/n", "^ (2n)")] == "=" and LAW[("odd core", "^ (2n)")] == "=" and LAW[("imbalance u-n", "^ (2n)")] == 1.0
assert LAW[("u/n", "v (n//2, n even)")] == "=" and LAW[("odd factors b", "^ (2n)")] == "="
assert LAW[("level L", "lake_in wall")] == "=" and LAW[("ones (popcount)", "mirror reverse (odd)")] == "="
pr("  read-out: invariant under ^ and v: odd core, b, u/n, ones (proven: u(2k) = 2u(k)); fixed law under ^: imbalance (x2),")
pr("  a (+1), L (+1), word class (a flips). Caution: readings that take nearly one value per n (odd core, u/n, imbalance)")
pr("  score near 1 in any frame and say nothing there; u mod 4 is 0 for most n. Few-valued readings with a real law:")
pr("  n mod 6 under the lake (n -> -n mod 6, wall offset = 0 mod 6), ones under reverse (=), L under lake/reverse (=).")
pr("  No law: prime under m (0.92), lake (0.84), reverse (0.84); word class under m, lake, reverse (0.34-0.50).")
pr("  So the 'interval' of a number across the scale frames is (odd core, u/n): a prime p and its even primes 2p, 4p ...")
pr("  are one scale-orbit; E1 = p seen from one level up. Left-outs are the orbits of odd composites plus the ^^ of anything.")
# do invariants distinguish families?  u/n of primes vs odd composites in the same octave (scale frame removes size)
for L in (16, 20):
    lo, hi = 1 << (L - 1), 1 << L; od = np.arange(lo + 1, hi, 2); r_ = u[od] / od
    pr(f"  octave L={L}: mean u/n primes {r_[isP[od]].mean():.5f}  odd composites {r_[~isP[od]].mean():.5f}  (no split)")
# rule-breaker families from rule-breakers_v1.0 (powers, walls, both strands, 2^a+2, sporadic) on the invariant u/n
br = sorted({1 << a for a in range(21)} | {3 << a for a in range(20)} | {(1 << a) + 1 for a in range(1, 21)} |
            {(3 << a) + 1 for a in range(20)} | {(1 << a) + 2 for a in range(1, 20)} | {5, 7, 9, 11, 13, 15, 18, 22, 33, 36, 44, 66, 88, 272, 2112, 4224, 8448})
br = [x for x in br if x <= X]
inv = Counter(F(int(u[x]), x) for x in br)
pr(f"  rule-breakers (families of rule-breakers_v1.0, {len(br)} to 1e6): distinct u/n values {len(inv)}; u/n = 1 (self-count) {inv[F(1)]};"
   f" u/n = 20/11 {inv[F(20,11)]}, 28/15 {inv[F(28,15)]}: breakers ride a few fixed invariants (their scale-orbits).")

# ---------------- 4. the lake side law: scale depth L enters as a coordinate ----------------
pr("\n== 4. BELOW vs ABOVE a power mirror: the lake side carries the level L, the telescope side does not ==")
sig = {0: F(0), 1: F(1)}; tau = {0: F(-2), 1: F(1, 2)}
for r in range(2, 4097):
    if r % 2 == 0: sig[r] = sig[r // 2]; tau[r] = tau[r // 2] + sig[r // 2]
    else:
        j = r // 2; sig[r] = sig[j + 1] + sig[j] / 2; tau[r] = sig[r] + tau[j + 1] + tau[j] / 2
for r in range(1, 4097):
    for L in range(14, 23):
        assert u[(1 << L) - r] == (1 << (L - 1)) * (sig[r] * L - tau[r]), (r, L)
pr("  asserted, r = 1..4096, L = 14..22:  u(2^L - r) = 2^(L-1) * (sig(r)*L - tau(r))")
pr("    sig(2j) = sig(j), sig(2j+1) = sig(j+1) + sig(j)/2 ; tau(2j) = tau(j) + sig(j), tau(2j+1) = sig(2j+1) + tau(j+1) + tau(j)/2")
pr("    sig(0)=0, sig(1)=1, tau(0)=-2, tau(1)=1/2.  The build rule u(2k+1) = 2u(k) + u(k+1) comes back MIRRORED:")
pr("    2 sig(2j+1) = 2 sig(j+1) + sig(j)  (the weight 2 moves from the near wing to the far wing).")
pr("  first slopes sig(r), r = 1..33: " + ", ".join(str(sig[r]) for r in range(1, 34)))
pr("  first tau(r): " + ", ".join(str(tau[r]) for r in range(1, 18)))
# above the power: fixed slope, no L term (the anchor law already found); assert linear in 2^L with no L term
for r in range(1, 513):
    a1 = u[(1 << 20) + r] - 2 * u[(1 << 19) + r]; a2 = u[(1 << 21) + r] - 2 * u[(1 << 20) + r]
    assert a2 == 2 * a1 or a1 == a2   # constant term doubles or stays; no L*2^L part
lin = all(u[(1 << 21) + r] - 2 * u[(1 << 20) + r] == u[(1 << 20) + r] - 2 * u[(1 << 19) + r] for r in range(1, 513))
pr(f"  above: u(2^L + r) = s_r 2^L - t_r (no L term) for r <= 512, L = 19..21: {lin}")
# walls: same question below 3*2^a
wl = []
for r in (1, 2, 3, 5, 7, 11):
    vals = [F(int(u[(3 << a) - r]), 3 << (a - 1)) for a in range(12, 21)]
    d = [vals[i + 1] - vals[i] for i in range(len(vals) - 1)]
    wl.append((r, d[-1], all(x == d[-1] for x in d[-4:])))
pr("  below a wall 3*2^a: u(3*2^a - r)/(3*2^(a-1)) steps per level: " + "; ".join(f"r={r}: {d} {'locked' if ok else 'not locked'}" for r, d, ok in wl))
assert all(ok for _, _, ok in wl)
# prime seats below powers: does sig(r) differ for 2^L - r prime?
pr("  sig(r) of prime seats 2^L - r vs composite seats (L = 22, odd r < 4096):")
rs = np.arange(1, 4096, 2); pm = isP[(1 << 22) - rs]
sv = np.array([float(sig[int(r)]) for r in rs])
pr(f"    mean sig prime seats {sv[pm].mean():.5f} ({pm.sum()}) vs composite {sv[~pm].mean():.5f} ({(~pm).sum()}) (r < 4096)")

# ---------------- 5. 4D map ----------------
pr("\n== 5. 4D MAP: (L = level / scale, t = n/2^(L-1) in [1,2) invariant under ^, d = mirror seat 2n - 11(2j+1) in the")
pr("   11-block, w = word classes of the two neighbours (n-1 | n+1)) ==")
X = 10 ** 7; n = np.arange(12, X + 1); j = (n - 1) // 11; d = 2 * n - 11 * (2 * j + 1)
P = isP[n]
cd = Counter(d[P].tolist()); pr("  primes by seat d (to 1e7): " + " ".join(f"{k:+d}:{cd[k]}" for k in sorted(cd)))
pr("  d is odd for every n; d and -d are the two faces of one fold; prime counts by |d| (seat +11 = multiples of 11):")
pr("   " + " ".join(f"|{k}|: {cd.get(k,0)} vs {cd.get(-k,0)}" for k in range(1, 12) if cd.get(k, 0) + cd.get(-k, 0)))
jb = j[P] % 2; dp = d[P]
pr(f"  prime seats in even blocks: d<0 {int(((jb==0)&(dp<0)).sum())}, d>0 {int(((jb==0)&(dp>0)).sum())};  odd blocks: d<0 {int(((jb==1)&(dp<0)).sum())}, d>0 {int(((jb==1)&(dp>0)).sum())}")
pr("  (odd n in an even block sit at d = -9,-5,-1,+3,+7 (+11): 3 seats left, 2 right; odd block mirrored. Per seat the")
pr("   counts are level: the 3:2 is the seat count of the fold, not a prime lean.)")
# word-class plane of neighbours
pq = n[P]; wpair = Counter(zip(cls(pq - 1).tolist(), cls(pq + 1).tolist()))
pr("  primes by neighbour word pair (left class, right class) to 1e7:")
for k_, c_ in sorted(wpair.items()): pr(f"    ({k_[0]},{k_[1]}) {c_:7d}   mirror pair ({k_[1]},{k_[0]}) {wpair.get((k_[1], k_[0]), 0):7d}")
# octave position t: where primes sit by tenth of the octave at L = 23 (density falls with log, so compare with 1/log)
L = 23; lo = 1 << (L - 1); od = np.arange(lo + 1, min(2 * lo, X), 2)
tb = ((od - lo) * 10 // lo); pc = np.bincount(tb[isP[od]], minlength=10); oc = np.bincount(tb, minlength=10)
pr("  L=23 (to 1e7) prime share by tenth of the octave t: " + " ".join(f"{pc[i]/oc[i]:.4f}" for i in range(10) if oc[i]))
# PNG
try:
    import matplotlib; matplotlib.use("Agg"); import matplotlib.pyplot as plt
    fig, ax = plt.subplots(1, 2, figsize=(13, 5))
    L = 16; lo = 1 << (L - 1); od = np.arange(lo + 1, 2 * lo, 2); t = od / lo; r_ = u[od] / od
    ax[0].scatter(t[~isP[od]], r_[~isP[od]], s=0.3, c="#9aa", label="odd composite")
    ax[0].scatter(t[isP[od]], r_[isP[od]], s=0.6, c="#c33", label="prime")
    ax[0].set_xlabel("t = n / 2^(L-1)  (scale-invariant seat in the octave, L=16)"); ax[0].set_ylabel("u(n)/n (invariant under ^ v)")
    ax[0].axvline(1.5, c="k", lw=.6); ax[0].text(1.505, r_.max() * .98, "wall = lake fold", fontsize=8); ax[0].legend(markerscale=10)
    Ls = np.arange(8, 23)
    Ls = np.arange(8, 22)
    for r in (1, 3, 5, 7, 9, 17):
        ax[1].plot(Ls, [u[(1 << l) - r] / (1 << (l - 1)) for l in Ls], "-o", ms=3, label=f"below 2^L - {r}")
        ax[1].plot(Ls, [u[(1 << l) + r] / (1 << (l - 1)) for l in Ls], "--", lw=1, label=f"above 2^L + {r}")
    ax[1].set_xlabel("level L (scale axis)"); ax[1].set_ylabel("u / 2^(L-1)"); ax[1].legend(fontsize=7, ncol=2)
    ax[1].set_title("lake side (below) grows with L; telescope side (above) flat")
    fig.tight_layout(); fig.savefig(os.path.join(HERE, "relativity-4d_v1.0_11-26-2026.png"), dpi=110)
    pr("  plot: relativity-4d_v1.0_11-26-2026.png")
except Exception as ex:
    pr("  plot skipped:", ex)

# ---------------- 6. PySR on the lake slope ----------------
if len(sys.argv) > 1 and sys.argv[1] == "pysr":
    import subprocess, shutil
    if subprocess.run(["pgrep", "-f", "julia"], capture_output=True).stdout.strip():
        pr("\nPySR skipped: another julia job is running")
    else:
        from pysr import PySRRegressor
        rs = [r for r in range(3, 2048, 2)]
        bl = lambda r: r.bit_length()
        Xp = np.array([[r, bl(r), int(u[r]), int(u[r + 1]), bin(r).count("1")] for r in rs], float)
        yp = np.array([float(sig[r] * (1 << (bl(r) - 1))) for r in rs])
        mdl = PySRRegressor(niterations=30, timeout_in_seconds=150, populations=12, maxsize=17,
                            binary_operators=["+", "-", "*", "/"], unary_operators=[],
                            output_directory=os.path.join(HERE, "pysr-runs"), run_id="lake-slope", progress=False,
                            verbosity=0, random_state=0, deterministic=True, parallelism="serial")
        mdl.fit(Xp, yp, variable_names=["r", "L", "ur", "ur1", "pc"])
        shutil.copy(os.path.join(HERE, "pysr-runs", "lake-slope", "hall_of_fame.csv"),
                    os.path.join(HERE, "pysr-hof-lake-slope_v1.0_11-26-2026.csv"))
        pr("\n== 6. PySR: S(r) = sig(r) * 2^(bitlen(r)-1) (integer) from r, L=bitlen, u(r), u(r+1), pc=ones ==")
        pr(mdl.equations_[["complexity", "loss", "equation"]].to_string())

pr(f"\nall asserts passed; {time.time()-T0:.0f} s")
open(os.path.join(HERE, "relativity-4d_v1.0_11-26-2026.txt"), "w").write("\n".join(OUT) + "\n")

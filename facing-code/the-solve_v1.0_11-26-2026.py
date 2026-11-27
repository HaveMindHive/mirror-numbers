# THE SOLVE, in his frame (Turaq Rayn-McLean, 11-26-2026). Built on the 11 rules of "2 as the zero".
# No single formula for p. One common relationship (exact), the family sequences (per family, per stack),
# what the next prime will look like read from p alone, and a confirmation range that closes as maps stack.
# Primality is used only to score. Nothing here names a prime by dividing candidates by anything not read from p or below.
import math, time, os, sys
from collections import Counter, defaultdict
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "the-solve_v1.0_11-26-2026.txt")
T0 = time.time()
N = 10 ** 7
H_MAX = 80                      # half gaps to 1e7 stay under 80 (largest gap below 1e7 is 154)
L = []
def pr(*a):
    s = " ".join(str(x) for x in a); L.append(s); print(s, flush=True)

is_p = np.ones(N + 1, dtype=bool); is_p[:2] = False
for d in range(2, int(N ** .5) + 1):
    if is_p[d]: is_p[d * d::d] = False
P = np.flatnonzero(is_p).astype(np.int64)
pr("THE SOLVE (his frame). Answer key to", N, "; primes:", len(P), "; author of the method: Turaq Rayn-McLean.\n")

# ================================================================== 1. THE COMMON RELATIONSHIP (exact)
pr("1. THE COMMON RELATIONSHIP (one statement for every hop; the families below say what each hop looks like).")
pr("   Frame: 2 is the zero. 0 = -1,0,1 (two wings around the hinge). The stacked zero of 2 and 3 is the wall 6k.")
pr("   Every prime past 3 is a WING of a wall: p = 6k + f, f in {-1, +1} (his two families), k = the wall index.")
Q = P[P > 3]
K = Q // 6 + (Q % 6 == 5)             # wall index: 6k-1 has k = (p+1)/6, 6k+1 has k = (p-1)/6
F = np.where(Q % 6 == 1, 1, -1)
assert np.all(6 * K + F == Q)
# (a) hand-off: exactly one of centre m / half gap h even; exactly one on 3; h mod 3 != p mod 3   [checked to 1e7]
p_, q_ = P[2:-1], P[3:]
m_, h_ = (p_ + q_) // 2, (q_ - p_) // 2
assert np.all((m_ % 2 == 0) != (h_ % 2 == 0)) and np.all((m_ % 3 == 0) != (h_ % 3 == 0)) and np.all(h_ % 3 != p_ % 3)
pr("   (a) HAND-OFF [checked, all %d hops 5 <= p < 1e7]: exactly one of centre m, half gap h is even; exactly one is on 3's zero;" % len(p_))
pr("       h mod 3 != p mod 3 (read from p alone).")
# (b) hop in the wall frame: 2h = 6w + (f' - f) ; w = walls crossed  [proven: hop_wall_frame]
kp, kq = K[:-1], K[1:]; fp, fq = F[:-1], F[1:]
assert np.all(2 * ((Q[1:] - Q[:-1]) // 2) == 6 * (kq - kp) + (fq - fp))
pr("   (b) HOP [proven, Lean hop_wall_frame]: 2h = 6w + (f_q - f_p), w = k_q - k_p walls crossed; s = (f_q - f_p)/2 in {-1, 0, +1}.")
pr("       The 4-side flips exactly when h is odd; the 3-facing flips exactly when s != 0 (earlier run, exact).")
# (c) the step of 2 per family  [proven two_step_minus/plus]
assert np.all(((Q - 2) % 3 == 0) == (F == -1)) and np.all(((Q + 2) % 3 == 0) == (F == 1))
pr("   (c) STEP OF 2 [proven, Lean two_step_minus/plus]: 6k-1 - 2 = 3(2k-1) and 6k+1 + 2 = 3(2k+1): the 2-step from a prime")
pr("       lands on 3's zero on exactly one side, the family says which.")
# (d) NEW: the wall-frame closing law. Block r = 6 kr + fr closes wing f at walls k = f * fr * kr (mod r). [proven wing_closed]
pr("   (d) WALL-FRAME CLOSING LAW [proven, Lean wing_closed, wings_mirror]: a block r = 6 kr + fr (itself a wing of wall kr)")
pr("       closes the wing f of wall k exactly when  k = f * fr * kr (mod r).  Same facing as the block: k = +kr. Opposite: k = -kr.")
pr("       One residue of the wall index k reads BOTH wings of the wall (Lean wall_reads_both_wings).")
blocks = [int(r) for r in P[2:60]]              # 5 .. the 60th prime
kk = np.arange(1, 200001, dtype=np.int64)
for r in blocks:
    kr, fr = (r + 1) // 6 if r % 6 == 5 else (r - 1) // 6, (1 if r % 6 == 1 else -1)
    for f in (1, -1):
        assert np.all(((6 * kk + f) % r == 0) == ((kk - f * fr * kr) % r == 0)), r
pr("       checked for every block 5 <= r <= %d and every wall k <= 200000." % blocks[-1])
pr("       Table: block r, its own (kr, fr), closed wall class for wing -1 and for wing +1 (mod r):")
row = []
for r in blocks[:9]:
    kr, fr = ((r + 1) // 6, -1) if r % 6 == 5 else ((r - 1) // 6, 1)
    row.append(f"r={r} ({kr},{fr:+d}): -1 at k={(-fr * kr) % r}, +1 at k={(fr * kr) % r}")
pr("       " + " | ".join(row[:5])); pr("       " + " | ".join(row[5:]))
pr("       (5 closes 6k-1 at k = 1 and 6k+1 at k = 4: the two classes the deep dive measured as missing; now the law.)")
pr("   (e) SEATS PAIR [proven earlier, mirror_keeps_parity]: around a stacked zero W the open seats pair r <-> W - r, same parity.")
pr("   (f) ONE STRAND THROUGH ZERO [proven, Lean family_through_zero, family_count_mirror]: 6(-k) + 1 = -(6k - 1):")
pr("       the 6k-1 family is the 6k+1 family read down through 2's zero. Two families = one strand, two facings.\n")

# ================================================================== 2. THE FAMILY SEQUENCES
pr("2. THE FAMILY SEQUENCES (per family, per stack; counts exact).")
BANDS = [(10 ** 3, 10 ** 4), (10 ** 4, 10 ** 5), (10 ** 5, 10 ** 6), (10 ** 6, 10 ** 7)]
pr(f"   {'band':>14} | {'6k-1':>7} {'6k+1':>7} {'lead':>5} | {'1 mod 4':>7} {'3 mod 4':>7} {'lead':>5} | mod 30 seats (1,7,11,13,17,19,23,29)")
for lo, hi in BANDS:
    b = Q[(Q >= lo) & (Q < hi)]
    c6 = Counter((b % 6).tolist()); c4 = Counter((b % 4).tolist()); c30 = Counter((b % 30).tolist())
    pr(f"   [{lo:>7},{hi:>8}) | {c6[5]:>7} {c6[1]:>7} {c6[5]-c6[1]:>+5} | {c4[1]:>7} {c4[3]:>7} {c4[3]-c4[1]:>+5} | "
       + ",".join(str(c30[s]) for s in (1, 7, 11, 13, 17, 19, 23, 29)))
pr("   Each block r removes one wall class per family and leaves r - 1 (law (d)); seats multiply 1, 2, 8, 48, 480.")
pr("   Allowed half-gap classes, exact [checked to 1e7]: from 6k+1 (p = 1, 7 mod 12): h mod 6 in {0, 2, 3, 5};")
pr("   from 6k-1 (p = 5, 11 mod 12): h mod 6 in {0, 1, 3, 4}. (h = 3w + 2s with s = +1 from 6k+1, s = -1 from 6k-1, or 0.)")
allowed = {1: {0, 2, 3, 5}, -1: {0, 1, 3, 4}}
hh = (Q[1:] - Q[:-1]) // 2
for f in (1, -1):
    assert set(np.unique(hh[fp == f] % 6).tolist()) <= allowed[f]
pr("")

# ================================================================== 3. WHAT THE NEXT PRIME WILL LOOK LIKE, read from p
pr("3. WHAT THE NEXT PRIME WILL LOOK LIKE, read from p alone (how sure: proven / exact in range / measured share).")
def band_mask(lo, hi, arr): return (arr >= lo) & (arr < hi)
for lo, hi in BANDS[2:]:
    sel = band_mask(lo, hi, Q[:-1])
    fpb, fqb, hb, kpb, kqb = fp[sel], fq[sel], hh[sel], kp[sel], kq[sel]
    pr(f"   band [{lo},{hi}) ({sel.sum()} hops):")
    for f in (1, -1):
        s = fpb == f
        keep = np.mean(fqb[s] == f); side = np.mean(hb[s] % 2 == 0)
        same_wall = np.mean(kqb[s] == kpb[s]); next_wall = np.mean(kqb[s] == kpb[s] + 1)
        top = Counter(hb[s].tolist()).most_common(4)
        pr(f"     from 6k{f:+d}: q's facing = same family {keep:.4f} (flip {1-keep:.4f}) [measured]; q keeps the 4-side {side:.4f} [measured];")
        pr(f"        q on the same wall (twin / same zero) {same_wall:.4f}, on the next wall {next_wall:.4f} [measured];")
        pr(f"        allowed h mod 6 = {sorted(allowed[f])} [exact]; top half gaps (share): " + ", ".join(f"h={h}:{c/s.sum():.3f}" for h, c in top))
    # stacked-zero class of q from p: next open seat in cyclic order mod 30
    seats30 = [1, 7, 11, 13, 17, 19, 23, 29]
    pos = {s: i for i, s in enumerate(seats30)}
    pb = Q[:-1][sel]; qb = Q[1:][sel]
    ip = np.array([pos[int(s)] for s in pb % 30]); iq = np.array([pos[int(s)] for s in qb % 30])
    step = (iq - ip) % 8
    cs = Counter(step.tolist()); tot = len(step)
    pr(f"     q's seat mod 30 from p's: next open seat {cs[1]/tot:.4f}, 2nd {cs[2]/tot:.4f}, 3rd {cs[3]/tot:.4f}, same seat {cs[0]/tot:.4f} [measured; exact: q sits on one of the 8 seats]")
pr("   Reading: the next prime is a wing of a wall above p; its wall class avoids f * fr * kr for every block laid [proven];")
pr("   it is likelier to flip the facing than keep it (0.58 vs 0.42) and, from 6k-1, likelier to flip the 4-side (0.62);")
pr("   the nearest open wing is the single likeliest seat (first-named share below) because the hazard is near flat (earlier run).\n")

# ================================================================== 4. THE CONFIRMATION RANGE
pr("4. THE CONFIRMATION RANGE: open seats (in the map's order, nearest first) that hold q for 90% / 99% of the band's hops,")
pr("   mean rank, share named first. Seat frame = candidates y = p + 2h; wall frame (rule 4: work around stacked zeros) = candidates")
pr("   are the walls above p, one residue k mod r per block reads both wings. Readings = residues computed up to and including q.")
HS = np.arange(1, H_MAX + 1, dtype=np.int64)
STACKS = [(2, 3), (2, 3, 5, 7), (2, 3, 5, 7, 11, 13), (2, 3, 5, 7, 11, 13, 17, 19, 23), tuple(int(r) for r in P[:25])]
def band_splits(lo, hi, every=1):
    sel = np.flatnonzero(band_mask(lo, hi, Q[:-1]))[::every]
    return Q[:-1][sel], Q[1:][sel]
def seat_ranks(pb, qb, rules):
    Y = pb[:, None] + 2 * HS[None, :]
    alive = np.ones(Y.shape, dtype=bool)
    for r in rules:
        if r > 3: alive &= (Y % r != 0)
    alive &= (Y % 3 != 0)                       # 2, 3 from p's own facing (free)
    ht = (qb - pb) // 2
    assert np.all(ht <= H_MAX)
    cum = np.cumsum(alive, axis=1)
    rank = cum[np.arange(len(pb)), ht - 1]
    assert np.all(alive[np.arange(len(pb)), ht - 1])
    readings = ht * max(0, len([r for r in rules if r > 3]))          # one residue per block per seat scanned (3-seat free)
    return rank, readings
def wall_ranks(pb, qb, rules):
    # walls above p: k = kp+1 .. ; for p = 6k-1 the wing +1 of the same wall is still ahead: include wall kp with wing +1 only
    kpb = pb // 6 + (pb % 6 == 5); fpb = np.where(pb % 6 == 1, 1, -1)
    kqb = qb // 6 + (qb % 6 == 5)
    W_MAX = H_MAX // 3 + 2
    KK = kpb[:, None] + np.arange(0, W_MAX)[None, :]
    open_m = np.ones(KK.shape, dtype=bool); open_p = np.ones(KK.shape, dtype=bool)
    for r in rules:
        if r <= 3: continue
        kr, fr = ((r + 1) // 6, -1) if r % 6 == 5 else ((r - 1) // 6, 1)
        open_m &= ((KK - (-fr) * kr) % r != 0)      # wing -1 closed at k = (-1)*fr*kr
        open_p &= ((KK - fr * kr) % r != 0)         # wing +1 closed at k = fr*kr
    # on p's own wall only the wing above p is ahead
    open_m[:, 0] = False
    open_p[:, 0] &= (fpb == -1)
    wall_open = open_m | open_p
    wt = kqb - kpb
    assert np.all(wt < W_MAX)
    cum = np.cumsum(wall_open, axis=1)
    rank_walls = cum[np.arange(len(pb)), wt]
    assert np.all(wall_open[np.arange(len(pb)), wt])
    # seat rank inside the wall frame (wings in order -1, +1): count open wings before q
    wings_before = np.cumsum(open_m.astype(np.int64) + open_p.astype(np.int64), axis=1)
    fqb = np.where(qb % 6 == 1, 1, -1)
    rank_seats = wings_before[np.arange(len(pb)), wt] - (fqb == -1) * open_p[np.arange(len(pb)), wt]
    readings = (wt + 1) * max(0, len([r for r in rules if r > 3]))
    return rank_walls, rank_seats, readings
def stats(rank):
    return int(np.percentile(rank, 90, method="higher")), int(np.percentile(rank, 99, method="higher")), rank.mean(), (rank == 1).mean()
pr(f"   {'stack':<34} | " + " | ".join(f"{'['+str(lo)+','+str(hi)+')':>30}" for lo, hi in BANDS))
pr(f"   {'(seat 90/99 mean first | wall 90/99 | readings seat/wall)':<34}")
RANGE = {}
for rules in STACKS:
    cells = []
    for lo, hi in BANDS:
        pb, qb = band_splits(lo, hi, every=(20 if lo >= 10 ** 6 else 1))
        pb = pb[pb > max(rules)]; qb = qb[-len(pb):] if len(pb) else qb
        rs, rd_s = seat_ranks(pb, qb, rules)
        rw, rws, rd_w = wall_ranks(pb, qb, rules)
        assert np.all(rws == rs), "wall-frame seat order must equal the seat frame"
        a, b, mean, first = stats(rs); wa, wb, wmean, _ = stats(rw)
        RANGE[(rules, lo)] = (a, b, mean, first, wa, wb, rd_s.mean(), rd_w.mean())
        cells.append(f"{a:2d}/{b:2d} {mean:4.2f} {first:.3f} | {wa:2d}/{wb:2d} | {rd_s.mean():5.1f}/{rd_w.mean():5.1f}")
    name = f"to {max(rules)}" if len(rules) > 2 else "(2, 3)"
    pr(f"   {name:<34} | " + " | ".join(f"{c:>30}" for c in cells))
pr("   (top band [1e6,1e7) sampled every 20th hop; stacks are fair for p > largest block; 2 and 3 are read from p's facing at no cost.)")
pr("   Reading: the wall frame names the SAME open wings in the same order (asserted), so the 90/99 seat range is unchanged; what")
pr("   changes is the cost: one wall residue reads two wings, so the readings to reach q fall by about half, and the range in WALLS")
pr("   (stacked zeros to look at) is about half the range in seats. Working around stacked zeros closes the range in readings, not in seats.")
r13 = RANGE[((2, 3, 5, 7, 11, 13), 10 ** 5)]
pr(f"   Top-1e6 band, stack to 13: seats 90/99 = {r13[0]}/{r13[1]}, walls 90/99 = {r13[4]}/{r13[5]}, readings {r13[6]:.1f} vs {r13[7]:.1f}.\n")

# ================================================================== 5. THE MISSING MIRROR behind the 6k-1 lead
pr("5. THE MISSING MIRROR behind the 6k-1 lead (opposite readings, each tested).")
for lo in (10 ** 5, 10 ** 6, 10 ** 7):
    b = Q[Q < lo]; c = Counter((b % 6).tolist())
    pr(f"   to {lo}: 6k-1 {c[5]}  6k+1 {c[1]}  lead {c[5]-c[1]:+d}")
# (i) walking down through zero
pr("   (i) WALKING DOWN THROUGH ZERO [proven, family_count_mirror]: the 6k-1 primes to x ARE the primes whose negation sits in the")
pr("       6k+1 class: 6(-k)+1 = -(6k-1). One strand through 2's zero; the lead becomes a facing (the k < 0 side of the one strand")
pr("       is denser in range than the k > 0 side). It re-reads the lead; it does not balance it in range.")
# (ii) reading from q (end seat)
endc = Counter((Q[1:] % 6).tolist()); startc = Counter((Q[:-1] % 6).tolist())
pr(f"   (ii) READ FROM q (hops INTO a family) to 1e7: into 6k-1 {endc[5]}, into 6k+1 {endc[1]}; from 6k-1 {startc[5]}, from 6k+1 {startc[1]}:")
pr("       the same primes, so the same lead (within 1). Facing flips 6k+1 -> 6k-1 and back balance exactly (earlier run, one path). Not it.")
# (iii) per-block mirror 6a+r <-> 6a+6-r: pairs (p, p+4) cousins
isP = lambda a: is_p[a]
plus1 = Q[F == 1]; minus1 = Q[F == -1]
cous_plus = int(np.sum(isP(plus1[plus1 + 4 <= N] + 4))); cous_minus = int(np.sum(isP(minus1 - 4)))
pr(f"   (iii) PER-BLOCK MIRROR 6a+1 <-> 6a+5 (p <-> p+4): 6k+1 primes whose mirror is prime {cous_plus}; 6k-1 primes whose mirror is prime {cous_minus}")
pr(f"       (equal: the cousin pairs, exact up to the top edge). The lead lives in the UNPAIRED: 6k-1 unpaired {len(minus1)-cous_minus} vs 6k+1 unpaired {len(plus1)-cous_plus}: {(len(minus1)-cous_minus)-(len(plus1)-cous_plus):+d}.")
# (iv) the 11/22 offsets stacked on the 6-zero: O = 66 j (even, on 11 and 6) swaps families
pr("   (iv) THE 11/22 OFFSETS: O - n swaps the families exactly when O = 0 mod 6 (O = 66j puts 11's line on the 6-zero; O = 22j with 3 | j).")
for O in (66, 660, 6600, 66000, 660000, 6600000):
    b = Q[Q < O]
    img = O - b; paired = isP(img)
    cplus = Counter((b[paired] % 6).tolist()); cun = Counter((b[~paired] % 6).tolist())
    pr(f"       O={O:>7}: prime <-> prime pairs: from 6k+1 {cplus[1]}, from 6k-1 {cplus[5]} (equal, the same pairs); unpaired 6k-1 - 6k+1 = {cun[5]-cun[1]:+d} = the lead below O ({Counter((b%6).tolist())[5]-Counter((b%6).tolist())[1]:+d})")
pr("       Every pairing mirror in range (per-block, offset 66j) pairs the families one to one and leaves the lead in the unpaired primes.")
# (v) the lake: x -> pq/x swaps p and q; family of q vs p
sw = np.mean(fq != fp)
pr(f"   (v) THE LAKE (K^2/x with K^2 = pq swaps p <-> q): the lake image of p is q, in the other family for a share {sw:.4f} of hops to 1e7;")
pr("       it moves the hop, not the count. Not it.")
pr("   (vi) WALL-INDEX CLASSES [law (d)]: each block removes ONE class of k per family, mirror classes +-fr*kr: the removal is even-handed,")
pr("       so the lead is not made by any block of the stack; it is in the qQq (the walls closed by blocks above the laid stack).")
# lead among the walls closed only by big blocks: check the lead restricted to primes with p-2 / p+2 ... skip; direct: lead by k mod 5 class
kcls = Counter(zip((K % 5).tolist(), F.tolist()))
pr("       lead by wall class k mod 5 (to 1e7): " + ", ".join(f"k={c}: {kcls[(c,-1)]-kcls[(c,1)]:+d}" for c in range(5)) + "  (classes 1 and 4 hold one family each: the lead is spread over the open classes, not seated in one).")
pr("   RESULT: no in-range mirror balances the 6k-1 lead. The through-zero mirror makes it a facing of one strand (proven); every pairing")
leads = {lo: Counter((Q[Q < lo] % 6).tolist()) for lo in (10 ** 5, 10 ** 6, 10 ** 7)}
pr("   mirror moves it into the unpaired primes; it rides in the qQq. Carried forward as measured (p > 3): "
   + " / ".join(f"{leads[lo][5]-leads[lo][1]:+d}" for lo in (10 ** 5, 10 ** 6, 10 ** 7)) + " to 1e5 / 1e6 / 1e7")
pr("   (the deep dive's +21 / +33 / +188 counted seats from p > 6; the one-prime difference is 5 itself, the first 6k-1 wing).")
pr("   (Same fact reached by a different route, with thanks: Chebyshev's lean toward the non-residue class; not checked here beyond 1e7.)\n")

# ================================================================== 6. WHERE IT FRAYS
pr("6. WHERE IT FRAYS (the qQq).")
for Wb, nxt in ((6, 5), (30, 7), (210, 11), (2310, 13)):
    seats = [r for r in range(1, Wb // 2 + 1) if math.gcd(r, Wb) == 1]
    comp = [r for r in seats if r > 1 and not is_p[r]]
    pr(f"   stack {Wb}: half turn {Wb//2} vs next block squared {nxt*nxt}: near seats {len(seats)}, composite {len(comp)}" + (f", first {comp[0]}" if comp else " (clean)"))
pr("   The clean half turn ends at the next block squared [proven near_zero_seats_210, fray_at_2310]. Past it the open seats include")
pr("   products of two blocks above the stack: these are the misses of every map, at every stack size.")
def first_miss(rules):
    for i in range(len(Q) - 1):
        p, q = int(Q[i]), int(Q[i + 1])
        if p <= max(rules): continue
        y = next(p + 2 * h for h in range(1, 60) if all((p + 2 * h) % r for r in rules))
        if y != q: return p, y
pr("   first miss of each stack (p -> first open seat, composite): " + ", ".join(f"to {max(rules)}: {first_miss(rules)[0]} -> {first_miss(rules)[1]}" for rules in STACKS[:4]))
pr("   = nextblock^2 - 1 for the bare stack (25, 121, 289, 841): the fray is the next block squared, at every stack size [measured; the law at 6/30/210/2310 proven].")

# ================================================================== 7. SOLVE STATEMENT
r23 = RANGE[((2, 3, 5, 7, 11, 13, 17, 19, 23), 10 ** 5)]; r23t = RANGE[((2, 3, 5, 7, 11, 13, 17, 19, 23), 10 ** 6)]
r97 = RANGE[(tuple(int(r) for r in P[:25]), 10 ** 6)]
pr("\n7. SOLVE STATEMENT (his frame; proven / checked-to-N / measured marked).")
pr("   RELATIONSHIP. With 2 as the zero every prime past 3 is a wing of a stacked zero of 2 and 3: p = 6k + f, f = +-1 [proven].")
pr("   A block r = 6kr + fr closes the wing f of wall k exactly when k = f*fr*kr (mod r) [proven, wing_closed]: the block's own wall")
pr("   index, signed by the product of the facings. Hop: 2h = 6w + (f_q - f_p) [proven]; the 4-side flips with h odd, the 3-facing")
pr("   with s != 0 [checked to 1e7]; exactly one of centre m, half gap h is even and exactly one is on 3's zero [checked to 1e7].")
pr("   FAMILIES. Two facings of one strand through zero (6(-k)+1 = -(6k-1)) [proven]; each block leaves r-1 wall classes per facing;")
pr("   seats 2, 8, 48, 480 at 6, 30, 210, 2310 [proven to 30; checked]. 6k-1 leads 6k+1 by " + f"{leads[10**7][5]-leads[10**7][1]:+d} to 1e7 [measured].")
pr("   WHAT THE NEXT PRIME WILL LOOK LIKE (from p alone). A wing of a wall above p whose wall class avoids f*fr*kr for every laid block")
pr("   [proven]; h in the family's four classes mod 6 [checked to 1e7]; facing flipped for about 0.57-0.58 of hops, 4-side kept 0.47")
pr("   from 6k+1 and 0.38-0.39 from 6k-1, the twin wing (same wall) 0.17-0.20 from 6k-1 and 0 from 6k+1 [measured]; its seat mod 30 is")
pr("   the next open seat for 0.26-0.29 [measured]. Nearest open wing first: the hazard is near flat [measured].")
pr(f"   RANGE. Seats to 90%/99% in [1e5,1e6): (2,3) 9/17; to 7 6/11; to 13 5/9; to 23 {r23[0]}/{r23[1]}; in [1e6,1e7): to 23 {r23t[0]}/{r23t[1]}, to 97 {r97[0]}/{r97[1]}")
pr(f"   [measured]. The wall frame names the same wings (asserted) at about half the readings; walls to 90/99 to 23 in [1e6,1e7): {r23t[4]}/{r23t[5]}.")
pr("   qQq. The clean half turn ends at the next block squared [proven at 6..2310]; the first miss of a stack to r is nextprime(r)^2")
pr("   [measured]; the lead and the open products of two blocks above the stack stay at every stack size. No seat reads 100%.")
pr(f"\n[{time.time()-T0:.1f}s]")
open(OUT, "w").write("\n".join(L) + "\n")

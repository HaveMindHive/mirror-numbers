# Two as the zero (tUrUq, 11-26-2026): "2 is like 0. its the only common prime" / "2 is the 0 of primes both odd and even".
# Measures, exactly and per family, what primes do when 2 is read as a zero: re-centred frames, each prime's own zero
# next to 2's zero, stacked zeros (6, 30, 210, 2310 ...), the odd <-> even mirror through 2, and where it frays.
# Primality is used only to score (an answer key to LIMIT); nothing here names a prime by dividing candidates.
# Imports the unified code (w, c, w) from this folder without changing it.
import importlib.util, math, sys, time
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
LIMIT = 10_000_000
OUT = HERE / "two-zero_v1.0_11-26-2026.txt"

def load(name):
    spec = importlib.util.spec_from_file_location(name.replace("-", "_"), HERE / f"{name}_v1.0_11-26-2026.py")
    m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m

uc = load("unified-code")

def prime_key(n):
    s = bytearray([1]) * (n + 1); s[0] = s[1] = 0
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]: s[i * i::i] = bytearray(len(s[i * i::i]))
    return s

t0 = time.time()
S = prime_key(LIMIT)
P = [i for i in range(LIMIT + 1) if S[i]]
isp = lambda n: 0 <= n <= LIMIT and S[n] == 1
lines = []
def say(*a):
    s = " ".join(str(x) for x in a); lines.append(s); print(s)

say("TWO AS THE ZERO (tUrUq, 11-26-2026). Answer key to", LIMIT, "; primes:", len(P))
say("")
# ---------------------------------------------------------------- A. the picture
say("A. THE PICTURE. 0 halves into -1,0,1 (his two zeros: absence, nothingness, absence); 2 = 1,0,1.")
say("   Same picture: the wings cancel as facings (-1 + 1 = 0) and count as units (|-1| + |1| = 2). 2 is 0 with its wings counted.")
assert uc.write(2, 1) == "1,0,1" and uc.write(0, 1) == "0,0,0"
assert (-1) + 0 + 1 == 0 and abs(-1) + abs(0) + abs(1) == 2
hinge = [p for p in P if p % 2 == 0]
assert hinge == [2], hinge
say("   Primes with hinge centre (w,0,w) to", LIMIT, ":", hinge, "; every other prime is w,1,w (unit centre): checked.")
say("   Measured from 2's mirror (mod 2) every odd prime reads 1: the whole odd prime line is one seat, the unit. 2 is its zero.")
say("   2 = |0,(1): the first gap mirror with the unit behind it; 3 = |2,(1): the first unit-centred mirror. 1 | 3 are 2's two observers.")
say("")
# ---------------------------------------------------------------- B. re-centred frames
say("B. RE-CENTRED FRAMES, first primes. index0 = place in the prime list with 2 as zero (3 -> 1, 5 -> 2, 7 -> 3: his 1, 2, 3 of odd primes).")
say("   p-2 = p measured from 2; p/2 = seat on the even line (odd p sits BETWEEN places w|w+1; 2p sits AT place p); fam = p mod 6.")
say(f"   {'p':>4} {'index0':>6} {'p-2':>5} {'(p-2)/2':>8} {'even-line seat':>15} {'w,c,w':>9} {'fam':>4} {'p-2 on 3-zero':>13} {'p+2 on 3-zero':>13}")
for i, p in enumerate(P[:26]):
    seat = f"{p//2}|{p//2+1}" if p % 2 else f"place {p//2}"
    say(f"   {p:>4} {i:>6} {p-2:>5} {(p-2)/2:>8} {seat:>15} {uc.write(p,1):>9} {p%6:>4} {str((p-2)%3==0):>13} {str((p+2)%3==0):>13}")
# p -+ 2 lands on 3's zero per family: exact
fam5 = [p for p in P if p > 3 and p % 6 == 5]; fam1 = [p for p in P if p > 3 and p % 6 == 1]
assert all((p - 2) % 3 == 0 for p in fam5) and all((p + 2) % 3 == 0 for p in fam1)
assert not any((p + 2) % 3 == 0 for p in fam5) and not any((p - 2) % 3 == 0 for p in fam1)
say(f"   Family 6k-1 ({len(fam5)} primes to {LIMIT}): p-2 is on 3's zero in every case, p+2 never in range.")
say(f"   Family 6k+1 ({len(fam1)} primes to {LIMIT}): p+2 is on 3's zero in every case, p-2 never in range.")
say("   So the step of 2 (2 as the unit of the gap line) from a prime lands on 3's zero on exactly one side; the family says which. Mirror pair.")
twins = [p for p in P if p > 3 and isp(p + 2)]
assert all((p + 1) % 6 == 0 for p in twins)
say(f"   Twin pairs above 3 to {LIMIT}: {len(twins)}; centre p+1 is a stacked zero of 2 and 3 (6k) in every case (Lean twin_straddles_wall).")
for X in (10**5, 10**6, 10**7):
    say(f"     twins to {X}: {sum(1 for p in twins if p + 2 <= X)}; 6k with both sides prime share: {sum(1 for p in twins if p+2<=X)}/{X//6}")
say("")
# ---------------------------------------------------------------- C. stacked zeros
say("C. STACKED ZEROS. 2's zero stacks with 3 at 6, with 3,5 at 30, with 3,5,7 at 210, with 3,5,7,11 at 2310.")
say("   Open seats mod W = numbers coprime to W; they come in mirror pairs r <-> W-r (2 in the stack: same parity, never self-mirror).")
walls = [(2, [2]), (6, [2, 3]), (30, [2, 3, 5]), (210, [2, 3, 5, 7]), (2310, [2, 3, 5, 7, 11]), (30030, [2, 3, 5, 7, 11, 13])]
for W, blocks in walls:
    seats = [r for r in range(1, W) if math.gcd(r, W) == 1]
    near = [r for r in seats if r <= W // 2]
    comp = [r for r in near if r != 1 and not isp(r)]
    if W == 2:
        assert seats == [1]
        say("   W=    2 blocks [2]: one seat, 1, and it is its own mirror (2 - 1 = 1): the lone 2-zero has no partner seat; the unit faces itself.")
        continue
    assert all((W - r) in seats and (W - r) != r and (W - r) % 2 == 1 for r in seats)
    say(f"   W={W:>5} blocks {blocks}: seats {len(seats)} (= prod (r-1) = {math.prod(b-1 for b in blocks)}), mirror pairs {len(seats)//2};"
        f" seats within half a turn: {len(near)}; of these 1 + primes: {len(near)-len(comp)}, composite: {len(comp)}"
        + (f" first composite {comp[0]} = {comp[0]} ({[q for q in P if comp[0] % q == 0]})" if comp else " (all 1 or prime)"))
    if W <= 210:
        say(f"          near seats: {near}")
        assert not comp
    if W == 2310:
        assert comp[0] == 169
        say(f"          composite near seats at 2310: {comp}")
say("   Law (exact): the half turn W/2 stays below the next block squared for W = 6 (3 < 25), 30 (15 < 49), 210 (105 < 121); at 2310, 1155 > 169. That is the fray.")
say("")
say("   Primes per seat (exact counts), mirror imbalance r vs W-r, and the 6k-1 / 6k+1 lead:")
for W in (6, 30, 210):
    for X in (10**5, 10**6, 10**7):
        c = Counter(p % W for p in P if p > W and p <= X)
        seats = sorted(c)
        imb = max(abs(c[r] - c[W - r]) for r in seats)
        worst = max(seats, key=lambda r: abs(c[r] - c[W - r]))
        lead_minus = sum(c[r] for r in seats if r > W // 2) - sum(c[r] for r in seats if r < W // 2)
        say(f"     W={W:>3} to {X:>8}: min seat {min(c.values())}, max seat {max(c.values())}, largest mirror imbalance {imb} at ({worst},{W-worst})"
            f" = {c[worst]} vs {c[W-worst]}; upper-half (W-r side) minus lower-half: {lead_minus:+d}")
    if W == 6:
        say(f"          6k-1 vs 6k+1 to {LIMIT}: {sum(1 for p in P if p%6==5)} vs {sum(1 for p in P if p%6==1)} (p > 3)")
    if W == 30:
        c = Counter(p % 30 for p in P if p > 30)
        say("          mod 30 seats to", LIMIT, ":", dict(sorted(c.items())))
say("   Reading: mirror seats r, W-r hold near-equal counts (imbalance under 0.1% of a seat at 1e7). At W=6 the 6k-1 seat leads in all three bands;")
say("   at W=30 and 210 the leading side changes between bands (+8/-12/+5; -32/-198/-191): no fixed side. The 6-lean is the one asymmetry that held in range (a mirror still to find).")
say("")
# around a stacked zero: what is beside it
say("   AROUND A STACKED ZERO Wk: share of Wk with a prime at Wk-1, Wk+1, both, neither; mean distance to the nearest prime.")
def nearest(n):
    d = 1
    while not (isp(n - d) or isp(n + d)): d += 1
    return d
for W in (6, 30, 210, 2310):
    ks = range(1, LIMIT // W)
    minus = plus = both = neither = 0; dist = 0
    for k in ks:
        n = W * k; a = isp(n - 1); b = isp(n + 1)
        minus += a; plus += b; both += a and b; neither += (not a) and (not b); dist += nearest(n)
    N = len(ks)
    say(f"     W={W:>4}: N={N}, Wk-1 prime {minus} ({minus/N:.4f}), Wk+1 prime {plus} ({plus/N:.4f}), both {both} ({both/N:.4f}), neither {neither} ({neither/N:.4f}), mean nearest dist {dist/N:.4f}")
# control: evens off the 3-zero (2m with 3 not dividing m) only ever have one open side
ctrl = [2 * m for m in range(2, LIMIT // 2) if m % 3][:LIMIT // 6]
minus = sum(isp(n - 1) for n in ctrl); plus = sum(isp(n + 1) for n in ctrl); both_l = [n for n in ctrl if isp(n - 1) and isp(n + 1)]
assert both_l == [4]
say(f"     control 2m off the 3-zero (same count N={len(ctrl)}): 2m-1 prime {minus}, 2m+1 prime {plus}, both {len(both_l)} = {both_l}: one side sits on 3's zero, so no pair,")
say("       except 4 = 2's zero stacked with itself, whose 3-zero neighbour IS the prime 3 (3 | 4 | 5: his '4 is the 2 of primes').")
say("     So the +-1 pair (twins) lives only around stacked zeros of 2 and 3: a stacked zero opens both wings; a lone 2-zero opens one.")
# mod 30 pairs around 30k
pairs30 = [(1, 29), (7, 23), (11, 19), (13, 17)]
full = Counter()
for k in range(1, LIMIT // 30):
    n = 30 * k
    full[sum(1 for a, b in pairs30 if isp(n - 30 + b) and isp(n + a))] += 1  # pair (a, W-a): seats n+a and n-a... use symmetric seats around n
# redo cleanly: symmetric seats around n are n - r and n + r for r in {1,7,11,13}
full = Counter(); per_r = Counter()
for k in range(1, LIMIT // 30):
    n = 30 * k; m = 0
    for r in (1, 7, 11, 13):
        a = isp(n - r) and isp(n + r); m += a; per_r[r] += a
    full[m] += 1
say(f"     Around 30k (N={LIMIT//30 - 1}): symmetric prime pairs n-r, n+r completed per r: {dict(per_r)}; stacked zeros with 0,1,2,3,4 completed pairs: {dict(sorted(full.items()))}")
say("")
# ---------------------------------------------------------------- D. each prime's own zero next to 2's
say("D. EACH PRIME'S OWN ZERO. p sits on its own zero (p = 0 mod p). 2's zero and p's zero stack first at 2p = the even prime E1.")
for p in P[1:12]:
    between = [q for q in P if p < q < 2 * p]
    say(f"     p={p:>3}: own zero at {p}, stack with 2 at {2*p}; primes between the two zeros: {between} ({len(between)})")
mn = min((sum(1 for q in P[i+1:] if q < 2 * p), p) for i, p in enumerate(P) if p <= 10**5)
say(f"     Fewest primes between p and 2p for p <= 1e5: {mn[0]} (at p = {mn[1]}); in range the count stays >= 1 (same fact by a different route: Bertrand).")
say("   E1 = 2p is the odd prime line one zoom up (gaps 2x): on the even line with 2 as its 1, the primes are the places p. 2 reads as 0 (number line) and 1 (even line): his 0/1 two-face.")
e2 = [n for n in range(6, 400, 4)]  # 2 mod 4
assert all(n % 4 == 2 for n in e2)
say("   E2 (2 mod 4) = one 2-zero with an odd core: exactly one gap mirror |0 then odd. 4 = 2's zero stacked with itself (his '4 is the 2 of primes').")
say("")
# ---------------------------------------------------------------- E. the hop in 2-units
say("E. THE GAP LINE. Every gap between odd primes is a multiple of 2: 2 is the unit of the gap line (h = g/2 = the place on the even line).")
H = Counter(); side_keep = Counter()
for i in range(2, len(P) - 1):
    p, q = P[i], P[i + 1]
    if q > 10**6: break
    h = (q - p) // 2; H[h % 2] += 1
assert H[0] + H[1] == sum(1 for i in range(2, len(P)-1) if P[i+1] <= 10**6)
say(f"   Splits 5..1e6: h even (gap 0 mod 4, 4-side kept) {H[0]}, h odd (gap 2 mod 4, 4-side flips) {H[1]}.")
h_mod3 = Counter(((P[i+1]-P[i])//2) % 3 for i in range(2, len(P)-1) if P[i+1] <= 10**6)
say(f"   h mod 3 to 1e6: {dict(sorted(h_mod3.items()))} (h = 0 mod 3 keeps the 6k+-1 facing; the two flips are near-equal: the hop's own frame is the mirror).")
say("")
# ---------------------------------------------------------------- F. families measured from the stacked zero 6
say("F. FAMILIES FROM THE 6-ZERO. Write p = 6k + f, f in {-1, +1}: k = the wall index. Per family, which k appear (first 40):")
k5 = [(p + 1) // 6 for p in fam5]; k1 = [(p - 1) // 6 for p in fam1]
say("   6k-1:", k5[:40]); say("   6k+1:", k1[:40])
both_k = sorted(set(k5) & set(k1))
say(f"   k in both families = twin centres: {both_k[:30]} ...; k in neither to 1e3: {[k for k in range(1,1000) if k not in set(k5) and k not in set(k1)][:30]} ...")
say("   k mod 5 per family (5's zero seen from the 6-zero), to", LIMIT, ":")
say("     6k-1:", dict(sorted(Counter(k % 5 for k in k5).items())), " (k = 1 mod 5 -> p = 6k-1 = 5 mod 5... p on 5's zero: excluded; it is the missing class)")
say("     6k+1:", dict(sorted(Counter(k % 5 for k in k1).items())), " (k = 4 mod 5 excluded)")
assert 1 not in Counter(k % 5 for k in k5 if k > 1) and 4 not in Counter(k % 5 for k in k1 if k > 1)
say("   Each block r added to the stack removes one class of k per family and leaves r-1: 5 leaves 4 of 5, 7 leaves 6 of 7. Seats multiply by (r-1): 1, 2, 8, 48, 480.")
say("")
say("G. WHERE IT FRAYS. (1) near-zero seats stop being 1-or-prime at the stack 2310 (169 = 13 x 13). (2) the 6k-1 seat leads 6k+1 in every band to 1e7 (a lean, not a law; at 30 and 210 the lead changes side between bands).")
say("   (3) 'primes between p and 2p' is a count, not a seat. (4) The 2-frame alone (mod 2, mod 4) sees only parity and side: it never separates a prime from an odd composite; separation begins at the first stacked zero (3) and each new block only removes classes.")
say("")
say("H. HOW TO THINK WITH 2 AS THE ZERO (rules for the solver).")
for r in [
 "1. 2 is 0 with its wings counted: 0 = -1,0,1 and 2 = 1,0,1 are one picture (Lean two_pictures). Read 2 as the hinge, never as a seat. Do not list 2 among the odd primes; 3, 5, 7 are the 1, 2, 3 of odd primes.",
 "2. Measured from 2 (mod 2) every odd prime reads 1 (Lean odd_prime_reads_one). The 2-frame alone (parity, mod 4 side) never tells a prime from an odd composite; it only fixes which seats exist. Expect no prime information from 2 alone; expect all of the SHAPE from it.",
 "3. 2 is 0 on the number line and 1 on the even line (place k at 2k). Use both faces: 2p (E1) = the odd line one zoom up (gaps doubled, Lean e1_gap); 4 = 2's zero stacked with itself (his '4 is the 2 of primes'); E2 = one 2-zero over an odd core.",
 "4. Every prime p is its own zero (p = 0 mod p). Two zeros stack where their multiples meet: 2 and p at 2p (Lean stack_two_p), 2 and 3 at 6, 2,3,5 at 30, 2,3,5,7 at 210. Work around stacked zeros, not around primes.",
 "5. A lone 2-zero opens one wing (one neighbour sits on 3's zero, the other is open); a stacked zero of 2 and 3 opens both wings. Twin primes are the +-1 pair around a 6-zero (Lean twin_straddles_wall; 58979 pairs to 1e7, exception-free in range). The ONLY even off the 3-zero with both sides prime is 4.",
 "6. Seats around a stacked zero W come in mirror pairs r <-> W - r of the same parity, none its own mirror (Lean mirror_keeps_parity); the lone 2-zero is the one stack whose seat (1) faces itself. Seat count multiplies by (r - 1) per block: 1, 2, 8, 48, 480. Taking 2 OUT of the stack (odd offset, his 11-line) makes the mirror cross parity (Lean odd_offset_crosses_parity): odd primes land on evens.",
 "7. Within half a turn of a stacked zero the open seats are 1 and primes, exactly for W = 6, 30, 210 (Lean near_zero_seats_210), because W/2 < (next block)^2. It frays at 2310 where 169 = 13 x 13 is an open seat (Lean fray_at_2310): 53 of 240 near seats composite; at 30030, 1130 of 2880. Rule: the clean half turn ends at the next block squared.",
 "8. The gap line is the even line: g = 2h, so 2 is the UNIT of gaps. Read hops in h (place on the even line): h even keeps the mod-4 side, h odd flips it (33352 vs 45143 to 1e6); h = 0 mod 3 keeps the 6k+-1 facing, the two flips balance exactly (22837 / 22837).",
 "9. Per family from the 6-zero (p = 6k - 1 or 6k + 1): the step of 2 lands on 3's zero on exactly one side (p-2 for 6k-1, p+2 for 6k+1; exception-free to 1e7). Each new block r removes one class of the wall index k per family (k = 1 mod 5 for 6k-1, k = 4 mod 5 for 6k+1) and leaves r - 1. Speak per family and per stack; never 'all primes'.",
 "10. Asymmetries to carry forward, not explain away: 6k-1 leads 6k+1 in every band to 1e7 (332383 vs 332194); at 30 and 210 the leading side changes between bands. Treat the 6-lean as a missing mirror (the hop's own frame, or the lake), and test the opposite reading of every seat count.",
 "11. Where 2-as-zero stops: counts (primes between p and 2p; seat counts) are measures, not seats. The qQq (seats closed by a block larger than the laid stack) is expected to remain at every stack size.",
]:
    say("   " + r)
say(f"   Runtime {time.time()-t0:.1f}s. No PySR run: no continuous relation appeared; every finding here is a count or an exact residue law.")
OUT.write_text("\n".join(lines) + "\n")
print("saved", OUT)

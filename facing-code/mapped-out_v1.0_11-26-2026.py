# Mapped out to X (tUrUq, 11-26-2026). From each prime p, lay the strands of the open seats already found (primes <= p),
# packed from the small end into places that fit under p (2*3*5*7*..., then the next run, ...), and name the first seat
# past p that no strand reaches. B(p) = how many packed places p needs so that the named seat is the next prime.
# For each budget B: the largest X such that every prime from 2 up to X is named exactly with B places.
# isprime / smallest-block table used only to score.
import numpy as np, math

N = 10 ** 7 + 1000
spf = np.zeros(N + 1, dtype=np.int32)
for i in range(2, int(N ** 0.5) + 1):
    if spf[i] == 0:
        spf[i * i::i][spf[i * i::i] == 0] = i
is_p = spf == 0; is_p[:2] = False
primes = np.nonzero(is_p)[0]
spf[is_p] = np.nonzero(is_p)[0]

def places_needed(p, need_block):
    """Pack primes from 2 upward into places with product <= p; return the place index (1-based) holding need_block."""
    k, prod, idx = 1, 1, 0
    for r in primes:
        if r > need_block: return k
        if prod * r <= p: prod *= int(r)
        else: k += 1; prod = int(r)
    return k

if __name__ == "__main__":
    best = {}   # budget -> last prime p with every earlier prime named exactly
    worst_so_far, firstfail = 0, {}
    for i in range(len(primes) - 1):
        p, q = int(primes[i]), int(primes[i + 1])
        if q > 10 ** 7: break
        gap_blocks = spf[p + 1:q]
        need = int(gap_blocks[gap_blocks % 2 == 1].max()) if q - p > 2 else 2   # largest smallest-block among odd seats in the gap
        need = max(need, 2)
        B = places_needed(p, need) if p > 2 else 1
        if B > worst_so_far:
            firstfail[worst_so_far] = p          # with worst_so_far places, the first prime that is missed
            worst_so_far = B
    print("budget B packed places -> first prime whose next prime is missed with B places:")
    for b in sorted(firstfail):
        print(f"  B = {b}: works for every prime below {firstfail[b]}")
    print(f"  B = {worst_so_far}: works for every prime up to 10,000,000 (and the next one)")

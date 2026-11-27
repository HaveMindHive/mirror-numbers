# Exact computations for claim-audit rows 79, 80, 85, 89, 113, 135 (tUrUq's paper v5.8).
# Frozen 11-27-2026. Pure Python 3, no third-party packages. Every number printed is an exact count.
# Run: python3 -I claims-b-exact_v1.0_11-27-2026.py > claims-b-exact-output_v1.0_11-27-2026.txt
import math

def prime_table(n):
    """is_p[k] = 1 exactly when k is prime, for 0 <= k <= n (crossing out multiples of each block)."""
    is_p = bytearray([1]) * (n + 1)
    is_p[0] = is_p[1] = 0
    for r in range(2, math.isqrt(n) + 1):
        if is_p[r]:
            is_p[r * r::r] = bytearray(len(range(r * r, n + 1, r)))
    return is_p

def min_block(n, is_p):
    """first mirror of n: the least q >= 2 dividing n (n itself when n is prime)."""
    if is_p[n]:
        return n
    q = 2
    while n % q:
        q += 1
    return q

N6, N7 = 10 ** 6, 10 ** 7
P = prime_table(2 * N6 + 2 if 2 * N6 + 2 > N7 else N7)
primes7 = [k for k in range(2, N7 + 1) if P[k]]
primes6 = [p for p in primes7 if p <= N6]
assert len(primes6) == 78498 and len(primes7) == 664579

# Row 79: the first mirror met inside a prime's centre (p+1)/2, primes 5 <= p < 10^6.
c = {}
for p in primes6:
    if p >= 5:
        m = (p + 1) // 2
        key = "prime" if P[m] else min_block(m, P)
        c[key] = c.get(key, 0) + 1
print("row 79: centre first mirror, primes 5..10^6:",
      {k: c[k] for k in (2, 3, 5, 7, "prime")}, "| primes counted:", sum(c.values()))

# Row 80: operator strands p -> (p+1)/2 while the centre is prime (p > 3); longest below 10^6.
def strand(p):
    out = [p]
    while p > 3 and P[(p + 1) // 2]:
        p = (p + 1) // 2
        out.append(p)
    return out
best = max(len(strand(p)) for p in primes6)
longest = sorted(strand(p)[::-1] for p in primes6 if len(strand(p)) == best)
print("row 80: longest strand length below 10^6:", best, "| strands of that length:", longest)

# Row 85: open wings w (2w+1 prime), 1 <= w <= 10^6; even and odd wings.
ev = sum(1 for w in range(1, N6 + 1) if P[2 * w + 1] and w % 2 == 0)
od = sum(1 for w in range(1, N6 + 1) if P[2 * w + 1] and w % 2 == 1)
pi_2N1 = sum(P[: 2 * N6 + 2])
print("row 85: open wings to 10^6:", ev + od, "| even:", ev, "| odd:", od,
      "| pi(2*10^6+1) - 1 =", pi_2N1 - 1)

# Row 89: gaps 5 <= p < q <= 10^6 of consecutive primes (the walker is exact on each, ClaimsB.walker_names).
gaps6 = [(p, q) for p, q in zip(primes6, primes6[1:]) if p >= 5]
print("row 89: consecutive prime gaps with 5 <= p < q <= 10^6:", len(gaps6))

# Row 113: facing flips (mod 6) and side flips (mod 4) by direction, consecutive primes 5 <= p < q < 10^6.
f51 = sum(1 for p, q in gaps6 if p % 6 == 5 and q % 6 == 1)
f15 = sum(1 for p, q in gaps6 if p % 6 == 1 and q % 6 == 5)
s13 = sum(1 for p, q in gaps6 if p % 4 == 1 and q % 4 == 3)
s31 = sum(1 for p, q in gaps6 if p % 4 == 3 and q % 4 == 1)
print("row 113: facing flips 6k+1->6k-1:", f15, "| 6k-1->6k+1:", f51,
      "| side flips 1->3 mod 4:", s13, "| 3->1 mod 4:", s31,
      "| first p, last q:", gaps6[0][0], gaps6[-1][1])
# The paper's reading walks every prime 5 <= p < 10^6 to its next prime (the last hop 999983 -> 1000003).
hops = [(p, q) for p, q in zip(primes7, primes7[1:]) if 5 <= p < N6]
print("row 113 (hops from every prime 5 <= p < 10^6):", len(hops), "hops | facing flips 6k+1->6k-1:",
      sum(1 for p, q in hops if p % 6 == 1 and q % 6 == 5), "| 6k-1->6k+1:",
      sum(1 for p, q in hops if p % 6 == 5 and q % 6 == 1), "| side flips 1->3 mod 4:",
      sum(1 for p, q in hops if p % 4 == 1 and q % 4 == 3), "| 3->1 mod 4:",
      sum(1 for p, q in hops if p % 4 == 3 and q % 4 == 1), "| last hop:", hops[-1])

# Row 135: lead of the 6k-1 family over the 6k+1 family, primes 5 <= p <= x.
lead, low, low_at, at = 0, None, None, {}
marks = {10 ** 3, 10 ** 4, 10 ** 5, 10 ** 6, 10 ** 7}
for x in range(5, N7 + 1):
    if P[x]:
        lead += 1 if x % 6 == 5 else -1
        if low is None or lead < low:
            low, low_at = lead, x
    if x in marks:
        at[x] = lead
print("row 135: lead (6k-1 count minus 6k+1 count) at 10^3..10^7:", at,
      "| least lead over every x in [5, 10^7]:", low, "first reached at x =", low_at)

# Row 92: builds of an even number from the even primes 2j (j odd): n = 2^v * m (m odd) is a product of
# exactly v even primes 2*a_i with a_1 <= ... <= a_v odd and a_1 * ... * a_v = m.
def builds(m, v, lo=1):
    if v == 0:
        return 1 if m == 1 else 0
    if v == 1:
        return 1 if m >= lo else 0
    return sum(builds(m // a, v - 1, a) for a in range(lo, math.isqrt(m) + 1, 2) if m % a == 0)
def builds_of(n):
    v, m = 0, n
    while m % 2 == 0:
        m //= 2; v += 1
    return builds(m, v) if v else 0
first = {}
for n in range(2, 10 ** 4, 2):
    b = builds_of(n)
    if b not in first:
        first[b] = n
print("row 92: first even number with b builds (b = 2, 3, 4, 5):", {b: first[b] for b in (2, 3, 4, 5)},
      "| 36 builds:", builds_of(36))

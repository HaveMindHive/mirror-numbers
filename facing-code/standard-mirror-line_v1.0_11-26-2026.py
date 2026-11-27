# Standard / mirror line with offset 11 (tUrUq, 11-26-2026): n_m = 11 - n_s (1s = 10m, 3m = 8s, 4m = 7s, 9s = 2m, 10s = 1m, 11s = 0m).
# Past 11 two readings: carried on (12s = -1m) and folded per block of 11 (n <-> (2j+1)*11 - n inside block j).
# Each row shows n's halving / thirding pictures beside its mirror's.
from sympy import isprime

def R(n): k = n // 2; return (k, 0 if n % 2 == 0 else k + 1, k)
def T(n):
    t, r = divmod(n, 3)
    return (t, t, t) if r == 0 else (t, t + 1, t) if r == 1 else (t + 1, t, t + 1)
pic = lambda x: ",".join(map(str, x))

def block_mirror(n):
    j = n // 11 if n % 11 else n // 11 - 1
    return (2 * j + 1) * 11 - n

if __name__ == "__main__":
    assert [11 - n for n in (8, 7, 9, 10)] == [3, 4, 2, 1] and block_mirror(13) == 20 and block_mirror(3) == 8
    for n in range(1, 45):
        bm = block_mirror(n)
        f = lambda x: ("P" if isprime(x) else " ")
        print(f"{n:3d}s {f(n)} R {pic(R(n)):<9s} T {pic(T(n)):<9s} | carried {11-n:4d}m | block mirror {bm:3d} {f(bm)} R {pic(R(bm)):<9s} T {pic(T(bm))}")

# Odd mirror faces (tUrUq, 11-26-2026). An odd n = w,1,w around a single unit (w = (n-1)/2).
# It can also fold around an odd block m: n = (a copies of m), m, (a copies of m), so its wing w = a*m + (m-1)/2.
# Prime = the only odd centre is the unit (m = 1) or the whole number.
from sympy import isprime, factorint

def faces(n):
    """Odd centres m (1 < m < n) with n = (2a+1)*m, as (m, a)."""
    return [(m, (n // m - 1) // 2) for m in range(3, n, 2) if n % m == 0]

if __name__ == "__main__":
    for n in range(3, 20000, 2):
        w = (n - 1) // 2
        assert (faces(n) == []) == isprime(n)
        assert all(w == a * m + (m - 1) // 2 for m, a in faces(n))
    for n in (9, 15, 21, 25, 27, 33, 35, 45, 49, 63):
        print(n, "wing", (n - 1) // 2, "faces", ", ".join(f"{2*a+1} copies of {m}" for m, a in faces(n)))

# Dual long hand (tUrUq, 11-26-2026): every number read two ways side by side.
#   halving  -> its neighbours: odd n = (n-1)/2, (n+1)/2, (n-1)/2  (the even neighbours n-1, n+1 halved; the left-outs)
#   turn     -> itself: n as q equal copies of n/q (q = smallest block), e.g. 55 = 11,11,11,11,11; a prime = p copies of 1
# Decimal unit line: 11 is the one of 10s (d x 11 = dd), so 55 = five 11s = the 5-turn of the 10s unit.
from sympy import factorint, isprime

def turn_face(n):
    if n < 4 or isprime(n): return f"{n} x 1"
    q = min(factorint(n)); return f"{q} x {n // q}"

def row(n):
    if n % 2:
        k = n // 2
        return f"{n:3d} {'P' if isprime(n) else ' '}  halving {k},{k+1},{k}  (neighbours {n-1} = {dict(factorint(n-1))}, {n+1} = {dict(factorint(n+1))})   turn {turn_face(n)}"
    return f"{n:3d}    halving {n//2},0,{n//2}   turn {turn_face(n)}"

if __name__ == "__main__":
    assert turn_face(55) == "5 x 11" and turn_face(13) == "13 x 1"
    for n in range(5, 60, 2): print(row(n))

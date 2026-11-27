# Dual forms (tUrUq, 11-26-2026): every number carried both ways at once, R (reflection, halving) / T (turn, thirding).
# R: n = k, c, k (c = 0 even, k+1 odd; read wing+wing or centre+wing). T: n = 3t + r as t,t,t / t,t+1,t / t+1,t,t+1 (all count).
# 3 is both: 1,2,1 / 1,1,1. Shared blocks = numbers that appear in both trees (where the two mirrors meet).
from sympy import isprime

def r_top(n):
    k = n // 2
    return (k, 0 if n % 2 == 0 else k + 1, k)

def t_top(n):
    t, r = divmod(n, 3)
    return (t, t, t) if r == 0 else (t, t + 1, t) if r == 1 else (t + 1, t, t + 1)

def blocks(n, top):
    seen, todo = set(), [n]
    while todo:
        m = todo.pop()
        if m <= 3 or m in seen: continue
        seen.add(m)
        todo += [x for x in set(top(m)) if x > 3]
    return seen

if __name__ == "__main__":
    assert r_top(3) == (1, 2, 1) and t_top(3) == (1, 1, 1) and t_top(8) == (3, 2, 3) and t_top(27) == (9, 9, 9)
    for n in range(2, 49):
        a, b = r_top(n), t_top(n)
        shared = sorted((blocks(n, r_top) & blocks(n, t_top)) - {n})
        kind = "P" if isprime(n) else ("E" if n % 2 == 0 else "o")
        print(f"{n:3d} {kind}  R {a[0]},{a[1]},{a[2]:<4d}  T {b[0]},{b[1]},{b[2]:<4d}  wing gap {a[0]-b[0]:2d}  shared blocks {shared}")

def value(a, b, s):
    """One rule for both mirrors: a picture a,b,a at scale s (2 = halving, 3 = thirding) is centre + wing x (s - 1).
    In halving an empty centre is the mirror showing the wing in its place."""
    if s == 2 and b == 0:
        b = a
    return b + (s - 1) * a

def consolidated(n):
    """n written once as picture:scale. Thirding when 3 divides n (equal copies), halving otherwise."""
    a, b, _ = t_top(n) if n % 3 == 0 else r_top(n)
    return f"{a},{b},{a}:{3 if n % 3 == 0 else 2}"

if __name__ == "__main__":
    for n in range(2, 5000):
        a, b, _ = r_top(n); assert value(a, b, 2) == n
        a, b, _ = t_top(n); assert value(a, b, 3) == n
    print("\nconsolidated:", ", ".join(f"{n} = {consolidated(n)}" for n in (2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 15, 22, 27)))

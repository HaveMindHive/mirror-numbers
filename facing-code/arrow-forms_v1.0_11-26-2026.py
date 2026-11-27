# Arrow forms (tUrUq, 11-26-2026). Arrow in = an operator acting on the now; arrow out = an observer.
# Every number takes its equal split when it has one: a turn when 3 divides it, a hinge when 2 does, else the odd halving.
#   turn   (3 | n):          k>,<k>,<k    operator past, observer now, operator future (all three count)   :3
#   hinge  (even, 3 not | n): <k,0,k>     two observers looking out, nothing between                         :2
#   odd    (else):            k>,k+1,<k   operators acting on the centre                                     :2
# Spine form: write the wings outside in and step into the centre until it is a word (<= 3) or a hinge.
from sympy import isprime

def form(n):
    if n % 3 == 0: return "T", n // 3, n // 3
    if n % 2 == 0: return "H", n // 2, 0
    return "O", n // 2, n // 2 + 1

def value(kind, k, c):
    return 3 * k if kind == "T" else 2 * k if kind == "H" else k + c

def spine(n):
    left, right, kinds = [], [], ""
    while n > 3:
        kind, k, c = form(n)
        kinds += kind
        if kind == "T":
            left.append(f"{k}>"); right.append(f"<{k}"); n = k
            continue
        if kind == "H":
            return kinds, ",".join(left + [f"<{k},0,{k}>"] + right[::-1])
        left.append(f"{k}>"); right.append(f"<{k}"); n = c
    centre = {1: "<1>", 2: "<1,0,1>", 3: "1>,<1>,<1"}[n]
    return kinds + str(n), ",".join(left + [centre] + right[::-1])

if __name__ == "__main__":
    for n in range(2, 5000):
        kind, k, c = form(n); assert value(kind, k, c) == n
    assert spine(7) == ("OH", "3>,<2,0,2>,<3") and spine(9) == ("T3", "3>,1>,<1>,<1,<3")
    rows = []
    for n in range(2, 121):
        kinds, s = spine(n)
        tag = "P" if isprime(n) else " "
        rows.append(f"{n:3d} {tag} {kinds:<8s} {s}")
    print("\n".join(rows))

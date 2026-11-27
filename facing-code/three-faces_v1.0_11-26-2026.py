# Three faces in one code (tUrUq, 11-26-2026). Plain commas add; |c| multiplies; the reflection is marked by facing.
#   add face        w,c,w             w = n//2, c = n mod 2           reads w + c + w
#   copies face     m,m,...,m         n = q copies of m (q >= 3 odd)   reads q*m           (plain commas: also adds)
#   product face    a,|b|,c           n = a*b*c                       reads a*b*c
#   reflection face |k,(k+1)|,|k      n = 2k+1 (odd)  or |k,0|,|k     reads centre + one wing (the far wing is the image)
# 3 = 1,1,1 = 1,|1|,1 = |1,2|,|1 ; 18 = 9,0,9 = 6,6,6 = 2,|3|,3 = |9,0|,|9
import re

def faces(n):
    out = {"add": f"{n//2},{n%2},{n//2}"}
    for q in range(3, n + 1, 2):
        if n % q == 0 and n // q >= 1:
            out["copies"] = ",".join([str(n // q)] * q) if q <= 9 else f"{q} x {n//q}"; break
    if n == 3:
        out["product"] = "1,|1|,1"   # bare units: 1 x 1 x 1 = 3; 1 itself has no product face (1x1x1 is 3, not 1)
    for a in (list(range(2, n + 1)) + [1] if n not in (1, 3) else []):
        if n % a: continue
        for b in range(1, n // a + 1):
            if (n // a) % b == 0 and a <= n // a // b:
                c = n // a // b
                if b > 1:
                    out["product"] = f"{a},|{b}|,{c}"
                    break
        if "product" in out: break
    k = n // 2
    out["reflection"] = f"|{k},{k+1}|,|{k}" if n % 2 else f"|{k},0|,|{k}"
    return out

def read(s):
    if s.endswith(tuple("0123456789")) and "x" in s:
        q, m = map(int, s.split(" x ")); return q * m
    if re.fullmatch(r"\d+,\|\d+\|,\d+", s):
        a, b, c = map(int, re.findall(r"\d+", s))
        return 3 if a == b == c == 1 else a * b * c       # bare units: 1 x 1 x 1 = 3
    m = re.fullmatch(r"\|(\d+),(\d+)\|,\|(\d+)", s)
    if m:
        k, c, _ = map(int, m.groups()); return k + (c if c else k)   # centre + one wing; hinge: wing + wing
    return sum(map(int, s.split(",")))

if __name__ == "__main__":
    assert faces(3)["reflection"] == "|1,2|,|1" and read("|1,2|,|1") == 3 and read("1,|1|,1") == 3 and read("1,1,1") == 3
    assert read("9,0,9") == read("6,6,6") == read("2,|3|,3") == read("|9,0|,|9") == 18
    bad = [(n, f, s) for n in range(1, 3000) for f, s in faces(n).items() if read(s) != n]
    assert not bad, bad[:5]
    for n in (3, 5, 7, 9, 11, 15, 18, 27):
        print(n, faces(n))
    print("every face reads back to n for n < 3000")

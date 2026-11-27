# Exact checks of the snapped PySR forms on training and held-out ranges (integers / Fractions only).
import json, importlib.util
from fractions import Fraction
D = json.load(open("pysr-finds-data_v1.0_11-27-2026.json"))
sp = importlib.util.spec_from_file_location("d", "pysr-finds-data_v1.0_11-27-2026.py"); d = importlib.util.module_from_spec(sp); sp.loader.exec_module(d)
def log2(x): return x.bit_length() - 1
rs = sorted(int(r) for r in D["share"])
ok = all(Fraction(*D["share"][str(r)]) == Fraction(1, r - 1) for r in rs)
print("share 1/(r-1): train r<=97 and held-out 101..", rs[-1], ok, "count", len(rs))
L = D["ladder"]
print("ladder length = log2(n//3)+1, n=2..20000:", all(L[str(n)][0] == log2(n // 3) + 1 if n >= 3 else L[str(n)][0] == 1 for n in range(2, 20001)))
def end_rule(n):
    m = log2(n); return 2 if n < 3 * 2 ** (m - 1) else 1
print("ladder end by range, n=4..20000:", all(L[str(n)][1] == end_rule(n) for n in range(4, 20001)))
E = D["evencount"]
print("even count = (X+2)//4 - 1, X=2..6000:", all(E[str(X)] == (X + 2) // 4 - 1 for X in range(2, 6001)))
A = D["alenT"]
print("A-len T(3^k) = 2*3^k - k - 2, k=1..8:", all(A[str(k)] == 2 * 3 ** k - k - 2 for k in range(1, 9)))
# extend A-len held-out to k = 12 with his own notation code
for k in range(9, 13):
    v = len(d.tm.notation_a(d.tm.T(3 ** k))[0]); print(" k", k, v, v == 2 * 3 ** k - k - 2)

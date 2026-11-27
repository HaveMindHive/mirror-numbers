# Claims A, exact computations (tUrUq's unit-counting paper v5.8, audit rows 9, 10, 40, 71), 11-27-2026.
# Frozen script: run with python3 (mpmath 1.3.0). Every check is an exact assert; the output is
# deterministic, and its SHA-256 is recorded in audit-updates-rows-1-75_v1.0_11-27-2026.md.
import importlib.util, os
from itertools import permutations
import mpmath

HERE = os.path.dirname(os.path.abspath(__file__))
CODE = os.path.join(HERE, "..", "unit-counting-paper_v1.0_11-24-2026", "unit-counting-code_v5.8_11-27-2026")

def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec); spec.loader.exec_module(mod); return mod

fb = load("fold_build", os.path.join(CODE, "fold_build_v2.1_11-24-2026.py"))
tm = load("two_mirrors", os.path.join(CODE, "facing-code", "two-mirrors_v1.0_11-26-2026.py"))
out = []
say = lambda s: (print(s), out.append(s))

# Rows 9, 10: each printed decimal is a double-precision reading. Checked against the true value to
# 60 digits: the printed decimal is within one unit of its last printed place, and the script says
# whether it is the shortest repr of the nearest double and/or the true value correctly rounded.
mpmath.mp.dps = 60
table = {
    "2^(1/2)": (mpmath.mpf(2) ** (mpmath.mpf(1) / 2), "1.4142135623730951"),
    "3^(1/3)": (mpmath.mpf(3) ** (mpmath.mpf(1) / 3), "1.4422495703074083"),
    "4^(1/4)": (mpmath.mpf(4) ** (mpmath.mpf(1) / 4), "1.4142135623730951"),
    "5^(1/5)": (mpmath.mpf(5) ** (mpmath.mpf(1) / 5), "1.379729661461215"),
    "6^(1/6)": (mpmath.mpf(6) ** (mpmath.mpf(1) / 6), "1.3480061545972777"),
    "7^(1/7)": (mpmath.mpf(7) ** (mpmath.mpf(1) / 7), "1.3204692477561237"),
    "8^(1/8)": (mpmath.mpf(8) ** (mpmath.mpf(1) / 8), "1.2968395546510096"),
    "10^(1/10)": (mpmath.mpf(10) ** (mpmath.mpf(1) / 10), "1.2589254117941673"),
    "e^(1/e)": (mpmath.e ** (1 / mpmath.e), "1.444667861009766"),
    "sqrt2": (mpmath.sqrt(2), "1.4142135623730951"),
    "sqrt3": (mpmath.sqrt(3), "1.7320508075688772"),
    "sqrt3/sqrt2": (mpmath.sqrt(3) / mpmath.sqrt(2), "1.224744871391589"),
    "sqrt(2/3)": (mpmath.sqrt(mpmath.mpf(2) / 3), "0.816496580927726"),
    "1/sqrt2": (1 / mpmath.sqrt(2), "0.7071067811865475"),
}
for name, (val, printed) in table.items():
    places = len(printed.split(".")[1])
    err = abs(mpmath.mpf(printed) - val)
    assert err < mpmath.mpf(10) ** -places, (name, printed)
    dbl = repr(float(mpmath.nstr(val, 40))) == printed
    rnd = mpmath.nstr(mpmath.mpf(round(val * 10 ** places)) / 10 ** places, 30) == mpmath.nstr(mpmath.mpf(printed), 30)
    say(f"row 9/10  {name:<11s} true {mpmath.nstr(val, 30)}  printed {printed}  "
        f"|error| < 1e-{places}  nearest-double-repr {dbl}  correctly-rounded {rnd}")
# the real peak of x^(1/x) is at e: derivative x^(1/x) (1 - ln x)/x^2 vanishes only at x = e
x0 = mpmath.findroot(lambda x: 1 - mpmath.log(x), 2.5)
assert abs(x0 - mpmath.e) < mpmath.mpf(10) ** -50
say(f"row 9  peak of x^(1/x) at x = {mpmath.nstr(x0, 30)} (= e)")

# Row 40: every arrangement of the prime factors gives its own string, n < 2000.
faces_total = 0
for n in range(2, 2000):
    fs = fb.faces(n)
    assert len(set(fs.values())) == len(fs), n
    for s in fs.values():
        assert s.count("1") == n and s == s[::-1]
    faces_total += len(fs)
say(f"row 40  n = 2..1999: {faces_total} faces, every arrangement its own string, n units, mirror")

# Row 71: notation A decodes for both mirrors, n < 3000; 27 takes 189 (R) and 49 (T) symbols.
for n in range(1, 3000):
    assert tm.read(tm.R(n)) == n and tm.read(tm.T(n)) == n
    assert tm.parse_a(tm.notation_a(tm.R(n))[0]) == tm.R(n)
    assert tm.parse_a(tm.notation_a(tm.T(n))[0]) == tm.T(n)
assert len(tm.notation_a(tm.R(27))[0]) == 189 and len(tm.notation_a(tm.T(27))[0]) == 49
say("row 71  n = 1..2999: notation A of the reflection and of the turn decodes to its tree; 27: 189 vs 49")
say("all exact checks pass")

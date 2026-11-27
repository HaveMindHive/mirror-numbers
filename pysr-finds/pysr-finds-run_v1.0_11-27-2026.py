# PySR runs for the finds (11-27-2026). One job at a time, each capped by timeout. Usage: python3 this.py JOB
import json, sys, os, numpy as np
from pysr import PySRRegressor
HERE = os.path.dirname(os.path.abspath(__file__))
D = json.load(open(os.path.join(HERE, "pysr-finds-data_v1.0_11-27-2026.json")))
job = sys.argv[1]
un = []
if job == "share":
    rs = sorted(int(r) for r in D["share"]); tr = [r for r in rs if r <= 97]
    X = np.array(tr, float)[:, None]; y = np.array([D["share"][str(r)][0] / D["share"][str(r)][1] for r in tr]); names = ["r"]
elif job == "ladlen":
    tr = range(2, 1001); X = np.array(tr, float)[:, None]; y = np.array([D["ladder"][str(n)][0] for n in tr], float)
    names = ["n"]; un = ["floor", "log2"]
elif job == "ladend":
    tr = range(4, 1001); X = np.array(tr, float)[:, None]; y = np.array([D["ladder"][str(n)][1] for n in tr], float)
    names = ["n"]; un = ["floor", "log2"]
elif job == "evencount":
    tr = range(2, 501); X = np.array(tr, float)[:, None]; y = np.array([D["evencount"][str(x)] for x in tr], float)
    names = ["X"]; un = ["floor"]
elif job == "alenT":
    tr = range(1, 6); X = np.array(tr, float)[:, None]; y = np.array([D["alenT"][str(k)] for k in tr], float)
    names = ["k"]; un = ["exp"]
extra = {}
if any("exp2" in u for u in un): extra["extra_sympy_mappings"] = {"exp2": lambda x: 2 ** x}
mdl = PySRRegressor(niterations=40, timeout_in_seconds=150, populations=15, maxsize=16,
                    binary_operators=["+", "-", "*", "/", "^"] if job in ("alenT", "ladend") else ["+", "-", "*", "/"], unary_operators=un,
                    output_directory=os.path.join(HERE, "pysr-runs"), run_id=job, progress=False, verbosity=0,
                    random_state=0, deterministic=True, parallelism="serial", **extra)
mdl.fit(X, y, variable_names=names)
print(mdl.equations_[["complexity", "loss", "equation"]].to_string())

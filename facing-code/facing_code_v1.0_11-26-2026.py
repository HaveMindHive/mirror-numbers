# Facing code (three values 1, 0, -1), mined from tUrUq's 11-26-2026 examples.
# Digits: '1', '0', '|' (= -1). Rewrite one order: 1 -> 010, 0 -> 000, | -> 0|0.
import itertools
from difflib import SequenceMatcher

REW = {"1": "010", "0": "000", "|": "0|0"}


def rewrite(s):
    return "".join(REW[c] for c in s)


def lift(s, w):
    while len(s) < w:
        s = rewrite(s)
    return s


# ---- his hand strings, digit by digit (commas removed, "-1" -> '|') ----
TWO, HINGE4, MTWO = "10|", "00|", "|01"
FOUR = TWO + HINGE4 + MTWO                       # 10-1,00-1,-101
HIS = {
    "4": FOUR,
    "14 half": "010010010" + FOUR + "010010010" + "00|",
    # 16: "-010" read as -(010) = 0|0 (reading a) or as -0,1,0 = 010 (reading b)
    "16 (a)": FOUR + "0000000|0" + FOUR + "000000000" + FOUR + "0000000|0" + FOUR + "000|0|",
    "16 (b)": FOUR + "000000010" + FOUR + "000000000" + FOUR + "000000010" + FOUR + "000|0|",
    "12 half": "111000111" + "00000|",
    "shorthand": "10|" "00||01" "00|" "10|" "00|" "|01" "00|000" "0|0|0" "00|",
}
HIS_BLOCKS = {"10": "232,000,232", "14": "343,000,343", "12": "303,000,303", "16 half": "40400|"}


def make_rule(marker="k_even", hinge_lift="rewrite", lift_odd=True, mirror="keep_hinge",
              one="010", three="111", mid="fixed"):
    return dict(marker=marker, hinge_lift=hinge_lift, lift_odd=lift_odd, mirror=mirror,
                one=one, three=three, mid=mid)


def word(n, R):
    return {0: "000", 1: R["one"], 2: TWO, 3: R["three"]}[n]


def neg(s):
    return s.translate(str.maketrans("1|", "|1"))


def hinge(k, w, R):
    marked = {"k_even": k % 2 == 0, "always": True, "never": False}[R["marker"]]
    h = "00|" if marked else "000"
    if R["hinge_lift"] == "rewrite":
        h = lift(h, w)
    elif R["hinge_lift"] == "pad":
        h = "0" * (w - 1) + h[-1] if w > 3 else h
    return h


def build(n, R):
    """Halving build. even 2k: B(k), hinge, M(B(k)); odd 2k+1: B(k), B(k+1), M(B(k))."""
    if n <= 3:
        return word(n, R)
    k = n // 2
    a, b = build(k, R), mir(k, R)
    if n % 2 == 0:
        return a + hinge(k, len(a), R) + b
    c = build(k + 1, R)
    if R["lift_odd"]:
        w = max(len(a), len(c))
        a, b, c = lift(a, w), lift(b, w), lift(c, w)
    return a + c + b


def mir(n, R):
    """Mirror. reverse: whole string reversed (hinges flip 00| -> |00). negate: 1 <-> |.
    keep_hinge: wings swap and mirror, hinges keep their facing (2 -> |01)."""
    if R["mirror"] == "negate":
        return neg(build(n, R))
    if R["mirror"] == "reverse" or n <= 3:
        return build(n, R)[::-1]
    if n % 2 == 0:
        return build(n, R)  # A, h, M(A) mirrored is itself when the hinge keeps facing
    k = n // 2
    a, b, c = build(k, R), mir(k, R), mir(k + 1, R)
    if R["lift_odd"]:
        w = max(len(a), len(c))
        a, b, c = lift(a, w), lift(b, w), lift(c, w)
    return a + c + b


def half(n, R):
    """Half fold of an even n: B(n/2) then the midpoint marker."""
    a = build(n // 2, R)
    m = {"fixed": "00|", "lifted": lift("00|", len(a)), "pad": "0" * (len(a) - 1) + "|"}[R["mid"]]
    return a + m


def blocks(n):
    if n <= 3:
        return str(n)
    k = n // 2
    return "".join(map(str, (k, 0, k) if n % 2 == 0 else (k, k + 1, k)))


def block_render(name):
    n = int(name.split()[0])
    if name.endswith("half"):
        return blocks(n // 2) + "00|"
    k = n // 2
    return ",".join([blocks(k), "000", blocks(k)])


def generated(name, R):
    if name == "4":
        return build(4, R)
    if name == "14 half":
        return half(14, R)
    if name.startswith("16"):
        return build(16, R)
    if name == "12 half":
        return half(12, R)
    if name == "shorthand":
        return half(16, R)


def diff(a, b):
    out = []
    for tag, i1, i2, j1, j2 in SequenceMatcher(None, a, b, autojunk=False).get_opcodes():
        if tag != "equal":
            out.append(f"{tag} his[{i1}:{i2}]='{a[i1:i2]}' vs rule[{j1}:{j2}]='{b[j1:j2]}'")
    return out


def score(R):
    return sum(generated(k, R) == v for k, v in HIS.items())


def counts(s):
    return s.count("1"), s.count("|")


def ternary(n, R):
    """Ternary mirror build: n=3k+r; r0 k,k,k; r1 k,k+1,k; r2 k+1,k,k+1 (mirror wing reversed)."""
    if n <= 3:
        return word(n, R)
    k, r = divmod(n, 3)
    a, c = (k, k + 1) if r < 2 else (k + 1, k)
    if r == 0:
        c = k
    x, y = ternary(a, R), ternary(c, R)
    w = max(len(x), len(y))
    x, y = lift(x, w), lift(y, w)
    return x + y + x[::-1]


def is_prime(n):
    return n > 1 and all(n % d for d in range(2, int(n ** .5) + 1))


if __name__ == "__main__":
    space = dict(marker=["k_even", "always", "never"], hinge_lift=["rewrite", "pad", "none"],
                 lift_odd=[True, False], mirror=["keep_hinge", "reverse", "negate"],
                 mid=["fixed", "lifted", "pad"])
    results = []
    for vals in itertools.product(*space.values()):
        R = make_rule(**dict(zip(space, vals)))
        results.append((score(R), vals, R))
    results.sort(key=lambda t: -t[0])
    print("top rule sets (exact matches out of", len(HIS), "):")
    for s, vals, _ in results[:8]:
        print(" ", s, dict(zip(space, vals)))
    best = results[0][2]
    print("\nBEST:", best)
    for k, v in HIS.items():
        g = generated(k, best)
        print(f"\n[{k}] {'MATCH' if g == v else 'NO'}  his len {len(v)}, rule len {len(g)}")
        print("  his :", v)
        print("  rule:", g)
        for d in diff(v, g):
            print("   ", d)
    print("\nblock renderings:")
    for k, v in HIS_BLOCKS.items():
        print(f"  {k}: his {v}  rule {block_render(k)}  {'MATCH' if block_render(k) == v else 'NO'}")

    # self-checks
    assert build(4, best) == HIS["4"]
    assert half(14, best) == HIS["14 half"]
    assert block_render("10") == "232,000,232" and block_render("16 half") == "40400|"
    for n in range(1, 200):
        s = build(n, best)
        assert counts(s) == counts(rewrite(s))  # orders keep every unit and marker
        assert counts(ternary(n, best))[0] + counts(ternary(n, best))[1] == n  # ternary keeps n nonzeros

    # shorthand: compare with half-16 built with order-0 (unlifted) hinges
    R0 = make_rule(**{**best, "hinge_lift": "none"})
    h16 = half(16, R0)
    pre = next(i for i, (x, y) in enumerate(zip(HIS["shorthand"] + "#", h16 + "@")) if x != y)
    print(f"\nshorthand vs half-16 (order-0 hinges) = {h16}: first {pre} digits agree; his rest = {HIS['shorthand'][pre:]}")
    assert pre == 24
    # ternary build: -1 count = distance from n to the nearest power of 3
    for n in range(1, 500):
        m = 1
        while m * 3 <= n:
            m *= 3
        assert counts(ternary(n, best))[1] == min(n - m, 3 * m - n), n
    odd_exact = [n for n in range(1, 400, 2) if counts(build(n, best))[0] == n]
    print("odd n whose halving build holds exactly n positive units:", odd_exact)

    # table
    rows = ["n  | fam        | +1 | -1wing | -1hinge | net | +|- tot | n/2 | width | string"]
    for n in range(1, 33):
        s = build(n, best)
        p, m = counts(s)
        old = make_rule(**{**best, "marker": "never"})
        mw = counts(build(n, old))[1]  # -1s carried by the 2-words only
        fam = ",".join(f for f, ok in [("P", is_prime(n)), ("2P", n % 2 == 0 and is_prime(n // 2)),
                                        ("2^m", n & (n - 1) == 0)] if ok)
        rows.append(f"{n:<3}| {fam:<10} | {p:<2} | {mw:<6} | {m - mw:<7} | {p - m:<3} | {p + m:<7} | "
                    f"{n / 2 if n % 2 else n // 2:<4}| {len(s):<5} | {s if len(s) <= 90 else s[:87] + '...'}")
    rows.append("\nternary mirror build with 2 = 10|:")
    rows.append("n  | +1 | -1 | net | string")
    for n in range(1, 33):
        s = ternary(n, best)
        p, m = counts(s)
        rows.append(f"{n:<3}| {p:<2} | {m:<2} | {p - m:<3} | {s if len(s) <= 90 else s[:87] + '...'}")
    txt = "\n".join(rows)
    print("\n" + txt)
    with open(__file__.replace("facing_code_v1.0_11-26-2026.py", "facing_table_v1.0_11-26-2026.txt"), "w") as f:
        f.write("Facing code table, best rule: " + str(best) + "\n\n" + txt + "\n")
    print("\nall checks pass")

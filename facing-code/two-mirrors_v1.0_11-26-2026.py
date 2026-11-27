# Two mirrors (tUrUq, 11-26-2026).
# R = reflection (halving, two-based): n = k, c, k with c = 0 (even) or k+1 (odd). Read: wing + wing (c = 0) or centre + one wing.
# T = turn (thirding, triangle): n = 3k + r as k,k,k / k,k+1,k / k+1,k,k+1. Read: all three copies count.
# A filled-centre triple a,b,a reads a+b as R and 2a+b as T: the imbalance is one wing, a. A hinge triple a,0,a reads 2a both ways.
# Notation A: marks as an extra symbol. R: "L|,C,|R" (wings face in). T: "X|,Y|,Z|" (every copy faces on, the last back to the first).
# Notation B: no extra symbol. Write one order up (0->000, 1->010): units then sit only at the centre seat of each triple,
# so a 1 in a side seat can only be a mark (his 110 / 011).
WORD = {0: "000", 1: "010", 2: "101", 3: "111"}

def R(n):
    if n <= 3: return ("w", n)
    k = n // 2
    return ("R", R(k), ("w", 0) if n % 2 == 0 else R(k + 1), R(k))

def T(n):
    if n <= 3: return ("w", n)
    k, r = divmod(n, 3)
    a, b = (k, k) if r == 0 else (k, k + 1) if r == 1 else (k + 1, k)
    return ("T", T(a), T(b), T(a))

def read(node):
    """The number a tree stands for, by the mark on each triple."""
    if node[0] == "w": return node[1]
    a, b = read(node[1]), read(node[2])
    if node[0] == "R": return a + a if b == 0 else a + b
    return 2 * a + b

def notation_a(node):
    """Marks as a symbol; a triple at height h is separated by h commas (his comma levels)."""
    if node[0] == "w": return WORD[node[1]], 0
    (l, hl), (c, hc), (r, hr) = (notation_a(x) for x in node[1:])
    h, cm = max(hl, hc, hr) + 1, None
    cm = "," * h
    return (f"{l}|{cm}{c}{cm}|{r}" if node[0] == "R" else f"{l}|{cm}{c}|{cm}{r}|"), h

def parse_a(s):
    import re
    runs = re.findall(r",+", s)
    if not runs:
        return ("w", {v: k for k, v in WORD.items()}[s])
    h = max(map(len, runs))
    parts = re.split(r"(?<!,)" + "," * h + r"(?!,)", s)
    l, c, r = parts
    if r.startswith("|"):
        return ("R", parse_a(l[:-1]), parse_a(c), parse_a(r[1:]))
    return ("T", parse_a(l[:-1]), parse_a(c[:-1]), parse_a(r[:-1]))

def digits(node):
    if node[0] == "w": return WORD[node[1]]
    l, c, r = (digits(x) for x in node[1:])
    return l + c + r

def zoom(s):
    return "".join("010" if ch == "1" else "000" for ch in s)

def triples(n):
    """Every filled-centre triple in the R build of n, with its two readings."""
    out = []
    def walk(node):
        if node[0] == "w": return
        a, b = read(node[1]), read(node[2])
        if b: out.append((a, b, a + b, 2 * a + b))
        for x in node[1:]: walk(x)
    walk(R(n))
    return out

if __name__ == "__main__":
    for n in range(1, 3000):
        assert read(R(n)) == n and read(T(n)) == n          # each mirror reads n exactly by its own rule
        assert parse_a(notation_a(R(n))[0]) == R(n) and parse_a(notation_a(T(n))[0]) == T(n)  # notation A decodes
        z = zoom(digits(R(n)))
        assert all(z[i] == "0" for i in range(len(z)) if i % 3 != 1)  # notation B: side seats always free for marks
    # the paradox: the same triple read by the other mirror
    for a in (1, 3, 9):
        assert read(("R", ("w", 1) if a == 1 else R(a), ("w", 1) if a == 1 else R(a), ("w", 1) if a == 1 else R(a))) == 2 * a
    print("n   R-units T-units  A-len(R)  A-len(T)  B-len(R)   R tree top     T tree top")
    for n in (3, 9, 11, 15, 22, 25, 27, 33, 45, 81, 97, 243):
        r, t = R(n), T(n)
        top = lambda x: str(x[1]) if x[0] == "w" else f"{x[0]}:{read(x[1])},{read(x[2])},{read(x[3])}"
        print(f"{n:<4d}{digits(r).count('1'):>6d}{digits(t).count('1'):>8d}{len(notation_a(r)[0]):>10d}{len(notation_a(t)[0]):>10d}"
              f"{3*len(digits(r)):>10d}   {top(r):<14s} {top(t)}")
    print("\nimbalance (filled-centre triples in the R build): a,b,a reads a+b as R, 2a+b as T")
    for n in (3, 9, 22, 27):
        print(n, triples(n)[:6])
    for n in range(1, 5000):  # the halving drift is exactly the uncounted wings
        assert sum(a for a, _, _, _ in triples(n)) == digits(R(n)).count("1") - n

# Unified code (tUrUq, 11-26-2026). One system: every number is  w, c, w  with w = n//2 and centre c = n mod 2
# (0 = the hinge for an even number, 1 = the unit for an odd one). Commas count how many levels down you have gone.
# Going one level down writes every block as its own w, c, w;  0 -> 0,0,0 and 1 -> 0,1,0 at the bottom.
# 8 = 4,0,4 -> 2,0,2,,0,0,0,,2,0,2 -> 1,0,1,0,0,0,1,0,1,,,0,0,0,... (his long hand).

def down(block):
    """One level down: each number in the block becomes w, c, w."""
    return [[n // 2, n % 2, n // 2] for n in block]

def flat(x):
    return [v for b in x for v in b]

def write(n, levels):
    blocks = [n]
    for _ in range(levels):
        blocks = flat(down(blocks))
    out = []
    for i, v in enumerate(blocks):
        if i:
            j = 0
            while i % 3 ** (j + 1) == 0: j += 1
            out.append("," * (j + 1))
        out.append(str(v))
    return "".join(out)

if __name__ == "__main__":
    assert write(8, 1) == "4,0,4" and write(8, 2) == "2,0,2,,0,0,0,,2,0,2"
    for n in range(0, 200):  # the long hand holds exactly n units at the bottom
        L = max(1, n.bit_length())
        assert sum(int(c) for c in write(n, L).replace(",", "")) == n
    for n in (2, 3, 4, 5, 7, 8, 9, 11):
        print(f"{n}:")
        for L in range(1, max(2, n.bit_length()) + 1):
            print(f"   {L} down: {write(n, L)}")

# The digit mirror on the offset-eleven line (v1.0, 11-27-2026). Built for tUrUq

His words (11-27-2026, verbatim): "it absolutely is, any time you see that mirror structure it is, but we need to nail that relationship down. all that weird digit stuff is what i want to explain."

Files in this folder:
- `digit-mirror_v1.0_11-27-2026.py`: asserts everything below, writes `digit-mirror-table_v1.0_11-27-2026.txt`. Runs in under a second.
- Lean: `lean-mirror-numbers-all_v1.0_11-26-2026/MirrorNumbersAll/DigitMirror.lean` (namespace `DigitMirror`).
- His table `offset-eleven-table_v1.0_11-26-2026.txt` was reproduced byte for byte from his script (sha256 3b9a0bbda04abe899a93a5cb3b29b322f545ef11699f79245ad61063edcfa274).

## 1. What "fray" and "crossing" are in his work

**Fray** is defined in code, `offset-eleven_v1.0_11-26-2026.py`:

```
def clean(m):  # class of an even mirror m > 0
    s = strand(core(m))
    if s != "above": return s
    if m % 4 == 2 and pr[m // 2]: return "2p"
    return "fray"
```

with `strand(c)` = "self" for 1, 3; "2^a+1"; "3*2^a+1"; "11/15"; otherwise "above". So an even m is clean when its odd core sits on the ratio-two line or m is a doubled prime 2p; otherwise it is a fray.

**Crossing** is not in any script. It is defined only by the paper sentence in section 25: "In the first blocks of the per-block mirror the primes face even primes and the odd composites face the evens that are not doubled primes ... the first crossings are 33 <-> 22 ... and 73 <-> 70." A crossing is a pair that breaks that facing. Read inclusively, with his ruling that 67 -> 76 is one:
- prime side: a prime faces a frayed even (67 -> 76, 73 -> 70);
- composite side: an odd composite faces a doubled prime 2q (33 <-> 22, 22 = 2 x 11).

The per-block mirror is `block_mirror` of `standard-mirror-line_v1.0_11-26-2026.py`: in block j, n faces (2j+1) x 11 - n, and a multiple of 11 folds to the block below (33 -> 22). 11 <-> 0 is the mirror's own seat and is left out.

## 2. The corrected list

Below 100, in order (Lean `first_crossings`, by `decide`):

| pair | side | note |
|---|---|---|
| 33 <-> 22 | composite | both carry the mirror's own 11 |
| 39 <-> 38 | composite | 38 = 2 x 19 |
| 63 <-> 58 | composite | 58 = 2 x 29 |
| **67 <-> 76** | prime | 76 = 4 x 19, core 19 off the line. A digit mirror |
| 69 <-> 74 | composite | 74 = 2 x 37 |
| 73 <-> 70 | prime | 70 = 2 x 35, core 35 off the line |
| 93 <-> 94 | composite | 94 = 2 x 47 |
| 97 <-> 90 | prime | 90 = 2 x 45 |

Prime side continues 101 <-> 108, 107 <-> 102, 127 <-> 126, 137 <-> 138, 149 <-> 148, 157 <-> 162, 163 <-> 156. Composite side continues 133 <-> 142, 141 <-> 134, 161 <-> 158, 175 <-> 166, 185 <-> 178. For odd n < 200000: 15996 prime-side and 7676 composite-side crossings. Up to 300 the full list is in the table file.

## 3. The exact relationship

Write a two-digit number as a,b (n = 10a + b) and its reversal b,a.

1. n + rev(n) = 11 x (a + b) and n - rev(n) = 9 x (a - b). Every base: (B + 1) and (B - 1). (Lean `two_digit_sum`, `two_digit_diff`.)
2. The per-block mirror fills its block: n + M(n) = (2j + 1) x 11, for every n >= 1 (`block_mirror_add`).
3. So the block mirror is the reversal moved by whole elevens: M(n) = rev(n) + 11 x ((2j + 1) - (a + b)) (`block_mirror_shift`, every base).
4. **The law** (`block_mirror_eq_rev_iff`, proven for every base B >= 2 and every pair of digits): the block mirror of a two-digit number on the line of the base's one, O = B + 1, is its digit reversal **exactly when the two digits are neighbours**, a = b + 1 or b = a + 1.
5. On those pairs the reversal steps by exactly one B - 1 (`neighbour_rev_step`): in base 10, by one 9.

In base 10 that gives exactly nine pairs (`decimal_pairs`): 01 <-> 10, 12 <-> 21, 23 <-> 32, 34 <-> 43, 45 <-> 54, 56 <-> 65, 67 <-> 76, 78 <-> 87, 89 <-> 98, each adding to 11 x (2a + 1). In base 2 (one = 3 = |^1) there is one pair, 01 <-> 10, that is 1 <-> 2 (`binary_pair`). One scale up, base 100 with its one 101, the pairs are 001 <-> 100, 102 <-> 201, ..., 809 <-> 908 (`hundred_pairs`). Base B has B - 1 pairs (checked for B = 2 to 40, proven for every B).

Longer numbers: reversal of an even-length number lands on the facing 11 face (rev(n) + n a multiple of 11), an odd-length one on its own face (rev(n) - n a multiple of 11 and of 99), and rev(n) - n is a multiple of 9 at every length (checked to 200000; the 99 form is the earlier Lean `PalindromeInvolutionModulus`). On the 11 line no three-digit number is its own block mirror's reversal (`no_three_digit_on_eleven`, proven for 100 to 999), and none from 100 to 99999 (checked in the script). The decimal digit mirror meets the 11 line at two digits, then moves up to 101.

**Crossing and digit mirror.** Whether a pair crosses is set by the core of the even partner; where the partner sits is set by the digits. Of the nine neighbour pairs, the odd members with prime class facing: 23 -> 32 (self), 43 -> 34 (core 17 = 2^4 + 1), 67 -> 76 (core 19, fray), 89 -> 98 (core 49 = 3 x 2^4 + 1). So with his clean classes as coded, 67 <-> 76 crosses and 23 <-> 32, 43 <-> 34, 89 <-> 98 do not. Of all crossings below 100, 67 <-> 76 is the one digit mirror (`crossing_digit_mirror`), and the same holds for every crossing below 200000 (script). If "that mirror structure" means every neighbour-digit pair, the classes in `clean` would have to change for 23, 43 and 89; this is left for his reading, the data are not dropped.

## 4. In plain words

A two-digit number has two wings, its tens and its ones. Turn it around and add: the two wings fold onto each other and you always get a whole number of 11s, because 11 is the one of tens, a ten and a one kept together. Take the difference instead and you get a whole number of 9s, the base less one, the other mirror of the same turn. The block mirror on the 11 line also hands every number the partner that fills its block to an odd count of 11s, so it and the digit mirror always face the same 11 seat; they can only disagree by whole 11s. They agree exactly when the digit sum is the block's own odd count, and that happens exactly when the two digits stand next to each other (a, a+1): then the 9 mirror moves one single 9 and the 11 mirror and the 9 mirror meet. That gives nine pairs in tens (01 <-> 10 up to 89 <-> 98), one in twos (1 <-> 2, on 3 = |^1), and the same law one scale up on 101, the one of hundreds: one law, the one of the base, at every scale. 67 <-> 76 is one of the nine, and it is the one of them where a prime faces a frayed even, so it is the first prime crossing and, below 200000, the one crossing that is also a digit mirror. 73 <-> 70 sits in the same block (both add to 143 = 11 x 13), but its partner is the reversal 37 moved up three 11s.

## 5. Corrected row 117 (claim audit) and paper text

Row 117:

| 117 | §25 | First crossings on the per-block 11 mirror: prime side 67 <-> 76, 73 <-> 70, 97 <-> 90 (a prime facing a frayed even); composite side 33 <-> 22 (both carry 11), 39 <-> 38, 63 <-> 58, 69 <-> 74, 93 <-> 94 (an odd composite facing a doubled prime). 67 <-> 76 is also a digit mirror: on the line of the base's one the block mirror is the reversal exactly at neighbour digits (nine pairs in base 10), proven for every base; Lemoine, Goldbach | P (DigitMirror.first_crossings, prime_crossings, crossing_digit_mirror, block_mirror_eq_rev_iff) / R |

Paper §25, replacing "the first crossings are $33\leftrightarrow22$, where both carry the mirror's own $11$, and $73\leftrightarrow70$.":

> the first crossings are $33\leftrightarrow22$, where both carry the mirror's own $11$, then $39\leftrightarrow38$ and $63\leftrightarrow58$ on the composite side, and on the prime side $67\leftrightarrow76$ and $73\leftrightarrow70$. The first prime crossing is a digit mirror: a two-digit number and its reversal add to $11$ times the digit sum and differ by $9$ times the digit difference, so on the line of the base's one ($3$ in base $2$, $11$ in base $10$, $101$ in base $100$) the block mirror is the reversal exactly when the two digits are neighbours ($01\leftrightarrow10$, $12\leftrightarrow21$, \dots, $89\leftrightarrow98$), each pair one $9$ apart (proven in Lean for every base, \texttt{block\_mirror\_eq\_rev\_iff}).

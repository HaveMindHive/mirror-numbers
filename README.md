# Mirror Numbers

**A solve of the prime pattern as a structure:** where every prime sits, the laws between consecutive primes, and a walk that names each one exactly, proven in Lean for every size. Not a formula that skips the computation; the qQq remains.

A counting system in which no unit is lost (1 × 1 = 2), a mirror notation for numbers, and what it shows about the primes: walls of six, the wall law, the hand-off, the hop, and a walk that names every prime in order. Method, notation and ideas by **Turaq Rayn-McLean** (Tormod Ravenskye). Computing and Lean proofs with Anthropic's Claude.

- **Paper:** v5.9, Zenodo, DOI [10.5281/zenodo.24600320](https://doi.org/10.5281/zenodo.24600320) (newest version always at [10.5281/zenodo.24515599](https://doi.org/10.5281/zenodo.24515599)). Source and PDF in `paper/`.
- **Live pages:** [havemindmedia.com/free/mirror-numbers/](https://havemindmedia.com/free/mirror-numbers/)

## What is proven

Every statement below is a theorem in Lean 4 with Mathlib, in `lean-mirror-numbers-all/`: 575 theorems, standard axioms only (`propext`, `Classical.choice`, `Quot.sound`), no `sorry`, no `admit`, no `native_decide`. The claim audit (`lean-mirror-numbers-all/claim-audit_v1.0_11-26-2026.md`) places all 146 claims of the paper: 111 fully proven, 24 more proven in part, and the rest exact computations (frozen scripts with hashes), measured shares, definitions, or readings.

- **Walls of six.** Every prime past 3 sits on a wing of a wall: p = 6k + f, f = ±1 (`Gems.prime_seat`).
- **The wall law.** A prime block r = 6k_r + f_r closes wing f of wall k exactly when k ≡ f·f_r·k_r (mod r) (`PrimeHandOff.wall_law_prime`). It holds at every wall width W, with no further condition (`FableImprovements.wall_law_width`), and the walk is exact on walls of 30 too (`wall_walk_thirty`).
- **The walk.** Starting from 2 and 3 alone, the wall walk names exactly the primes, in order, at every size (`WallWalk.wall_walk`).
- **The hand-off.** For primes 3 < p < q with q = p + 2h, the 2-mirror and the 3-mirror each sit on exactly one of the centre p + h and the half gap h (`PrimeHandOff.hand_off_primes`), and the hop is h = 3w + 2s with w walls crossed (`hop_primes`). For every prime block, the centre sits on neither mirror seat of the half gap (`FableImprovements.hand_off_every_block`), and the hop is read off the centre (`hop_and_hand_off`).
- **One formula, said plainly.** A seat n = 6k + f is prime exactly when no block 6j + g with (6j + g)² ≤ n divides k − f·g·j (`WallFormula.wall_formula`); and p_n + 1 = #{a ≤ 2^(n+1) : π(a) ≤ n} (`nth_prime_formula`); the wall count is proven equal to Mathlib's `Nat.primeCounting` (`prime_count_walls`). It is a computation: exact, and not a fast way to find large primes. The walk is.
- **The walls and the Riemann hypothesis.** In one Lean environment with the community Lean proof of the Riemann hypothesis ([leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis), L. Alpöge with Claude), the wall count is proven to lie within C·N^(1−δ) of Li(N) for some δ > 0 (`walls-meet-rh/WallsMeetRH_v1.0_11-27-2026.lean`, `walls_meet_rh`, standard axioms only). Sharper, from the same proved RH: |W(N) − Li(N)| ≤ C·N^(1/2+δ) for every δ > 0, and ≤ C·√N·(log N)² for N ≥ 55 (`walls-meet-rh/WallsMeetRHSharp_v1.0_11-27-2026.lean`: `walls_meet_rh_half`, `walls_meet_rh_sqrt`), with ψ(x) − x = O(x^(1/2+δ)) and O(√x·(log x)³) proven on the way. Sharpest, by a kernel-checked truncated explicit formula: |W(N) − Li(N)| ≤ C·√N·log N for N ≥ 55, von Koch's form (`WallsMeetRHVonKoch.walls_meet_rh_sqrt_log`). From the proved generalized RH, each wing family 6k − 1 and 6k + 1 holds Li(x)/2 + O(√x·(log x)²) primes, and the lead of one over the other is at most C·√x·(log x)² (`WingFamiliesGRH.wing_families_meet_grh`). Schoenfeld's explicit constants are not formalized. Check it with `walls-meet-rh/check-walls-meet-rh_v1.0_11-27-2026.sh` inside a built clone of that repo.
- **The digit mirror.** On the line of the base's one (3 in base 2, 11 in base 10), the block mirror of a two-digit number is its reversal exactly when the two digits are neighbours, proven for every base (`DigitMirror.block_mirror_eq_rev_iff`); 67 ↔ 76 is the first prime crossing and a digit mirror.
- **The unit count.** u(n) = n exactly at 2^a and 3·2^a, and u(n) ≠ 2n for every n (`RatioTwoLine.fixed_iff`, `ManyTurns.line_never`), plus the two-point law and laws found by PySR and then proven (`Gems`, `PySRFinds`).

## What was run

| Run | Result |
|---|---|
| Every number from 2 to 10^13 by the wall walk (C: walls of 6 in 2269 s, walls of 30 in 1051 s, fast walls of 30 in 186 s) | 346,065,536,839 primes, equal to `sympy.primepi` |
| Every number from 2 to 10^12 (walls of 6: 185 s; walls of 30: 38.1 s; fast: 10.0 s) | 37,607,912,018 primes, equal to `sympy.primepi` |
| The last 1,000,000,002 seats below 2^64 | 67,611,645 primes; two separate Miller–Rabin base sets agree on every one; every closed seat carries a dividing block; the last is 2^64 − 59 |

## Check it yourself

```
cd lean-mirror-numbers-all
lake exe cache get      # Mathlib build cache
lake build              # builds every module
lake env lean AxiomCheckAll_v1.4_11-27-2026.lean   # prints the axioms of all 422 theorems
```

The walkers: `facing-code/wall-walk-max_v1.0_11-27-2026.c` (`clang -O3 -o wall-walk-max wall-walk-max_v1.0_11-27-2026.c -lpthread`, then `./wall-walk-max walk 1e11 12`), the faster walls-of-30 walker `facing-code/wall-walk-thirty_v1.0_11-27-2026.c` (`./wall-walk-thirty 1e11 12`), and the Python walkers beside them.

## What it is not

It is not one closed formula that skips the computation; the author's view is that the primes are a relationship with families and that a residue, the qQq, remains at every scale. Every correct method ends with the same list of primes, so the list is the check, not the claim. What is claimed is the structure above, proven.

## Licences

Paper: CC BY 4.0. Code and Lean sources: MIT (`LICENSE-CODE-MIT.txt`).

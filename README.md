# Mirror Numbers

**A solve of the prime pattern as a structure:** where every prime sits, the laws between consecutive primes, and a walk that names each one exactly, proven in Lean for every size. Not a formula that skips the computation; the qQq remains.

A counting system in which no unit is lost (1 × 1 = 2), a mirror notation for numbers, and what it shows about the primes: walls of six, the wall law, the hand-off, the hop, and a walk that names every prime in order. Method, notation and ideas by **Turaq Rayn-McLean** (Tormod Ravenskye). Computing and Lean proofs with Anthropic's Claude.

- **Paper:** v5.7, Zenodo, DOI [10.5281/zenodo.24596924](https://doi.org/10.5281/zenodo.24596924) (newest version always at [10.5281/zenodo.24515599](https://doi.org/10.5281/zenodo.24515599)). Source and PDF in `paper/`.
- **Live pages:** [havemindmedia.com/free/mirror-numbers/](https://havemindmedia.com/free/mirror-numbers/)

## What is proven

Every statement below is a theorem in Lean 4 with Mathlib, in `lean-mirror-numbers-all/`: 422 theorems, standard axioms only (`propext`, `Classical.choice`, `Quot.sound`), no `sorry`, no `admit`, no `native_decide`. The claim audit (`lean-mirror-numbers-all/claim-audit_v1.0_11-26-2026.md`) places all 143 claims of the paper: 94 proven, the rest checked by computer to a stated range, measured, definitions, or readings.

- **Walls of six.** Every prime past 3 sits on a wing of a wall: p = 6k + f, f = ±1 (`Gems.prime_seat`).
- **The wall law.** A prime block r = 6k_r + f_r closes wing f of wall k exactly when k ≡ f·f_r·k_r (mod r) (`PrimeHandOff.wall_law_prime`). It holds at every wall width W, with no further condition (`FableImprovements.wall_law_width`), and the walk is exact on walls of 30 too (`wall_walk_thirty`).
- **The walk.** Starting from 2 and 3 alone, the wall walk names exactly the primes, in order, at every size (`WallWalk.wall_walk`).
- **The hand-off.** For primes 3 < p < q with q = p + 2h, the 2-mirror and the 3-mirror each sit on exactly one of the centre p + h and the half gap h (`PrimeHandOff.hand_off_primes`), and the hop is h = 3w + 2s with w walls crossed (`hop_primes`). For every prime block, the centre sits on neither mirror seat of the half gap (`FableImprovements.hand_off_every_block`), and the hop is read off the centre (`hop_and_hand_off`).
- **One formula, said plainly.** A seat n = 6k + f is prime exactly when no block 6j + g with (6j + g)² ≤ n divides k − f·g·j (`WallFormula.wall_formula`); and p_n + 1 = #{a ≤ 2^(n+1) : π(a) ≤ n} (`nth_prime_formula`); the wall count is proven equal to Mathlib's `Nat.primeCounting` (`prime_count_walls`). It is a computation: exact, and not a fast way to find large primes. The walk is.
- **The walls and the Riemann hypothesis.** In one Lean environment with the community Lean proof of the Riemann hypothesis ([leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis), L. Alpöge with Claude), the wall count is proven to lie within C·N^(1−δ) of Li(N) for some δ > 0 (`walls-meet-rh/WallsMeetRH_v1.0_11-27-2026.lean`, `walls_meet_rh`, standard axioms only). This is a consequence of RH, through Tau Ceti's Ingham transfer; the sharper √N·log²N form is not yet formalized. Check it with `walls-meet-rh/check-walls-meet-rh_v1.0_11-27-2026.sh` inside a built clone of that repo.
- **The unit count.** u(n) = n exactly at 2^a and 3·2^a, and u(n) ≠ 2n for every n (`RatioTwoLine.fixed_iff`, `ManyTurns.line_never`), plus the two-point law and laws found by PySR and then proven (`Gems`, `PySRFinds`).

## What was run

| Run | Result |
|---|---|
| Every number from 2 to 10^13 by the wall walk (C, 12 threads: walls of 6 in 2269 s, walls of 30 in 1051 s) | 346,065,536,839 primes, equal to `sympy.primepi` |
| Every number from 2 to 10^12 (walls of 6: 185 s; walls of 30: 38.1 s) | 37,607,912,018 primes, equal to `sympy.primepi` |
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

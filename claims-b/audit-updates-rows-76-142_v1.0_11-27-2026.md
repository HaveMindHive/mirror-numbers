# Audit updates, rows 76 to 142 (11-27-2026)

Proposed changes to `claim-audit_v1.0_11-26-2026.md` (the audit itself is not overwritten). Paper: unit-counting-paper v5.8.

New module: `lean-mirror-numbers-all_v1.0_11-26-2026/MirrorNumbersAll/ClaimsB.lean` (namespace `ClaimsB`), sha256 5585cacbea0b6eb06cc206d819325a876e0bde72446c842d1a0bd347ca23a85e. It compiles clean with `lake env lean MirrorNumbersAll/ClaimsB.lean`. It has no sorry, no admit and no native_decide. Axioms for all 40 declarations: `claims-b-axioms_v1.0_11-27-2026.txt`. 26 use [propext, Classical.choice, Quot.sound], 2 use [propext, Quot.sound], 3 use [propext] and 9 use none. The module is not yet in `MirrorNumbersAll.lean` (no `lake build` was run). Add `import MirrorNumbersAll.ClaimsB` there at the next shared build.

New class label **E** = exact computation: a frozen script, its output and the sha256 of both. A count labelled E is exact and reproducible but is not a Lean proof.

Exact computation files:
- `claims-b-exact_v1.0_11-27-2026.py` (sha256 c0f5cac1090e6ffc5b776cc3e055f85fc1e5dacd56831e57fc3f442f1e8616fc) writes `claims-b-exact-output_v1.0_11-27-2026.txt` (sha256 8a8f2e4f25c43e47961d4a264a5ccb26fe34a6c9a37d0e219bab611bf3e6d7c8). It is pure Python 3 and runs in under a minute: `python3 -I claims-b-exact_v1.0_11-27-2026.py`.
- `reruns_v1.0_11-27-2026/`: his scripts were rerun on 11-27-2026 and each output is byte-identical to his stored table (`diff -q` found no difference):
  - asymmetric-tell: script c752fb4dcafaaf02e07a927d1268dcca16dfd105b25ae32145a383ffec8cfb40, output c89b6e4b58d726a34150fbe0b785ad244e8ef20d01fc4f27bc0f23736d73016e
  - rule-breakers: script 1149eef5549f5da4682bcc708f778e76dcacb785d53edde01e6c9cf9fecff5b2, output a9f41355ce81a7cea8f6a9c3856f6ecd492321604280ea637d2713071d8e0c65
  - mapped-out: script 5d473f1b197e683131d0dc4bd40a3e50253b1e6d6171c2871c1ef96dd66684e5, output d545a62f144556ddb95f4a4b79a09b9ce4035bd10a77e38e2900a13ccad18871

Rows already plain P (76, 84, 86, 87, 93, 95 to 98, 100, 103 to 108, 111, 112, 116, 118 to 122, 124 to 127, 129 to 132, 138, 139, 142) are unchanged. Rows 81 and 101 are "D/P (new)" and are already proven, so they are also unchanged. Rows 143 and 144 are left as they are.

| # | Old | New | Lean theorem(s) (ClaimsB.) / exact computation | Note |
|---|-----|-----|-----------------------------------------------|------|
| 77 | D | D/P | arrowNest, arrow_runs, arrow_examples, arrow_shorthand | k -> k<1> = 2k+1. n nestings from 1 give 2^(n+1) - 1, for every n |
| 78 | C/R | P/R | first_false_prime, false_prime_seat, false_prime_25, false_prime_49, false_prime_121 | For every prime block q: once every mirror below q is laid, the first false prime is q * q. "First mirror" = least split = minFac. The reading stays his |
| 79 | M | E | claims-b-exact, row 79 line | 39321 (2), 19610 (3), 4868 (5), 2478 (7), 4299 (centre prime) over the 78496 primes 5..10^6. All exact. The other 7920 centres meet larger mirrors |
| 80 | M | P/E | longest_strand_chain; claims-b-exact, row 80 line | Lean proves that every member of the strand is prime, that each step is 2q - 1, that the strand cannot step in at 16651 (centre 8326) and that its next step 1065601 > 10^6. The computation finds that the longest length is 6 and that this strand is the one strand of that length below 10^6 |
| 83 | D | D/P | strand, strand_start, strand_step, strand_missing, strand_examples, wing_examples | Strands of 3, 5, 7 and p = \|w examples |
| 85 | M | P/E | open_wings_image, open_wings_card, open_wings_count, even_open_wings_count; claims-b-exact, row 85 line | For every N: open wings in [1, N] = primes in [3, 2N+1]. Even open wings = primes 4j+1 and odd open wings = primes 4j+3. At N = 10^6 the counts are 148932 = pi(2000001) - 1, 74416 even and 74516 odd (E) |
| 88 | D/R | D/P/R | wing_shared, gap_sides | 2k and 2k+1 share wing k. For odd p < q, q - 1 lies inside the gap and p - 1 lies outside it. "The right side is broken, the tell" stays a reading |
| 89 | M | P/E | walker_names; claims-b-exact, row 89 line | In every gap of consecutive primes 3 <= p < q, the walker reads no open wing before the centre and reads q at the centre. 78495 gaps for 5 <= p < q <= 10^6 (E) |
| 90 | P/M | P/E | (structure: HandOff.never_both, PrimeHandOff.never_both_primes); asymmetric-tell rerun | 194071 pairs, 0 identical block sets, 46084 shared, all shared blocks are blocks of the centre: reproduced exactly |
| 91 | M | M | asymmetric-tell rerun | The shares are reproduced exactly by the rerun (0.7832 at [10^3, 10^4) is the 78.3%) but stay measured shares. No exact law |
| 92 | P/M | P/E/M | claims-b-exact, row 92 line | "First with 2, 3, 4, 5 builds: 36, 180, 360, 840" is exact (E). A build of 2^v m (m odd) is v even primes 2a_i, with the a_i odd and their product m. The leader list stays M |
| 94 | R | P/R | place_product, half_unit, half_product_hom | On the even line the place product is a (x) b = 2ab, so 1 (x) 1 = 2. With 2 as the unit, 2 . 2 = 2, and doubling carries ordinary multiplication onto ab/2, so factoring is single again. "The counting rule is lost" stays a reading |
| 99 | P/C | P | fifty_five (with TwoParts.neighbour_up, neighbour_down) | The 55 example: 27, 28, 27; 54 = 2*3^3; 56 = 2^3*7; both coprime to 55 = 5*11; 28^2 - 27^2 = 55 |
| 102 | D | D/P | twenty_two_three | 22 = 11,0,11 and 23 = 11,1,11 as 1,0,1 and 1,1,1 with wing 11 |
| 109 | P/M | P/M | stays | 0.2503, 0.1250, 0.0626 are measured shares. The exact law over each run of 6r is already P |
| 110 | P/R | P/R | stays | "Change the picture, not the verdict" is a reading beyond the proven parts |
| 113 | M/P | P/E | (Gems.gap_class_balance_primes); claims-b-exact, row 113 lines | Over the 78496 hops from every prime 5 <= p < 10^6 (the last hop is 999983 -> 1000003): facing 6k+1 -> 6k-1 22837 and 6k-1 -> 6k+1 22838; side 1 -> 3 mod 4 22572 and 3 -> 1 mod 4 22571. All exact. If hops are cut at q <= 10^6, the facing flips are 22837 / 22837. This is why two-zero_v1.0 prints 22837 / 22837 |
| 114 | M | M | stays | Range table and chance figures are measured |
| 115 | C | P | offset_eleven_line, offset_22_pairs, offset_66_pairs, offset_33_pairs | Offset 22: 3, 5, 11. Offset 66: six pairs (5, 7, 13, 19, 23, 29). Offset 33 pairs a prime with twice a prime exactly at 7, 11, 19, 23, 29 (4 = 2 x 2). Proven by `decide` |
| 117 | C/R | C/R | stays; flag for his reading | "First crossings" use the clean/fray classes of the u count, which are not formalized here. His own table (offset-eleven-table, block [66,77]) marks 67 -> 76 as fray too, ahead of 73 -> 70. Lemoine, Goldbach part = reading |
| 123 | P/M | P/E | (WallWalk.wall_walk); mapped-out rerun | 664579 primes named. Place counts 1 -> 23, 2 -> 167, 10 -> 9403, 29 -> 100483, 78 -> 1018057, 213 to 10^7: reproduced exactly. The packing is not in Lean |
| 128 | R | P | near_zero_iff, near_zero_6, near_zero_30, near_zero_210, frays_2310 | For every width: if every prime below the block q divides W and q does not, then every open seat 1 <= s <= W/2 is 1 or prime exactly when W/2 < q^2. This is an iff, stronger than "holds while" but exactly what the sentence states. 6, 30, 210 hold; 2310 frays (1155 >= 169) |
| 130 (add) | P | P | seat_210_count, wall_walk_210, prime_count_width | Walls of 210 have 48 wings, with the walk on them. For any W: pi(N) = #{primes <= N dividing W} + #{n <= N, n >= 2, prime to W, no block r prime to W with r^2 <= n divides n} |
| 133 | P/M | P/M | stays | The shares 57%, 47.5%, 38%, 20% stay measured |
| 134 | M | M | stays | Measured seat ranges |
| 135 | M/R | E/R | claims-b-exact, row 135 line | Lead of 6k-1 over 6k+1 (primes 5..x): 6 at 10^3, 5 at 10^4, 22 at 10^5, 34 at 10^6, 189 at 10^7 (exact). Over every x in [5, 10^7] the least lead is 0 (a tie, first at x = 7) and the lead is never negative. "Rides in the qQq" and the offset 66 sentence stay readings |
| 136 | R | R | stays | A reading of the method as waves; no precise statement |
| 137 | R | R | stays | Related work; not a claim |
| 140 | C/P | C/P | stays | Needs the packing function in Lean; not attempted in this job |
| 141 | C/P | E/P | rule-breakers rerun | The ten off-strand breakers 11, 15, 22, 36, 44, 88, 272, 2112, 4224, 8448 to 10^6 are reproduced exactly. It is a finite list; no general statement to prove |

## Totals

- Rows gaining a full Lean proof of their stated mathematics (to P or a proven part): 77, 78, 80, 83, 85, 88, 89, 94, 99, 102, 115, 128 (12 rows). Rows 99, 115 and 128 are now plain P. Row 130 gained walls of 210 and the count at any width.
- Counts made exact and reproducible (E): rows 79, 80, 85, 89, 90, 92, 113, 123, 135, 141 (10 rows).
- Unchanged, with the reason given above: 91, 109, 110, 114, 117, 133, 134, 136, 137, 140.
- Found false as written: none. Two notes. Row 113's 22838 counts the last hop from 999983 to 1000003, past 10^6. Row 117's "first crossing 73 <-> 70" sits after 67 -> 76, which his own table also marks fray; this needs his reading.

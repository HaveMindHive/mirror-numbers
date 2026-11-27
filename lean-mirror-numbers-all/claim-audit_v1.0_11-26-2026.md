# Claim audit: unit-counting-paper v5.9 (11-27-2026; first made for v5.1, 11-26-2026)

Paper: `unit-counting-paper_v5.1_11-26-2026.tex`. Library: `lean-mirror-numbers-all_v1.0_11-26-2026` (one Lake project, 15 modules; `Gems` added 11-27-2026).

Build: `lake build` clean (18208 jobs, exit 0; log `lean-build-log_v1.0_11-26-2026.txt`); rebuilt with `Gems` 11-27-2026 (18210 jobs, exit 0; log `lean-build-log_v1.1_11-27-2026.txt`). Axioms: 308 + 22 theorems printed, every one on propext / Classical.choice / Quot.sound only (`lean-axiom-check_v1.0_11-26-2026.txt`, Gems block appended at the end); no sorry, no admit, no native_decide in any module.
"P (gem)" = proven 11-27-2026 in module `Gems` from the PySR gems file (`gems-for-lean_v1.0_11-26-2026.txt`).

Classes: **P** proven in Lean (module.theorem) · **C** checked by computer to a stated range · **M** measured share or count · **D** definition or notation · **R** reading or theoretical note.
"P (new)" = proven in this job (modules `UnifiedCode`, `PrimeHandOff`); the earlier range check is listed in the note.

| # | Section | Claim | Class | Lean theorem(s) / check | Note |
|---|---------|-------|-------|-------------------------|------|
| 1 | Terms | Two zeros 0_n, 0_a; two ones 1_u, 1_c; words 000, 010, 101, 111; wing/centre/hinge; comma; marks | D/P | ClaimsA: `words_mirror_units`, `mirror_words_are_words`: 000, 010, 101, 111 are exactly the three-digit 0/1 mirrors, and the word of n holds n units. The names (0_n, 0_a, 1_u, 1_c, wing, centre, hinge, comma, marks) stay notation. |  |
| 2 | §1 | Table of two zeros and two ones | D | ClaimsA: A table of names with no mathematical statement. |  |
| 3 | §2 | Containment: 1 x n = n for n > 1 | P | ClaimsA: `containment`: unitProd [1,n] = unitProd [n,1] = n for n not 1. |  |
| 4 | §2 | Bare units: 1 x 1 = 2, 1 x ... x 1 (n times) = n | P | ClaimsA: `bare_units` (n bare units give n, every n), `bare_units_small`; with UnifiedCode.face_bare_units. |  |
| 5 | §2 | Whole-expression rule; grouping does not change a result | P | ClaimsA: `whole_expression_examples`, `unitProd_perm`, `PExpr`, `grouping`, `grouping_swap`, `one_one_one_grouped`. The reading of 1 x (1+1) as "1,2, then 3" stays R, because it reads a sum inside a product, which the rule does not model. |  |
| 6 | §2 | No distributive law; agreement with ordinary arithmetic off bare units | P | ClaimsA: `agreement` (a factor holding the unit gives the ordinary product), `no_distributive`. The near-ring and octonion remark stays R. |  |
| 7 | §3 | 1/1 = 1, inf/inf = inf, two-valued 2/1, 0_a/0_a = 1, 0_n/0_n = 0_n, 1^n = n, 1^0 = 0_n | D/P | ClaimsA: `two_over_one` (x x 1 = 2 iff x = 1 or 2), `over_one` (2 is the only two-valued n/1), `one_pow_count`, `one_pow_zero`, `pow_count`. The values 1/1 = 1, inf/inf, 0_a/0_a = 1 and 0_n/0_n = 0_n stay definitions. Note: under the rule, x x 1 = 1 has no solution (1 x 1 = 2), so 1/1 = 1 is a definition and not a solve. |  |
| 8 | §4 | Count root of n of order n is 1 | P | ClaimsA: `count_root`: for n >= 1, x^n = n under the rule iff x = 1. |  |
| 9 | §4 | Table of n^(1/n) decimals; peak at e; e^(1/e) = 1.4446... | P + exact | ClaimsA: `measure_root_peak` (n^(1/n) < 3^(1/3) for every whole n >= 1, n not 3), `cube_lt_three_pow`, `two_four_tie`, `measure_root_ne_one`. The decimals are an exact computation: each printed decimal is a double-precision reading within one unit of its last place of the 60-digit true value. 2^(1/2), 3^(1/3), 6^(1/6), 7^(1/7), 10^(1/10) and sqrt2 print the nearest double, which differs from correct rounding in the last digit. Peak of x^(1/x) at e over the reals: the derivative zero, computed. |  |
| 10 | §4 | Two yardsticks: sqrt(3)/sqrt(2), sqrt(2/3) = 0.8164..., 1/sqrt(2) | P + exact | ClaimsA: `yardsticks` (2 sqrt(n/2)^2 = n, (sqrt3/sqrt2)^2 = 3/2, sqrt(2/3) (sqrt3/sqrt2) = 1, (1/sqrt2)^2 = 1/2, sqrt(1/2) = 1/sqrt2), `cube_diagonals`. Decimals as in row 9. 1/sqrt2 prints 0.7071067811865475, which is the correct rounding; the nearest double prints ...476. |  |
| 11 | §5 | Halving build B(2k) = B(k),0,B(k); B(2k+1) = B(k),B(k+1),B(k); examples 4, 5, 6, 17 | P | ClaimsA: `B_examples` (4, 5, 6, 17 as printed), `B_digits` (every digit is 0 or 1). |  |
| 12 | §5 | Every build is a mirror with one hub; even hub is the zero, odd inherits | P (v5.4) | Upgrades.B_reverse, B_length, hub_even, hub_odd | B matches fold_build_v2.1 |
| 13 | §5 | T(1)=T(2)=T(3)=1, T(2k) = 2T(k)+1, T(2k+1) = 2T(k)+T(k+1) | P | ClaimsA: `T`, `T_base`, `T_even`, `T_odd` (recursion for k >= 2, every k). |  |
| 14 | §6 | Rewrite 0 -> 000, 1 -> 010; order-1 words | P | ClaimsA: `rewrite_words`, with UnifiedCode.step and order_one_words. |  |
| 15 | §6 | Rewrite before build = rewrite after build (n < 300, orders 0..2) | P (new) | UnifiedCode.levels_succ, levels_succ_step, step_eq_level | one level deeper = one order of the rewrite once the string is in digits (every n, every level, both block rules) |
| 16 | §6 | Units stay fixed across orders | P (new) | UnifiedCode.step_sum, order_keeps_units |  |
| 17 | §6 | A one at digit i moves to digit 3i+1 | P (v5.4) | Upgrades.step_position, one_moves, centre_stays | position law not formalized |
| 18 | §6 | Length triples per order; centre stays the centre | P (new) | UnifiedCode.step_length, step_reverse | mirror kept and width tripled; the centre index is implied |
| 19 | §6 | Left wing of 11: 10 ones; 3, 30, 111 zeros at orders 0, 1, 2 | P | ClaimsA: `eleven_wing`, every order d: the left wing of 11 holds 10 ones and (27 3^d - 1)/2 - 10 zeros. `eleven_wing_zeros` gives 3, 30, 111. Supporting lemmas: `leftWing_step`, `leftWing_order`. |  |
| 20 | §6 | Mixing orders not allowed; Cantor remark | R | ClaimsA: A rule of the notation (mixing orders is not allowed) and a shape remark on Cantor; no statement to prove. |  |
| 21 | §7 | Mirror-word counts for L = 2, 3, 4, 5 | P | ClaimsA: `palCount_table` (L = 2, 3, 4, 5, every weight). |  |
| 22 | §7 | Triaxial theorem: one mirror word per unit count iff L in {0, 1, 3}; two words of weight 2 for L >= 4 | P | UnitCountingLaws.triaxial_iff, two_le_palCount_two, not_triaxial_of_four_le |  |
| 23 | §8 | Ternary build k,k,k / k,k+1,k / k+1,k,k+1; level one gives the four words; level two the order-1 words | P | ClaimsA: Already proven: UnifiedCode.blocks3, words3, order_one_words. |  |
| 24 | §8 | Every ternary string is a mirror (n <= 729) | P (new) | UnifiedCode.tern_reverse | every n, every level |
| 25 | §8 | Each number has its own string | P (new) | UnifiedCode.levels_inj |  |
| 26 | §8 | Units equal n exactly, no excess (n <= 729) | P (new) | UnifiedCode.tern_sum | every n, every level |
| 27 | §8 | One level deeper = one order of the rewrite | P (new) | UnifiedCode.levels_succ_step |  |
| 28 | §8 | Centre unit exactly when n is odd | P (new) | UnifiedCode.centre_eq_parity |  |
| 29 | §8 | Odd 2k+1 as k,k+1,k is the one source of excess | P | TwoMirrors.u_eq_add_imb, imb_odd | excess = wings of filled-centre triples |
| 30 | §8 | Octave [2^k, 2^(k+1)) holds (17 5^(k-1) - 2^k)/3 units; x5 against x4; drift 5/4 | P (new) | UnifiedCode.S_succ, octave_sum, octave_sum', octave_values; Gems.octave_from_blocks | S(k+1) = 5 S(k) + 2^k; 3 S(k) + 2^k = 17 5^(k-1), k >= 1 (Python asserted a = 1..22); second route 11-27: the octave is the c = 2 block beside the c = 3 block of G2 |
| 31 | §8 | No-excess numbers of the binary build: {2^k, 3 2^k} | P | RatioTwoLine.fixed_iff |  |
| 32 | §8 | No-excess numbers of the ternary build: {3^k, 2 3^k} | P (corrected) | ClaimsA: **False as written**: the row's list {3^k, 2 3^k} is not the full set; 5 has no excess. Corrected statement, proven: the ternary build has no excess at any n (`ternary_no_excess`). `five_not_three_pow` is the counterexample. Paper v5.8 already says this. |  |
| 33 | §9 | Mirror remainders: same mod 9; mod 11 same for odd digit count, opposite for even | P | UnitCountingLaws.mirror_mod_nine, mirror_mod_eleven_odd, mirror_mod_eleven_even |  |
| 34 | §9 | A prime of >= 3 digits: its mirror is not divisible by 3 or 11 | P | ClaimsA: `prime_mirror_not_three_eleven`: if p is prime and p >= 100, its digit mirror is divisible by neither 3 nor 11. |  |
| 35 | §9 | 2 and 5 through 10: odd orders of 2 and 5 give odd order of 10; even period means not both odd; odd period means equal 2-adic parts | P | UnitCountingLaws.even_period_law, even_period_never_both_odd, odd_period_law |  |
| 36 | §9 | Seven-segment mirrors swap 2 and 5 | P | ClaimsA: `seven_segment_swap`: the top-bottom and left-right mirrors of the seven segments swap 2 and 5. The segment model is in the docstring. |  |
| 37 | §9 | Carry level: one integer in (x, y] carries the top power of 2, which is 2^floor(log2(x xor y)) | P | UnitCountingLaws.carry_level_law, xor_log_split |  |
| 38 | §9 | ... the level at which the builds of x and y first share a block | R | ClaimsA: "First share a block" is not defined precisely in the paper; the level formula itself is row 37 (P). |  |
| 39 | §10 | Divisor build: d copies of m, zero growing one order per level; 12 example | P | ClaimsA: `rep`, `leaf`, `face` (match fold_build_v2.1 `face`), `face_twelve` (the 12 example). |  |
| 40 | §10 | Every face has n ones, is a mirror, is its own string, no composite face reads as a prime (n < 2000) | P + exact | ClaimsA: Every arrangement, every n: `face_sum` (a face holds exactly n ones), `face_reverse` (mirror), `composite_face_not_leaf` (no face with two or more factors is the string of any prime leaf; via `leaf_no_nine`, `nine_in_face`). "Every arrangement its own string" is an exact computation for n = 2..1999, 17177 faces. |  |
| 41 | §10 | Why the zero grows; the 35 error of v2.0 | P | ClaimsA: `v20_error` (with the first gap at 000, 5 copies of 7 is exactly the prime string of 35), `rep_rep` (one fixed gap flattens copies of copies), `twentyfour_flattens`. The "why" sentence stays as a reading. |  |
| 42 | §11 | Equal-width zoom: every width a power of 3 | P (new) | UnifiedCode.levels_length, code_length | 3^d at level d |
| 43 | §11 | Mark rules; half-words give the four words; commas count the zoom; 17 example | D/P | ClaimsA: `markR`, `markL`, `foldWhole`, `half_words`, `mark_examples` (4 = 10\|,00\|,\|01; 4 = 101,000,\|; 8 unfolds to 101,000,101,000,101,000,101; 8 = 4,,0,,\|). The comma display stays notation. |  |
| 44 | §11 | Width steps up exactly after 3 2^k (4-6: 9, 7-12: 27, 13-24: 81, 25-48: 243) | P (v5.4) | Upgrades.width_closed, width_words | W matches facing-number-line zoom for n < 3000 |
| 45 | §11 | Mark rule; marked string unfolds to the build (n < 400); 11 example | P | ClaimsA: `marked_unfolds`, **every n** (the script checked n < 400): the mark rule of eleven-mirror_v1.0 (xy\|, \|yx, x\|x, x\|1\|x) unfolds to B(n). Also `marked_eleven`, `eleven_marked`, `B_words`, `unmark_markWord`. Commas are separators and are not modelled. |  |
| 46 | §11 | Centre digit a unit only for 1, 3, 2^m+1 (n < 600) | P (v5.4) | Upgrades.centre_unit_iff | every n |
| 47 | §11 | Cube form a,\|a\|,a = a^3; 1,\|1\|,1 = 3 | P | ClaimsA: `cube_form` (a,\|a\|,a = a^3 for a not 1), `cube_examples` (8, 27, 64; 1,\|1\|,1 = 3). |  |
| 48 | §12 | Only neighbours k, k+1 occur at each level; ladder shorthand; 19, 97 examples | P | ClaimsA: `neighbours`, every n and every level: each block at level d is n/2^d or n/2^d + 1. Also `lvl_nineteen`, `ladder_examples` (19, 97). |  |
| 49 | §12 | Every ladder ends in 2\| P (v5.4) | PySRFinds.ladder_ends_two_three, ladder_ends_one_two, ladder_length | ranges for M >= 2 | ladder-shorthand script |  |
| 50 | §12 | u recursion; u(19) = 44; sequence values | P | ClaimsA: `u_values` (u(1..16)), `u_nineteen` ((2,3) -> (4,7) -> (15,14) -> 44). |  |
| 51 | §12 | u shares the k, k+1 shape with Stern's diatomic; not in OEIS | R/M | ClaimsA: Absence from the OEIS is a dated search result, not a theorem. The shared k, k+1 shape is a description. |  |
| 52 | §13 | u(n) = n iff n = 2^a or 3 2^a; otherwise 5u >= 7n | P | RatioTwoLine.fixed_iff, dich |  |
| 53 | §13 | u(n) is not 2n for n >= 1 | P | RatioTwoLine.u_ne_two_mul |  |
| 54 | §13 | u(2^a+1) = 2^(a+1) - 1; u(3 2^a + 1) = 2(3 2^a - 1) | P | RatioTwoLine.u_pow_add_one, u_three_pow_add_one; Gems.strand_pow, strand_three_pow, strands_agree | second route 11-27: both strands are the j = 1 case of G1 (Gems.u_pow_one) at c = 2, 3 |
| 55 | §13 | Odd n below 2n iff 2^a+1, 3 2^a+1 (a >= 1) or 1, 11, 15 | P | RatioTwoLine.ratio_two_line, below_strand, strand_below |  |
| 56 | §13 | 11 and 15 forced as pair points | P | TurnRoots.pair_point, eleven, fifteen; ManyTurns.below_classify |  |
| 57 | §13 | u(n) = 2(n-1) at 2, 11, 15 and at no other n < 2^20 | P (new) | PrimeHandOff.two_eleven_fifteen | every n >= 1, from the ratio-two classification and the mod-2 law |
| 58 | §13 | Decimal mirrors below the line to 2^20: 11, 22, 33, 44, 66, 88, 272, 2112, 4224, 8448 | P | ClaimsA: `decimal_mirrors_below`: for 10 <= n < 2^20, n is a decimal mirror below the line iff n is one of 11, 22, 33, 44, 66, 88, 272, 2112, 4224, 8448. This uses `below_shape` (every n: below the line iff n = 2^j m, m on a strand or a pair point), `u_pow_mul`, `dig_eq`, `pal_iff`, and `ok_pow`, `ok_eleven`, `ok_fifteen`, `ok_strand_one`, `ok_strand_two` (decide +kernel). The old script ran to 10^6; this covers the full 2^20. |  |
| 59 | §13 | u/n = 20/11 on 11 2^j and 21/11 on 33 2^j | P (new) | UnifiedCode.u_eleven_pow, u_thirtythree_pow |  |
| 60 | §13 | Mod-4 law: odd u exactly at 1 and 2^a+1; 2 mod 4 exactly at 3 2^a+1; else 4 divides u | P | TwoMirrors.u_odd_iff, u_two_mod_four_iff, strand_law_odd, four_dvd_rest |  |
| 61 | §13 | 11 and 15 first odd numbers with exactly one factor 4 | P (v5.4) | Upgrades.first_four_factor |  |
| 62 | §13 | The factor comes from 2u(n) - u(n+1) = 4u(k) at n = 2k+1 | P | TwoMirrors.d_odd, d_even |  |
| 63 | §14 | Even line: a (x) b = 2ab; two readings of "even prime"; first part at 18; 36, 60, 180 | P | ClaimsA: `otimes`, `even_line_product`, `two_p_even_world`, `first_part_eighteen`, `splits_examples`. **Correction**: 180 has three splits (2 x 90 = 6 x 30 = 10 x 18) and the paper lists two. "First part at 18" holds with p odd; 4 = 2 x 2 is twice a prime but not an even-line prime. |  |
| 64 | §14 | Midpoint k+1 even iff p = 3 mod 4 | P | RuleHierarchy.even_centre_iff |  |
| 65 | §14 | p = 1 mod 4 iff p = x^2 + y^2 | P | ClaimsA: `one_mod_four_iff_two_squares`, `odd_midpoint_iff_two_squares`. This is the same set Fermat and Euler reached by another route; Mathlib's Nat.Prime.sq_add_sq gives one direction. |  |
| 66 | §15 | Reflection reading gives n for every n | P (new) | UnifiedCode.read_halving_odd, read_halving_even, face_reflection_odd/even |  |
| 67 | §15 | Turn reading gives n; ternary digits hold n units (n < 3000) | P (new) | UnifiedCode.read_turn, tern_sum |  |
| 68 | §15 | Paradox: 9,9,9 as reflection is 18; 1,1,1 as reflection is 2 | P | ClaimsA: `paradox` (9,9,9 reads 18 as a reflection and 27 as a turn; 1,1,1 reads 2 and 3). |  |
| 69 | §15 | Imbalance = u(n) - n; 2^a and 3 2^a have none; 22 example | P | ClaimsA: `imb_zero_iff` (no imbalance exactly at 0, 2^a, 3 2^a), `twentytwo_imb` (imb 22 = 18, u 22 = 40). |  |
| 70 | §15 | Pure halving v: v(n) = n at 2^a; v is not 2n; odd below 2n exactly 1, 7, 2^a+1 | P | TwoMirrors.v_fixed_iff, v_ne_two_mul, v_below_iff |  |
| 71 | §15 | Both mark notations decode (n < 3000); 27: 49 vs 189 symbols | P + exact | ClaimsA: `twentyseven_marks` (27: 189 symbols as a reflection, 49 as a turn; `markRf` is notation A of two-mirrors_v1.0), with PySRFinds.markT_length. "Both notations decode" is an exact computation for n = 1..2999. |  |
| 72 | §16 | Picture rule a,b,a:s = b + (s-1)a; scale 1 the centre | P | ClaimsA: Already proven: UnifiedCode.read, read_one, read_step. |  |
| 73 | §16 | Every halving and thirding form reads n (n < 5000) | P (new) | UnifiedCode.read_halving_odd/even, read_turn |  |
| 74 | §16 | 1,1,1 -> 1,2,3; 2,3,2 -> 3,5,7; 9,9,9 -> 9,18,27 | P (new) | UnifiedCode.read_examples |  |
| 75 | §16 | Wing-2 picture gives three primes only at 2,3,2 | P (new) | UnifiedCode.wing_two_primes | b, b+2, b+4 prime forces b = 3 |
| 76 | §16 | Halving and thirding share wings exactly at 2, 3, 5 | P | TwoMirrors.shared_wings |  |
| 77 | §16 | Arrows: operator in, observer out; k -> k<1> = 2k+1 | D/P | ClaimsB: arrowNest, arrow_runs, arrow_examples, arrow_shorthand | k -> k<1> = 2k+1. n nestings from 1 give 2^(n+1) - 1, for every n |
| 78 | §17 | First mirror; stopping at 2, 3 leaves the first false prime at 25; each mirror moves it to the next prime squared | P/R | ClaimsB: first_false_prime, false_prime_seat, false_prime_25, false_prime_49, false_prime_121 | For every prime block q: once every mirror below q is laid, the first false prime is q * q. "First mirror" = least split = minFac. The reading stays his |
| 79 | §17 | Centre first-mirror counts to 10^6: 39321 (2), 19610 (3), 4868 (5), 2478 (7), 4299 prime | E | ClaimsB: claims-b-exact, row 79 line | 39321 (2), 19610 (3), 4868 (5), 2478 (7), 4299 (centre prime) over the 78496 primes 5..10^6. All exact. The other 7920 centres meet larger mirrors |
| 80 | §17 | Longest operator strand below 10^6: 16651 -> ... -> 532801 | P/E | ClaimsB: longest_strand_chain; claims-b-exact, row 80 line | Lean proves that every member of the strand is prime, that each step is 2q - 1, that the strand cannot step in at 16651 (centre 8326) and that its next step 1065601 > 10^6. The computation finds that the longest length is 6 and that this strand is the one strand of that length below 10^6 |
| 81 | §18 | One code w,c,w; 8, 7, 11 examples | D/P (new) | UnifiedCode.blocks2, code_examples |  |
| 82 | §18 | Every number holds exactly itself in units | P (new) | UnifiedCode.code_sum, code_reverse | every n, every level |
| 83 | §19 | p = \|w; strand rule w = a m + (m-1)/2; strands of 3, 5, 7 | D/P | ClaimsB: strand, strand_start, strand_step, strand_missing, strand_examples, wing_examples | Strands of 3, 5, 7 and p = \|w examples |
| 84 | §19 | Open wings are prime seats; next prime = first open seat (3..10^4; 10^9..10^9+2 10^4) | P (v5.4) | Upgrades.open_iff_prime, missing_iff_not_prime; WallWalk.wall_walk | every wing; walk exact to 1e12 and 1e9 seats below 2^64 (wall-walk-max) |
| 85 | §19 | 148932 open wings to 10^6; 74416 even, 74516 odd | P/E | ClaimsB: open_wings_image, open_wings_card, open_wings_count, even_open_wings_count; claims-b-exact, row 85 line | For every N: open wings in [1, N] = primes in [3, 2N+1]. Even open wings = primes 4j+1 and odd open wings = primes 4j+3. At N = 10^6 the counts are 148932 = pi(2000001) - 1, 74416 even and 74516 odd (E) |
| 86 | §19 | Even open wings belong to primes that are sums of two squares, odd ones do not (w < 50000) | P (v5.4) | Upgrades.even_wing_iff_two_squares, two_squares_mod_four | sum of two squares proven; a+-bi split read from it |
| 87 | §20 | Centre seat fixes half-gap seat (four cases, every gap to 10^6) | P (new) | PrimeHandOff.centre_fixes_half_gap, hand_off_primes; HandOff.two_hand_off, three_hand_off; FableImprovements.hand_off_every_block, hand_off_primes' | every pair of primes 3 < p < q |
| 88 | §20 | 2k and 2k+1 share the wing k; the right side is broken | D/P/R | ClaimsB: wing_shared, gap_sides | 2k and 2k+1 share wing k. For odd p < q, q - 1 lies inside the gap and p - 1 lies outside it. "The right side is broken, the tell" stays a reading |
| 89 | §20 | Walker names q in all 78495 gaps to 10^6 | P/E | ClaimsB: walker_names; claims-b-exact, row 89 line | In every gap of consecutive primes 3 <= p < q, the walker reads no open wing before the centre and reads q at the centre. 78495 gaps for 5 <= p < q <= 10^6 (E) |
| 90 | §20 | Blocks cross only through the centre (194071 pairs, 46084 shared) | P/E | ClaimsB: (structure: HandOff.never_both, PrimeHandOff.never_both_primes); asymmetric-tell rerun | 194071 pairs, 0 identical block sets, 46084 shared, all shared blocks are blocks of the centre: reproduced exactly |
| 91 | §20 | Prediction shares 78.3 / 60.3 / 49.7 % vs 31.3 / 24.3 / 20.1 %; misses before q | M | ClaimsB: asymmetric-tell rerun | The shares are reproduced exactly by the rerun (0.7832 at [10^3, 10^4) is the 78.3%) but stay measured shares. No exact law |
| 92 | §21 | Even-line primes are odd places, a fixed quarter floor((X+2)/4) - 1; multiple builds; leaders to 10^6 | P/E/M | ClaimsB: claims-b-exact, row 92 line | "First with 2, 3, 4, 5 builds: 36, 180, 360, 840" is exact (E). A build of 2^v m (m odd) is v even primes 2a_i, with the a_i odd and their product m. The leader list stays M |
| 93 | §21 | 4w+2 is twice a prime iff w is open (to 10^6) | P (v5.4) | Upgrades.twice_prime_iff_open |  |
| 94 | §21 | Unit remarks: 2 (x) 2 = 4; with 2 as the unit the rule is lost | P/R | ClaimsB: place_product, half_unit, half_product_hom | On the even line the place product is a (x) b = 2ab, so 1 (x) 1 = 2. With 2 as the unit, 2 . 2 = 2, and doubling carries ordinary multiplication onto ab/2, so factoring is single again. "The counting rule is lost" stays a reading |
| 95 | §21 | 2p sits between a shallow and a deep left-out; deep side by p mod 4; depth = halvings + 1 (p < 2 10^5) | P (v5.4) | PySRFinds.depth_one_mod_four, depth_three_mod_four | every odd p >= 5 |
| 96 | §22 | Three faces: commas add, bars multiply, facing wings reflect; every face reads n (n < 3000) | P (new) | UnifiedCode.face_add, face_copies, face_product, face_reflection_odd/even |  |
| 97 | §22 | 3 = 1,1,1 = 1,\|1\|,1 = \|1,2\|,\|1; 18 four ways | P (new) | UnifiedCode.eighteen_faces, face_bare_units |  |
| 98 | §22 | 1 has no product face; a prime's product face is 1,\|p\|,1 | P (new) | UnifiedCode.face_bare_units, face_prime |  |
| 99 | §23 | Halving shows the neighbours, which share no block with n; 55 example | P | ClaimsB: fifty_five (with TwoParts.neighbour_up, neighbour_down) | The 55 example: 27, 28, 27; 54 = 2*3^3; 56 = 2^3*7; both coprime to 55 = 5*11; 28^2 - 27^2 = 55 |
| 100 | §23 | centre^2 - wing^2 = n; faces are pictures one to one; a prime has one picture | P | TwoParts.halving_square, face_square, face_block, centre_gap, prime_one_picture |  |
| 101 | §23 | Mark \|^x = x(b+1); 11, 101, 55; 3, 5, 9, 17, 33 in base 2 | D/P (new) | UnifiedCode.mark, mark_base_two, mark_examples |  |
| 102 | §23 | 22 = 11,0,11 and 23 = 11,1,11 as pictures of 2 and 3 | D/P | ClaimsB: twenty_two_three | 22 = 11,0,11 and 23 = 11,1,11 as 1,0,1 and 1,1,1 with wing 11 |
| 103 | §23 | (k ones)(10^(k-1)+1) = (k-1 ones) 2 (k-1 ones) | P | TwoParts.repunit_mirror, eleven_unit |  |
| 104 | §23 | 7^2 = 2 5^2 - 1; (3,2), (17,12), (41,29) | P (v5.4) | Upgrades.ladder_sign, ladder_rungs, seven_five | Pell numbers by another route |
| 105 | §24 | Every set of turns: u is not 2n; self-count numbers c 2^a; odd non-turn below the line is strand, pair point 4j+3 or near-turn; nothing below 3/4 | P | ManyTurns.line_never, below_classify, three_quarter, no_sporadic; TurnRoots.odd_fixed, pow_fixed |  |
| 106 | §24 | t = 2^b+1 makes 4t-1, t = 2^b-1 makes 4t+3; 3 makes 11 and 15 | P | TurnRoots.pair_point (general), eleven, fifteen, nineteen, thirtyone, seven |  |
| 107 | §24 | Seat rule h = -p 2^(-1) mod r; 5: 2p, 7: 3p, 11: 5p, 13: 6p | P | RuleHierarchy.five_class, seven_class, eleven_class, thirteen_class |  |
| 108 | §24 | Rules stack in size order; block r above the hand-off from two seats per run of 6r | P | RuleHierarchy.five_above_handoff, seven_above_handoff, eleven_above_handoff, allowed_mod_30 |  |
| 109 | §24 | Block r takes 1/(r-1) of what is left: 0.2503, 0.1250, 0.0626 to 10^6 | P/M | ClaimsB: stays | 0.2503, 0.1250, 0.0626 are measured shares. The exact law over each run of 6r is already P |
| 110 | §24 | Offset-11 mirror, per-block mirror, lake change the picture, not the verdict | P/R | ClaimsB: stays | "Change the picture, not the verdict" is a reading beyond the proven parts |
| 111 | §24 | Hop: h = 3w + 2s, s in {-1,0,1}; side flips iff w odd; facing flips iff s is not 0 | P (new on primes) | WallMirror.half_gap_walls, step_cases, side_is_walls, facing_is_step; PrimeHandOff.hop_primes; FableImprovements.hop_reads_centre, hop_and_hand_off | now stated for primes 3 < p < q |
| 112 | §24 | Wall-free hop of 4 leaves 6k+1 and lands on 6k-1 | P | WallMirror.no_wall_needs_first_seat, no_wall_lands_last_seat |  |
| 113 | §24 | Flip counts 22837/22838 and 22572/22571 to 10^6; differ by at most one on any walk | P/E | ClaimsB: (Gems.gap_class_balance_primes); claims-b-exact, row 113 lines | Over the 78496 hops from every prime 5 <= p < 10^6 (the last hop is 999983 -> 1000003): facing 6k+1 -> 6k-1 22837 and 6k-1 -> 6k+1 22838; side 1 -> 3 mod 4 22572 and 3 -> 1 mod 4 22571. All exact. If hops are cut at q <= 10^6, the facing flips are 22837 / 22837. This is why two-zero_v1.0 prints 22837 / 22837 |
| 114 | §24 | Range table 28/50 ... 1/2; chance 0.39-0.45 nearly flat | M | ClaimsB: stays | Range table and chance figures are measured |
| 115 | §25 | Offset-11 pairings; 22; 33; 66 | P | ClaimsB: offset_eleven_line, offset_22_pairs, offset_66_pairs, offset_33_pairs | Offset 22: 3, 5, 11. Offset 66: six pairs (5, 7, 13, 19, 23, 29). Offset 33 pairs a prime with twice a prime exactly at 7, 11, 19, 23, 29 (4 = 2 x 2). Proven by `decide` |
| 116 | §25 | Odd offsets pair odd with even, even offsets keep parity | P | TwoZero.odd_offset_crosses_parity, mirror_keeps_parity |  |
| 117 | §25 | First crossings 33 <-> 22, 73 <-> 70; Lemoine, Goldbach | P/R (v5.9) | DigitMirror: first_crossings, prime_crossings, crossing_digit_mirror, block_mirror_eq_rev_iff | corrected: first crossings below 100 are 33,39,63,67,69,73,93,97; 67<->76 is the crossing that is also a digit mirror; block mirror = reversal exactly at neighbour digits, every base; Lemoine, Goldbach stay readings |
| 118 | §26 | (\|^1)^2 = 1,2,1 and (\|^1)^3 = 1,3,3,1 in its base; 9, 121, 1331 | P | NineCubes.mark_square, mark_cube; UnifiedCode.mark_sq_digits (b >= 3), mark_cube_digits (b >= 4) | digit lists now P |
| 119 | §26 | Two-digit reversal: sum is 11 x digit sum, difference 9 x digit difference; nines reverse on the 11-line | P | NineCubes.rev_sum, rev_diff, nine_rev, eighteen_rev |  |
| 120 | §26 | A cube carries its root's halving scaled; its halving reads p^2 +- p + 1 | P | NineCubes.cube_picture, cube_halving |  |
| 121 | §26 | Squares of 3, 5, 7 sit one past a wall; no other prime below 1000 does | P (v5.4) | Upgrades.square_past_self_counting_iff; NineCubes.nine_self_counting | self-counting numbers 2^a, 3 2^a; every prime |
| 122 | §26 | Sums of two cubes are composite except 1^3 + 1^3 = 2; first two are 2 and 9 | P (v5.4) | Upgrades.cube_sum_prime_iff, cube_sum_first_two |  |
| 123 | §27 | Construction names every prime to 10^7 (664579), at most 213 places; 23, 167, 9403, 100483, 1018057 | P/E | ClaimsB: (WallWalk.wall_walk); mapped-out rerun | 664579 primes named. Place counts 1 -> 23, 2 -> 167, 10 -> 9403, 29 -> 100483, 78 -> 1018057, 213 to 10^7: reproduced exactly. The packing is not in Lean |
| 124 | §28 | 0 = -1,0,1 and 2 = 1,0,1 one picture | P | TwoZero.two_pictures |  |
| 125 | §28 | 2 the prime with the hinge; every other prime has the unit at its centre; reads 1 from 2's mirror | P | TwoZero.hinge_prime, odd_prime_unit_centre, odd_prime_reads_one |  |
| 126 | §28 | Primes past the stacks sit on seats coprime to 6, 30; mirror r <-> W - r keeps parity, none its own mirror | P | TwoZero.stacked_six, stacked_thirty, mirror_keeps_parity |  |
| 127 | §28 | Within half a turn of 6, 30, 210 every open seat is 1 or a prime; frays at 2310 at 169 | P | TwoZero.near_zero_seats_210, fray_at_2310 | 6 and 30 are the small cases of row 126 |
| 128 | §28 | ... holds while W/2 is below the next block squared | P | ClaimsB: near_zero_iff, near_zero_6, near_zero_30, near_zero_210, frays_2310 | For every width: if every prime below the block q divides W and q does not, then every open seat 1 <= s <= W/2 is 1 or prime exactly when W/2 < q^2. This is an iff, stronger than "holds while" but exactly what the sentence states. 6, 30, 210 hold; 2310 frays (1155 >= 169) |
| 129 | §28 | Twins straddle a multiple of 6; 6k-1: p-2 on 3's zero; 6k+1: p+2 (to 10^7) | P | TwoZero.twin_straddles_wall; TheSolve.two_step_minus, two_step_plus | every k |
| 130 | §29 | Wall law: r = 6kr + fr closes wing f of wall k iff k = f fr kr (mod r); one residue for both wings (blocks 5..281, walls to 200000) | P (new on primes) | TheSolve.wing_identity, wing_closed, wings_mirror, wall_reads_both_wings, five_closes, seven_closes; PrimeHandOff.wall_law_prime, wall_both_wings_prime; FableImprovements.wall_law_width, wall_law_six, wall_law_inverse (any width, no coprimality clause) | every prime block r >= 5 and every wall |
| 131 | §29 | Two families one strand through zero; equal count under negation | P | TheSolve.family_through_zero, neg_swaps_family, family_count_mirror |  |
| 132 | §29 | Hop 2h = 6w + (f_q - f_p) | P (new on primes) | TheSolve.hop_wall_frame; PrimeHandOff.hop_facings; FableImprovements.hop_and_hand_off |  |
| 133 | §29 | Facing flips ~57%; side kept 47.5% / 38%; same wall 20% from 6k-1, none from 6k+1 (to 10^7) | P/M | ClaimsB: stays | The shares 57%, 47.5%, 38%, 20% stay measured |
| 134 | §29 | Next prime within 1/1, 2/4, 3/5, 3/6 seats (90/99%) by band; walls at half the reading cost | M | ClaimsB: stays | Measured seat ranges |
| 135 | §29 | 6k-1 leads 6k+1 in every band (22, 34, 189); offset 66 pairs equal; lead rides in the qQq | E/R | ClaimsB: claims-b-exact, row 135 line | Lead of 6k-1 over 6k+1 (primes 5..x): 6 at 10^3, 5 at 10^4, 22 at 10^5, 34 at 10^6, 189 at 10^7 (exact). Over every x in [5, 10^7] the least lead is 0 (a tie, first at x = 7) and the lead is never negative. "Rides in the qQq" and the offset 66 sentence stay readings |
| 136 | §30 | The method as waves | R | ClaimsB: stays | A reading of the method as waves; no precise statement |
| 137 | §31 | Related work | R | ClaimsB: stays | Related work; not a claim |
| 138 | gems G1 | Two-point law: c >= 2, 0 <= j <= 2^a: u(c 2^a + j) = u(c) v(2^a + j) - d(c) v(j), d(c) = 2u(c) - u(c+1) | P (gem) | Gems.two_point, u_block_start, u_pow_one | PySR found it at loss 0; Python checked 1,634,586 cases (c < 400, a < 12); induction on a with j split by parity; the class-by-8 weights are the a = 3 case (Gems.u_8k1'..u_8k7', class_eight_agree) |
| 139 | gems G2 | Block sums: 3 sum_{j<2^a} v(j) = 5^a - 2^a; 3 sum_{j<2^a} v(2^a+j) = 4 5^a - 2^a; c >= 2: 3 sum_{j<2^a} u(c 2^a + j) = u(c)(4 5^a - 2^a) - d(c)(5^a - 2^a) | P (gem) | Gems.v_sum_low, v_sum_high, v_sums_int, block_sum | Python checked 2,980 cases (c < 300, a < 10), v sums a < 14; each halving multiplies a block total by 5 |
| 140 | gems G3 | Record block of the packed places: at each record X the places needed equal places_needed(X, prevprime(isqrt(nextprime(X)))) | C/P | ClaimsB: stays | Needs the packing function in Lean; not attempted in this job |
| 141 | gems G5 | Rule-breaker count: every member of 2^a, 2^a+1, 2^a+2, 3 2^a, 3 2^a+1 breaks a rule; off the strands exactly 11, 15, 22, 36, 44, 88, 272, 2112, 4224, 8448 (to 10^6) | E/P | ClaimsB: rule-breakers rerun | The ten off-strand breakers 11, 15, 22, 36, 44, 88, 272, 2112, 4224, 8448 to 10^6 are reproduced exactly. It is a finite list; no general statement to prove |

## Counts

Rows: 141. Classes (a row with two classes counts under each): P 77 (of which P (new) 29, P (gem) 4), C 34, M 16, D 27, R 19.

Gems job 11-27-2026: no paper row changed class from C to P; the gems are new laws (rows 138, 139 P; rows 140, 141 C with a proven part), and rows 30, 54, 113 gained a second proven route (G2 recovers the octave sum, G1 recovers both strands, G4 reads flips_balance on the gap classes). Row 50's note now points at the law behind the values.

## Checked claims that became proven in this job (C -> P)

Rows 15, 16, 18, 24, 25, 26, 27, 28, 30, 42, 57, 59, 66, 67, 73, 74, 75, 82, 87, 96, 97, 98, 111 (on primes), 118 (digit lists), 130 (on primes), 132 (on primes); plus the class-by-8 weights of u from the Python checks (UnifiedCode.u_8k1, u_8k3, u_8k5, u_8k7), not stated in the paper text.

## Stays checked to N or measured, and why

- Rows 11, 12, 17, 19, 44, 45, 46, 48, 49: facts about the halving build B with leaves 1, 2, 3 (hub, zoom widths, mark unfolding, centre digit, ladder ends) and the digit position law 3i+1. B's string is not formalized as a list; `levels` formalizes the unified code and the ternary build. The route is the same as `levels_reverse` with the block rule [k,0,k] / [k,k+1,k] and leaves 1, 2, 3.
- Row 40: the divisor build with a zero growing one order per level is not formalized.
- Rows 58, 61, 104, 115, 117, 121, 122 (second half): finite lists and numeric facts.
- Rows 78, 84, 86, 93: strands laid over a window and the sum-of-two-squares reading; these are range checks over primes, not exact general statements in the paper's wording.
- M rows (79, 80, 85, 89, 91, 109, 113 counts, 114, 123, 133, 134, 135): shares and counts.
- Row 32 is flagged for his reading: the ternary build as defined has zero excess at every n.
- Row 140 (G3): the packed-place record equality needs the packing function in Lean first; only its bound minFac y <= sqrt q is proven (Gems.small_block_le_sqrt). Row 141 (G5): a finite list of ten off-strand breakers to 10^6, not a general statement.
| 142 | §35 | One formula: seat n = 6k+f is prime iff no block 6j+g with (6j+g)^2 <= n divides k - f g j; p_n + 1 = #{a <= 2^(n+1) : pi(a) <= n} | P (v5.5) | WallFormula.wall_formula, nth_prime_formula, nth_prime_le_pow; FableImprovements.prime_count_walls (= Nat.primeCounting), prime_iff_passes | a computation, said plainly |
| 143 | §35 | Walls and RH: from the proved Riemann hypothesis, |wall count - Li(N)| <= C N^(1-delta) for some delta > 0 | P (v5.7) | WallsMeetRH.walls_meet_rh (walls-meet-rh/WallsMeetRH_v1.0_11-27-2026.lean, checked in the environment of leanprover-community/riemann-hypothesis) | consequence of RH via Tau Ceti Ingham transfer; sqrt(N) log^2 N not yet formalized |
| 144 | §35 | Walls and RH, sharp: |W(N) - Li(N)| <= C N^(1/2+delta) for every delta > 0, and <= C sqrt(N) (log N)^2 for N >= 55 | P (v5.8) | WallsMeetRHSharp.walls_meet_rh_half, walls_meet_rh_sqrt (walls-meet-rh/WallsMeetRHSharp_v1.0_11-27-2026.lean, RH environment) | consequence of the proved RH; von Koch exact psi form and Schoenfeld constants not formalized |
| 145 | §35 | Walls and RH, von Koch: |W(N) - Li(N)| <= C sqrt(N) log N for N >= 55; psi(x) - x = O(sqrt x log^2 x) | P (v5.9) | WallsMeetRHVonKoch.walls_meet_rh_sqrt_log, psi_sub_le_sqrt_log_sq_of_RH, primeCounting_sub_logIntegral_le_sqrt_log_of_RH (RH environment) | truncated explicit formula, residues at the zeros on Re 1/2; Schoenfeld constants not formalized |
| 146 | §35 | Wing families and GRH: each wing family 6k-1, 6k+1 holds Li(x)/2 + O(sqrt x log^2 x) primes; the lead of 6k-1 over 6k+1 is at most C sqrt x log^2 x | P (v5.9) | WingFamiliesGRH.wing_families_meet_grh, wing_count_sub_half_li, wing_lead_le (RH environment) | the sign of the lead is not decided by GRH; measured never behind to 10^7 (row 135) |

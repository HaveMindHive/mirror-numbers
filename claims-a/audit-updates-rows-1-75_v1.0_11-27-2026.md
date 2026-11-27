# Audit updates, rows 1 to 75 (claims A), 11-27-2026

For merging into `claim-audit_v1.0_11-26-2026.md` (the audit itself is not touched here).

- New module: `lean-mirror-numbers-all_v1.0_11-26-2026/MirrorNumbersAll/ClaimsA.lean` (987 lines, 98 theorems, namespace `ClaimsA`). Imports Upgrades, PrimeHandOff, PySRFinds, UnitCountingLaws. SHA-256 `ea3eabfcf42fc8fa4da7edb37c0bc76a3fa8211adffceffa08e9e344ee5f6c4e`.
- Compiled with `lake env lean MirrorNumbersAll/ClaimsA.lean`: 0 errors (warnings are deprecations and style only). It is not yet in the root import list and has not been through `lake build`; the main session adds it.
- No sorry, no admit, no native_decide. `decide +kernel` is used for the finite tables (rows 58, 71).
- Axioms: `claims-a-axiom-check_v1.0_11-27-2026.txt`, which has 98 lines, one per theorem. Every theorem uses only propext, Classical.choice and Quot.sound, and 13 use none.
- Exact computations: `claims-a-exact_v1.0_11-27-2026.py` (SHA-256 `4b4edb7259e22fe8f0e2e463ebc20ea3cb44725d17a9b04ba0826bdc28dc730d`) and its output `claims-a-exact-output_v1.0_11-27-2026.txt` (SHA-256 `7ad3df709896335e67f6dff395a8f9e49aa68a3998eead61304a388c4e01025f`). It runs in under a second and every check is an assert.

New class key: **P** means proven in Lean. **P + exact** means the mathematical statement is proven and a finite remainder is settled by the frozen script. **D/P** means the definition stays a definition and its stated examples or properties are proven.

| # | Old | New | ClaimsA theorem(s), or why it stays |
|---|-----|-----|-------------------------------------|
| 1 | D | D/P | `words_mirror_units`, `mirror_words_are_words`: 000, 010, 101, 111 are exactly the three-digit 0/1 mirrors, and the word of n holds n units. The names (0_n, 0_a, 1_u, 1_c, wing, centre, hinge, comma, marks) stay notation. |
| 2 | D | D | A table of names with no mathematical statement. |
| 3 | D | P | `containment`: unitProd [1,n] = unitProd [n,1] = n for n not 1. |
| 4 | D/P | P | `bare_units` (n bare units give n, every n), `bare_units_small`; with UnifiedCode.face_bare_units. |
| 5 | D | P | `whole_expression_examples`, `unitProd_perm`, `PExpr`, `grouping`, `grouping_swap`, `one_one_one_grouped`. The reading of 1 x (1+1) as "1,2, then 3" stays R, because it reads a sum inside a product, which the rule does not model. |
| 6 | D/R | P | `agreement` (a factor holding the unit gives the ordinary product), `no_distributive`. The near-ring and octonion remark stays R. |
| 7 | D/R | D/P | `two_over_one` (x x 1 = 2 iff x = 1 or 2), `over_one` (2 is the only two-valued n/1), `one_pow_count`, `one_pow_zero`, `pow_count`. The values 1/1 = 1, inf/inf, 0_a/0_a = 1 and 0_n/0_n = 0_n stay definitions. Note: under the rule, x x 1 = 1 has no solution (1 x 1 = 2), so 1/1 = 1 is a definition and not a solve. |
| 8 | D | P | `count_root`: for n >= 1, x^n = n under the rule iff x = 1. |
| 9 | C | P + exact | `measure_root_peak` (n^(1/n) < 3^(1/3) for every whole n >= 1, n not 3), `cube_lt_three_pow`, `two_four_tie`, `measure_root_ne_one`. The decimals are an exact computation: each printed decimal is a double-precision reading within one unit of its last place of the 60-digit true value. 2^(1/2), 3^(1/3), 6^(1/6), 7^(1/7), 10^(1/10) and sqrt2 print the nearest double, which differs from correct rounding in the last digit. Peak of x^(1/x) at e over the reals: the derivative zero, computed. |
| 10 | C | P + exact | `yardsticks` (2 sqrt(n/2)^2 = n, (sqrt3/sqrt2)^2 = 3/2, sqrt(2/3) (sqrt3/sqrt2) = 1, (1/sqrt2)^2 = 1/2, sqrt(1/2) = 1/sqrt2), `cube_diagonals`. Decimals as in row 9. 1/sqrt2 prints 0.7071067811865475, which is the correct rounding; the nearest double prints ...476. |
| 11 | D/C | P | `B_examples` (4, 5, 6, 17 as printed), `B_digits` (every digit is 0 or 1). |
| 13 | D | P | `T`, `T_base`, `T_even`, `T_odd` (recursion for k >= 2, every k). |
| 14 | D/P | P | `rewrite_words`, with UnifiedCode.step and order_one_words. |
| 19 | C | P | `eleven_wing`, every order d: the left wing of 11 holds 10 ones and (27 3^d - 1)/2 - 10 zeros. `eleven_wing_zeros` gives 3, 30, 111. Supporting lemmas: `leftWing_step`, `leftWing_order`. |
| 20 | D/R | R | A rule of the notation (mixing orders is not allowed) and a shape remark on Cantor; no statement to prove. |
| 21 | C | P | `palCount_table` (L = 2, 3, 4, 5, every weight). |
| 23 | D/P (new) | P | Already proven: UnifiedCode.blocks3, words3, order_one_words. |
| 32 | R | P (corrected) | **False as written**: the row's list {3^k, 2 3^k} is not the full set; 5 has no excess. Corrected statement, proven: the ternary build has no excess at any n (`ternary_no_excess`). `five_not_three_pow` is the counterexample. Paper v5.8 already says this. |
| 34 | R | P | `prime_mirror_not_three_eleven`: if p is prime and p >= 100, its digit mirror is divisible by neither 3 nor 11. |
| 36 | R | P | `seven_segment_swap`: the top-bottom and left-right mirrors of the seven segments swap 2 and 5. The segment model is in the docstring. |
| 38 | R | R | "First share a block" is not defined precisely in the paper; the level formula itself is row 37 (P). |
| 39 | D/C | P | `rep`, `leaf`, `face` (match fold_build_v2.1 `face`), `face_twelve` (the 12 example). |
| 40 | C | P + exact | Every arrangement, every n: `face_sum` (a face holds exactly n ones), `face_reverse` (mirror), `composite_face_not_leaf` (no face with two or more factors is the string of any prime leaf; via `leaf_no_nine`, `nine_in_face`). "Every arrangement its own string" is an exact computation for n = 2..1999, 17177 faces. |
| 41 | R | P | `v20_error` (with the first gap at 000, 5 copies of 7 is exactly the prime string of 35), `rep_rep` (one fixed gap flattens copies of copies), `twentyfour_flattens`. The "why" sentence stays as a reading. |
| 43 | D | D/P | `markR`, `markL`, `foldWhole`, `half_words`, `mark_examples` (4 = 10\|,00\|,\|01; 4 = 101,000,\|; 8 unfolds to 101,000,101,000,101,000,101; 8 = 4,,0,,\|). The comma display stays notation. |
| 45 | C | P | `marked_unfolds`, **every n** (the script checked n < 400): the mark rule of eleven-mirror_v1.0 (xy\|, \|yx, x\|x, x\|1\|x) unfolds to B(n). Also `marked_eleven`, `eleven_marked`, `B_words`, `unmark_markWord`. Commas are separators and are not modelled. |
| 47 | D/P | P | `cube_form` (a,\|a\|,a = a^3 for a not 1), `cube_examples` (8, 27, 64; 1,\|1\|,1 = 3). |
| 48 | D/C | P | `neighbours`, every n and every level: each block at level d is n/2^d or n/2^d + 1. Also `lvl_nineteen`, `ladder_examples` (19, 97). |
| 49 | P (v5.4) | P | Unchanged (PySRFinds.ladder_ends_two_three, ladder_ends_one_two, ladder_length). The row text needs `2\|3` escaped: the bare pipe breaks the table columns. |
| 50 | D/C | P | `u_values` (u(1..16)), `u_nineteen` ((2,3) -> (4,7) -> (15,14) -> 44). |
| 51 | R/M | R/M | Absence from the OEIS is a dated search result, not a theorem. The shared k, k+1 shape is a description. |
| 58 | C | P | `decimal_mirrors_below`: for 10 <= n < 2^20, n is a decimal mirror below the line iff n is one of 11, 22, 33, 44, 66, 88, 272, 2112, 4224, 8448. This uses `below_shape` (every n: below the line iff n = 2^j m, m on a strand or a pair point), `u_pow_mul`, `dig_eq`, `pal_iff`, and `ok_pow`, `ok_eleven`, `ok_fifteen`, `ok_strand_one`, `ok_strand_two` (decide +kernel). The old script ran to 10^6; this covers the full 2^20. |
| 63 | D/C | P | `otimes`, `even_line_product`, `two_p_even_world`, `first_part_eighteen`, `splits_examples`. **Correction**: 180 has three splits (2 x 90 = 6 x 30 = 10 x 18) and the paper lists two. "First part at 18" holds with p odd; 4 = 2 x 2 is twice a prime but not an even-line prime. |
| 65 | R | P | `one_mod_four_iff_two_squares`, `odd_midpoint_iff_two_squares`. This is the same set Fermat and Euler reached by another route; Mathlib's Nat.Prime.sq_add_sq gives one direction. |
| 68 | D | P | `paradox` (9,9,9 reads 18 as a reflection and 27 as a turn; 1,1,1 reads 2 and 3). |
| 69 | P/C | P | `imb_zero_iff` (no imbalance exactly at 0, 2^a, 3 2^a), `twentytwo_imb` (imb 22 = 18, u 22 = 40). |
| 71 | P/M (v5.4) | P + exact | `twentyseven_marks` (27: 189 symbols as a reflection, 49 as a turn; `markRf` is notation A of two-mirrors_v1.0), with PySRFinds.markT_length. "Both notations decode" is an exact computation for n = 1..2999. |
| 72 | D/P (new) | P | Already proven: UnifiedCode.read, read_one, read_step. |

Rows already P and unchanged: 12, 15, 16, 17, 18, 22, 24, 25, 26, 27, 28, 29, 30, 31, 33, 35, 37, 42, 44, 46, 49, 52, 53, 54, 55, 56, 57, 59, 60, 61, 62, 64, 66, 67, 70, 73, 74, 75.

Totals: 30 rows moved to P (3, 4, 5, 6, 8, 9, 10, 11, 13, 14, 19, 21, 23, 32, 34, 36, 39, 40, 41, 45, 47, 48, 50, 58, 63, 65, 68, 69, 71, 72; rows 9, 10, 40 and 71 are P + exact). 3 rows moved to D/P (1, 7, 43). 4 rows stay as they were, each for the reason given (2, 20, 38, 51).

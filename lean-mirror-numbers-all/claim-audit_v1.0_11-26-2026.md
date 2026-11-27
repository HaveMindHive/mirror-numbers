# Claim audit: unit-counting-paper v5.8 (11-27-2026; first made for v5.1, 11-26-2026)

Paper: `unit-counting-paper_v5.1_11-26-2026.tex`. Library: `lean-mirror-numbers-all_v1.0_11-26-2026` (one Lake project, 15 modules; `Gems` added 11-27-2026).

Build: `lake build` clean (18208 jobs, exit 0; log `lean-build-log_v1.0_11-26-2026.txt`); rebuilt with `Gems` 11-27-2026 (18210 jobs, exit 0; log `lean-build-log_v1.1_11-27-2026.txt`). Axioms: 308 + 22 theorems printed, every one on propext / Classical.choice / Quot.sound only (`lean-axiom-check_v1.0_11-26-2026.txt`, Gems block appended at the end); no sorry, no admit, no native_decide in any module.
"P (gem)" = proven 11-27-2026 in module `Gems` from the PySR gems file (`gems-for-lean_v1.0_11-26-2026.txt`).

Classes: **P** proven in Lean (module.theorem) · **C** checked by computer to a stated range · **M** measured share or count · **D** definition or notation · **R** reading or theoretical note.
"P (new)" = proven in this job (modules `UnifiedCode`, `PrimeHandOff`); the earlier range check is listed in the note.

| # | Section | Claim | Class | Lean theorem(s) / check | Note |
|---|---------|-------|-------|-------------------------|------|
| 1 | Terms | Two zeros 0_n, 0_a; two ones 1_u, 1_c; words 000, 010, 101, 111; wing/centre/hinge; comma; marks | D |  |  |
| 2 | §1 | Table of two zeros and two ones | D |  |  |
| 3 | §2 | Containment: 1 x n = n for n > 1 | D |  | counting rule, by definition |
| 4 | §2 | Bare units: 1 x 1 = 2, 1 x ... x 1 (n times) = n | D/P | UnifiedCode.face_bare_units, face_product, face_prime | the rule `unitProd` on a three-factor face: bare units count (1,\|1\|,1 = 3), a factor holding the unit multiplies |
| 5 | §2 | Whole-expression rule; grouping does not change a result | D |  |  |
| 6 | §2 | No distributive law; agreement with ordinary arithmetic off bare units | D/R |  |  |
| 7 | §3 | 1/1 = 1, inf/inf = inf, two-valued 2/1, 0_a/0_a = 1, 0_n/0_n = 0_n, 1^n = n, 1^0 = 0_n | D/R |  |  |
| 8 | §4 | Count root of n of order n is 1 | D |  |  |
| 9 | §4 | Table of n^(1/n) decimals; peak at e; e^(1/e) = 1.4446... | C | numeric | decimal values |
| 10 | §4 | Two yardsticks: sqrt(3)/sqrt(2), sqrt(2/3) = 0.8164..., 1/sqrt(2) | C | numeric |  |
| 11 | §5 | Halving build B(2k) = B(k),0,B(k); B(2k+1) = B(k),B(k+1),B(k); examples 4, 5, 6, 17 | D/C | fold_build_v2.1 | B has leaves 1, 2, 3 |
| 12 | §5 | Every build is a mirror with one hub; even hub is the zero, odd inherits | P (v5.4) | Upgrades.B_reverse, B_length, hub_even, hub_odd | B matches fold_build_v2.1 |
| 13 | §5 | T(1)=T(2)=T(3)=1, T(2k) = 2T(k)+1, T(2k+1) = 2T(k)+T(k+1) | D |  |  |
| 14 | §6 | Rewrite 0 -> 000, 1 -> 010; order-1 words | D/P | UnifiedCode.order_one_words, words3 |  |
| 15 | §6 | Rewrite before build = rewrite after build (n < 300, orders 0..2) | P (new) | UnifiedCode.levels_succ, levels_succ_step, step_eq_level | one level deeper = one order of the rewrite once the string is in digits (every n, every level, both block rules) |
| 16 | §6 | Units stay fixed across orders | P (new) | UnifiedCode.step_sum, order_keeps_units |  |
| 17 | §6 | A one at digit i moves to digit 3i+1 | P (v5.4) | Upgrades.step_position, one_moves, centre_stays | position law not formalized |
| 18 | §6 | Length triples per order; centre stays the centre | P (new) | UnifiedCode.step_length, step_reverse | mirror kept and width tripled; the centre index is implied |
| 19 | §6 | Left wing of 11: 10 ones; 3, 30, 111 zeros at orders 0, 1, 2 | C |  | zeros of the whole string = 3^d - n is P (levels_length + levels_sum) |
| 20 | §6 | Mixing orders not allowed; Cantor remark | D/R |  |  |
| 21 | §7 | Mirror-word counts for L = 2, 3, 4, 5 | C | UnitCountingLaws.palCount (decide) | L = 1, 3 and "not triaxial for L = 2..8" are P |
| 22 | §7 | Triaxial theorem: one mirror word per unit count iff L in {0, 1, 3}; two words of weight 2 for L >= 4 | P | UnitCountingLaws.triaxial_iff, two_le_palCount_two, not_triaxial_of_four_le |  |
| 23 | §8 | Ternary build k,k,k / k,k+1,k / k+1,k,k+1; level one gives the four words; level two the order-1 words | D/P (new) | UnifiedCode.blocks3, words3, order_one_words |  |
| 24 | §8 | Every ternary string is a mirror (n <= 729) | P (new) | UnifiedCode.tern_reverse | every n, every level |
| 25 | §8 | Each number has its own string | P (new) | UnifiedCode.levels_inj |  |
| 26 | §8 | Units equal n exactly, no excess (n <= 729) | P (new) | UnifiedCode.tern_sum | every n, every level |
| 27 | §8 | One level deeper = one order of the rewrite | P (new) | UnifiedCode.levels_succ_step |  |
| 28 | §8 | Centre unit exactly when n is odd | P (new) | UnifiedCode.centre_eq_parity |  |
| 29 | §8 | Odd 2k+1 as k,k+1,k is the one source of excess | P | TwoMirrors.u_eq_add_imb, imb_odd | excess = wings of filled-centre triples |
| 30 | §8 | Octave [2^k, 2^(k+1)) holds (17 5^(k-1) - 2^k)/3 units; x5 against x4; drift 5/4 | P (new) | UnifiedCode.S_succ, octave_sum, octave_sum', octave_values; Gems.octave_from_blocks | S(k+1) = 5 S(k) + 2^k; 3 S(k) + 2^k = 17 5^(k-1), k >= 1 (Python asserted a = 1..22); second route 11-27: the octave is the c = 2 block beside the c = 3 block of G2 |
| 31 | §8 | No-excess numbers of the binary build: {2^k, 3 2^k} | P | RatioTwoLine.fixed_iff |  |
| 32 | §8 | No-excess numbers of the ternary build: {3^k, 2 3^k} | R |  | as defined, the ternary build has zero excess at every n (tern_sum); this sentence needs his reading of "excess" for the ternary case |
| 33 | §9 | Mirror remainders: same mod 9; mod 11 same for odd digit count, opposite for even | P | UnitCountingLaws.mirror_mod_nine, mirror_mod_eleven_odd, mirror_mod_eleven_even |  |
| 34 | §9 | A prime of >= 3 digits: its mirror is not divisible by 3 or 11 | R | corollary of row 33 | not stated separately in Lean |
| 35 | §9 | 2 and 5 through 10: odd orders of 2 and 5 give odd order of 10; even period means not both odd; odd period means equal 2-adic parts | P | UnitCountingLaws.even_period_law, even_period_never_both_odd, odd_period_law |  |
| 36 | §9 | Seven-segment mirrors swap 2 and 5 | R |  | visual |
| 37 | §9 | Carry level: one integer in (x, y] carries the top power of 2, which is 2^floor(log2(x xor y)) | P | UnitCountingLaws.carry_level_law, xor_log_split |  |
| 38 | §9 | ... the level at which the builds of x and y first share a block | R |  | reading of row 37 |
| 39 | §10 | Divisor build: d copies of m, zero growing one order per level; 12 example | D/C | fold_build_v2.1 (faces) |  |
| 40 | §10 | Every face has n ones, is a mirror, is its own string, no composite face reads as a prime (n < 2000) | C | fold_build_v2.1 | copies face sum d m = n is P (UnifiedCode.face_copies); the growing-zero string itself is not formalized |
| 41 | §10 | Why the zero grows; the 35 error of v2.0 | R |  |  |
| 42 | §11 | Equal-width zoom: every width a power of 3 | P (new) | UnifiedCode.levels_length, code_length | 3^d at level d |
| 43 | §11 | Mark rules; half-words give the four words; commas count the zoom; 17 example | D |  |  |
| 44 | §11 | Width steps up exactly after 3 2^k (4-6: 9, 7-12: 27, 13-24: 81, 25-48: 243) | P (v5.4) | Upgrades.width_closed, width_words | W matches facing-number-line zoom for n < 3000 |
| 45 | §11 | Mark rule; marked string unfolds to the build (n < 400); 11 example | C | facing scripts |  |
| 46 | §11 | Centre digit a unit only for 1, 3, 2^m+1 (n < 600) | P (v5.4) | Upgrades.centre_unit_iff | every n |
| 47 | §11 | Cube form a,\|a\|,a = a^3; 1,\|1\|,1 = 3 | D/P | UnifiedCode.face_product, face_bare_units |  |
| 48 | §12 | Only neighbours k, k+1 occur at each level; ladder shorthand; 19, 97 examples | D/C | ladder-shorthand script | structural, by construction |
| 49 | §12 | Every ladder ends in 2\| P (v5.4) | PySRFinds.ladder_ends_two_three, ladder_ends_one_two, ladder_length | ranges for M >= 2 | ladder-shorthand script |  |
| 50 | §12 | u recursion; u(19) = 44; sequence values | D/C | Gems.two_point (closed form on every block c 2^a + j) | the listed values stay a list; the law behind them is row 138 |
| 51 | §12 | u shares the k, k+1 shape with Stern's diatomic; not in OEIS | R/M |  |  |
| 52 | §13 | u(n) = n iff n = 2^a or 3 2^a; otherwise 5u >= 7n | P | RatioTwoLine.fixed_iff, dich |  |
| 53 | §13 | u(n) is not 2n for n >= 1 | P | RatioTwoLine.u_ne_two_mul |  |
| 54 | §13 | u(2^a+1) = 2^(a+1) - 1; u(3 2^a + 1) = 2(3 2^a - 1) | P | RatioTwoLine.u_pow_add_one, u_three_pow_add_one; Gems.strand_pow, strand_three_pow, strands_agree | second route 11-27: both strands are the j = 1 case of G1 (Gems.u_pow_one) at c = 2, 3 |
| 55 | §13 | Odd n below 2n iff 2^a+1, 3 2^a+1 (a >= 1) or 1, 11, 15 | P | RatioTwoLine.ratio_two_line, below_strand, strand_below |  |
| 56 | §13 | 11 and 15 forced as pair points | P | TurnRoots.pair_point, eleven, fifteen; ManyTurns.below_classify |  |
| 57 | §13 | u(n) = 2(n-1) at 2, 11, 15 and at no other n < 2^20 | P (new) | PrimeHandOff.two_eleven_fifteen | every n >= 1, from the ratio-two classification and the mod-2 law |
| 58 | §13 | Decimal mirrors below the line to 2^20: 11, 22, 33, 44, 66, 88, 272, 2112, 4224, 8448 | C |  | finite list |
| 59 | §13 | u/n = 20/11 on 11 2^j and 21/11 on 33 2^j | P (new) | UnifiedCode.u_eleven_pow, u_thirtythree_pow |  |
| 60 | §13 | Mod-4 law: odd u exactly at 1 and 2^a+1; 2 mod 4 exactly at 3 2^a+1; else 4 divides u | P | TwoMirrors.u_odd_iff, u_two_mod_four_iff, strand_law_odd, four_dvd_rest |  |
| 61 | §13 | 11 and 15 first odd numbers with exactly one factor 4 | P (v5.4) | Upgrades.first_four_factor |  |
| 62 | §13 | The factor comes from 2u(n) - u(n+1) = 4u(k) at n = 2k+1 | P | TwoMirrors.d_odd, d_even |  |
| 63 | §14 | Even line: a (x) b = 2ab; two readings of "even prime"; first part at 18; 36, 60, 180 | D/C | even-primes script |  |
| 64 | §14 | Midpoint k+1 even iff p = 3 mod 4 | P | RuleHierarchy.even_centre_iff |  |
| 65 | §14 | p = 1 mod 4 iff p = x^2 + y^2 | R |  | same fact by another route (Fermat, Euler); not invoked in Lean |
| 66 | §15 | Reflection reading gives n for every n | P (new) | UnifiedCode.read_halving_odd, read_halving_even, face_reflection_odd/even |  |
| 67 | §15 | Turn reading gives n; ternary digits hold n units (n < 3000) | P (new) | UnifiedCode.read_turn, tern_sum |  |
| 68 | §15 | Paradox: 9,9,9 as reflection is 18; 1,1,1 as reflection is 2 | D |  |  |
| 69 | §15 | Imbalance = u(n) - n; 2^a and 3 2^a have none; 22 example | P/C | TwoMirrors.u_eq_add_imb |  |
| 70 | §15 | Pure halving v: v(n) = n at 2^a; v is not 2n; odd below 2n exactly 1, 7, 2^a+1 | P | TwoMirrors.v_fixed_iff, v_ne_two_mul, v_below_iff |  |
| 71 | §15 | Both mark notations decode (n < 3000); 27: 49 vs 189 symbols | P/M (v5.4) | PySRFinds.markT_length, markT_27 | turn mark length 2 3^k - k - 2 |
| 72 | §16 | Picture rule a,b,a:s = b + (s-1)a; scale 1 the centre | D/P (new) | UnifiedCode.read, read_one, read_step |  |
| 73 | §16 | Every halving and thirding form reads n (n < 5000) | P (new) | UnifiedCode.read_halving_odd/even, read_turn |  |
| 74 | §16 | 1,1,1 -> 1,2,3; 2,3,2 -> 3,5,7; 9,9,9 -> 9,18,27 | P (new) | UnifiedCode.read_examples |  |
| 75 | §16 | Wing-2 picture gives three primes only at 2,3,2 | P (new) | UnifiedCode.wing_two_primes | b, b+2, b+4 prime forces b = 3 |
| 76 | §16 | Halving and thirding share wings exactly at 2, 3, 5 | P | TwoMirrors.shared_wings |  |
| 77 | §16 | Arrows: operator in, observer out; k -> k<1> = 2k+1 | D |  |  |
| 78 | §17 | First mirror; stopping at 2, 3 leaves the first false prime at 25; each mirror moves it to the next prime squared | C/R |  | the mirrors and their reading are the author's |
| 79 | §17 | Centre first-mirror counts to 10^6: 39321 (2), 19610 (3), 4868 (5), 2478 (7), 4299 prime | M |  |  |
| 80 | §17 | Longest operator strand below 10^6: 16651 -> ... -> 532801 | M |  | Cunningham chains of the second kind, by another route |
| 81 | §18 | One code w,c,w; 8, 7, 11 examples | D/P (new) | UnifiedCode.blocks2, code_examples |  |
| 82 | §18 | Every number holds exactly itself in units | P (new) | UnifiedCode.code_sum, code_reverse | every n, every level |
| 83 | §19 | p = \|w; strand rule w = a m + (m-1)/2; strands of 3, 5, 7 | D |  |  |
| 84 | §19 | Open wings are prime seats; next prime = first open seat (3..10^4; 10^9..10^9+2 10^4) | P (v5.4) | Upgrades.open_iff_prime, missing_iff_not_prime; WallWalk.wall_walk | every wing; walk exact to 1e12 and 1e9 seats below 2^64 (wall-walk-max) |
| 85 | §19 | 148932 open wings to 10^6; 74416 even, 74516 odd | M |  |  |
| 86 | §19 | Even open wings belong to primes that are sums of two squares, odd ones do not (w < 50000) | P (v5.4) | Upgrades.even_wing_iff_two_squares, two_squares_mod_four | sum of two squares proven; a+-bi split read from it |
| 87 | §20 | Centre seat fixes half-gap seat (four cases, every gap to 10^6) | P (new) | PrimeHandOff.centre_fixes_half_gap, hand_off_primes; HandOff.two_hand_off, three_hand_off; FableImprovements.hand_off_every_block, hand_off_primes' | every pair of primes 3 < p < q |
| 88 | §20 | 2k and 2k+1 share the wing k; the right side is broken | D/R |  |  |
| 89 | §20 | Walker names q in all 78495 gaps to 10^6 | M |  |  |
| 90 | §20 | Blocks cross only through the centre (194071 pairs, 46084 shared) | P/M | HandOff.never_both; PrimeHandOff.never_both_primes | structure P, counts M |
| 91 | §20 | Prediction shares 78.3 / 60.3 / 49.7 % vs 31.3 / 24.3 / 20.1 %; misses before q | M |  |  |
| 92 | §21 | Even-line primes are odd places, a fixed quarter floor((X+2)/4) - 1; multiple builds; leaders to 10^6 | P/M (v5.4) | PySRFinds.evenWorldPrime_iff, even_world_count | quarter (X+2)/4 - 1 proven; leaders measured |
| 93 | §21 | 4w+2 is twice a prime iff w is open (to 10^6) | P (v5.4) | Upgrades.twice_prime_iff_open |  |
| 94 | §21 | Unit remarks: 2 (x) 2 = 4; with 2 as the unit the rule is lost | R |  |  |
| 95 | §21 | 2p sits between a shallow and a deep left-out; deep side by p mod 4; depth = halvings + 1 (p < 2 10^5) | P (v5.4) | PySRFinds.depth_one_mod_four, depth_three_mod_four | every odd p >= 5 |
| 96 | §22 | Three faces: commas add, bars multiply, facing wings reflect; every face reads n (n < 3000) | P (new) | UnifiedCode.face_add, face_copies, face_product, face_reflection_odd/even |  |
| 97 | §22 | 3 = 1,1,1 = 1,\|1\|,1 = \|1,2\|,\|1; 18 four ways | P (new) | UnifiedCode.eighteen_faces, face_bare_units |  |
| 98 | §22 | 1 has no product face; a prime's product face is 1,\|p\|,1 | P (new) | UnifiedCode.face_bare_units, face_prime |  |
| 99 | §23 | Halving shows the neighbours, which share no block with n; 55 example | P/C | TwoParts.neighbour_up, neighbour_down |  |
| 100 | §23 | centre^2 - wing^2 = n; faces are pictures one to one; a prime has one picture | P | TwoParts.halving_square, face_square, face_block, centre_gap, prime_one_picture |  |
| 101 | §23 | Mark \|^x = x(b+1); 11, 101, 55; 3, 5, 9, 17, 33 in base 2 | D/P (new) | UnifiedCode.mark, mark_base_two, mark_examples |  |
| 102 | §23 | 22 = 11,0,11 and 23 = 11,1,11 as pictures of 2 and 3 | D |  |  |
| 103 | §23 | (k ones)(10^(k-1)+1) = (k-1 ones) 2 (k-1 ones) | P | TwoParts.repunit_mirror, eleven_unit |  |
| 104 | §23 | 7^2 = 2 5^2 - 1; (3,2), (17,12), (41,29) | P (v5.4) | Upgrades.ladder_sign, ladder_rungs, seven_five | Pell numbers by another route |
| 105 | §24 | Every set of turns: u is not 2n; self-count numbers c 2^a; odd non-turn below the line is strand, pair point 4j+3 or near-turn; nothing below 3/4 | P | ManyTurns.line_never, below_classify, three_quarter, no_sporadic; TurnRoots.odd_fixed, pow_fixed |  |
| 106 | §24 | t = 2^b+1 makes 4t-1, t = 2^b-1 makes 4t+3; 3 makes 11 and 15 | P | TurnRoots.pair_point (general), eleven, fifteen, nineteen, thirtyone, seven |  |
| 107 | §24 | Seat rule h = -p 2^(-1) mod r; 5: 2p, 7: 3p, 11: 5p, 13: 6p | P | RuleHierarchy.five_class, seven_class, eleven_class, thirteen_class |  |
| 108 | §24 | Rules stack in size order; block r above the hand-off from two seats per run of 6r | P | RuleHierarchy.five_above_handoff, seven_above_handoff, eleven_above_handoff, allowed_mod_30 |  |
| 109 | §24 | Block r takes 1/(r-1) of what is left: 0.2503, 0.1250, 0.0626 to 10^6 | P/M (v5.4) | PySRFinds.above_classes, off_classes, above_share, stack_seven, stack_eleven | exact 1/(r-1) over each run of 6r, every prime block; measured shares kept |
| 110 | §24 | Offset-11 mirror, per-block mirror, lake change the picture, not the verdict | P/R | RuleHierarchy.offset_keeps_gap, block_mirror_even; WallMirror.block_mirror_hop, lake_centre |  |
| 111 | §24 | Hop: h = 3w + 2s, s in {-1,0,1}; side flips iff w odd; facing flips iff s is not 0 | P (new on primes) | WallMirror.half_gap_walls, step_cases, side_is_walls, facing_is_step; PrimeHandOff.hop_primes; FableImprovements.hop_reads_centre, hop_and_hand_off | now stated for primes 3 < p < q |
| 112 | §24 | Wall-free hop of 4 leaves 6k+1 and lands on 6k-1 | P | WallMirror.no_wall_needs_first_seat, no_wall_lands_last_seat |  |
| 113 | §24 | Flip counts 22837/22838 and 22572/22571 to 10^6; differ by at most one on any walk | M/P | WallMirror.flips_balance, flips_balance_bound; Gems.gap_class_balance_exact, gap_class_balance, gap_class_balance_primes | gap reading 11-27 (G4): #(gap = 2 mod 6) - #(gap = 4 mod 6) = [p_0 = 5 mod 6] - [p_n = 5 mod 6] on any walk of seats off 2 and 3, so in {-1, 0, 1}; the counts stay M |
| 114 | §24 | Range table 28/50 ... 1/2; chance 0.39-0.45 nearly flat | M |  |  |
| 115 | §25 | Offset-11 pairings; 22; 33; 66 | C | offset-eleven script | finite lists |
| 116 | §25 | Odd offsets pair odd with even, even offsets keep parity | P | TwoZero.odd_offset_crosses_parity, mirror_keeps_parity |  |
| 117 | §25 | First crossings 33 <-> 22, 73 <-> 70; Lemoine, Goldbach | C/R |  |  |
| 118 | §26 | (\|^1)^2 = 1,2,1 and (\|^1)^3 = 1,3,3,1 in its base; 9, 121, 1331 | P | NineCubes.mark_square, mark_cube; UnifiedCode.mark_sq_digits (b >= 3), mark_cube_digits (b >= 4) | digit lists now P |
| 119 | §26 | Two-digit reversal: sum is 11 x digit sum, difference 9 x digit difference; nines reverse on the 11-line | P | NineCubes.rev_sum, rev_diff, nine_rev, eighteen_rev |  |
| 120 | §26 | A cube carries its root's halving scaled; its halving reads p^2 +- p + 1 | P | NineCubes.cube_picture, cube_halving |  |
| 121 | §26 | Squares of 3, 5, 7 sit one past a wall; no other prime below 1000 does | P (v5.4) | Upgrades.square_past_self_counting_iff; NineCubes.nine_self_counting | self-counting numbers 2^a, 3 2^a; every prime |
| 122 | §26 | Sums of two cubes are composite except 1^3 + 1^3 = 2; first two are 2 and 9 | P (v5.4) | Upgrades.cube_sum_prime_iff, cube_sum_first_two |  |
| 123 | §27 | Construction names every prime to 10^7 (664579), at most 213 places; 23, 167, 9403, 100483, 1018057 | P/M (v5.4) | WallWalk.wall_walk | naming exact for every n proven; place counts measured |
| 124 | §28 | 0 = -1,0,1 and 2 = 1,0,1 one picture | P | TwoZero.two_pictures |  |
| 125 | §28 | 2 the prime with the hinge; every other prime has the unit at its centre; reads 1 from 2's mirror | P | TwoZero.hinge_prime, odd_prime_unit_centre, odd_prime_reads_one |  |
| 126 | §28 | Primes past the stacks sit on seats coprime to 6, 30; mirror r <-> W - r keeps parity, none its own mirror | P | TwoZero.stacked_six, stacked_thirty, mirror_keeps_parity |  |
| 127 | §28 | Within half a turn of 6, 30, 210 every open seat is 1 or a prime; frays at 2310 at 169 | P | TwoZero.near_zero_seats_210, fray_at_2310 | 6 and 30 are the small cases of row 126 |
| 128 | §28 | ... holds while W/2 is below the next block squared | R |  | general criterion, reading |
| 129 | §28 | Twins straddle a multiple of 6; 6k-1: p-2 on 3's zero; 6k+1: p+2 (to 10^7) | P | TwoZero.twin_straddles_wall; TheSolve.two_step_minus, two_step_plus | every k |
| 130 | §29 | Wall law: r = 6kr + fr closes wing f of wall k iff k = f fr kr (mod r); one residue for both wings (blocks 5..281, walls to 200000) | P (new on primes) | TheSolve.wing_identity, wing_closed, wings_mirror, wall_reads_both_wings, five_closes, seven_closes; PrimeHandOff.wall_law_prime, wall_both_wings_prime; FableImprovements.wall_law_width, wall_law_six, wall_law_inverse (any width, no coprimality clause) | every prime block r >= 5 and every wall |
| 131 | §29 | Two families one strand through zero; equal count under negation | P | TheSolve.family_through_zero, neg_swaps_family, family_count_mirror |  |
| 132 | §29 | Hop 2h = 6w + (f_q - f_p) | P (new on primes) | TheSolve.hop_wall_frame; PrimeHandOff.hop_facings; FableImprovements.hop_and_hand_off |  |
| 133 | §29 | Facing flips ~57%; side kept 47.5% / 38%; same wall 20% from 6k-1, none from 6k+1 (to 10^7) | P/M (v5.6) | FableImprovements.same_wall_twin | "none from 6k+1" proven: primes sharing a wall are 6k-1, 6k+1; the shares stay measured |
| 134 | §29 | Next prime within 1/1, 2/4, 3/5, 3/6 seats (90/99%) by band; walls at half the reading cost | M |  |  |
| 135 | §29 | 6k-1 leads 6k+1 in every band (22, 34, 189); offset 66 pairs equal; lead rides in the qQq | M/R |  | Chebyshev's bias by another route |
| 136 | §30 | The method as waves | R |  |  |
| 137 | §31 | Related work | R |  |  |
| 138 | gems G1 | Two-point law: c >= 2, 0 <= j <= 2^a: u(c 2^a + j) = u(c) v(2^a + j) - d(c) v(j), d(c) = 2u(c) - u(c+1) | P (gem) | Gems.two_point, u_block_start, u_pow_one | PySR found it at loss 0; Python checked 1,634,586 cases (c < 400, a < 12); induction on a with j split by parity; the class-by-8 weights are the a = 3 case (Gems.u_8k1'..u_8k7', class_eight_agree) |
| 139 | gems G2 | Block sums: 3 sum_{j<2^a} v(j) = 5^a - 2^a; 3 sum_{j<2^a} v(2^a+j) = 4 5^a - 2^a; c >= 2: 3 sum_{j<2^a} u(c 2^a + j) = u(c)(4 5^a - 2^a) - d(c)(5^a - 2^a) | P (gem) | Gems.v_sum_low, v_sum_high, v_sums_int, block_sum | Python checked 2,980 cases (c < 300, a < 10), v sums a < 14; each halving multiplies a block total by 5 |
| 140 | gems G3 | Record block of the packed places: at each record X the places needed equal places_needed(X, prevprime(isqrt(nextprime(X)))) | C/P | Gems.small_block_le_sqrt (the provable part: a composite y < q has minFac y <= sqrt q) | record equality checked 212/212 to 10^7; the packing function is not formalized, so the equality stays C |
| 141 | gems G5 | Rule-breaker count: every member of 2^a, 2^a+1, 2^a+2, 3 2^a, 3 2^a+1 breaks a rule; off the strands exactly 11, 15, 22, 36, 44, 88, 272, 2112, 4224, 8448 (to 10^6) | C/P | strand membership: RatioTwoLine, TwoMirrors, ManyTurns (rows 55, 60, 105) | "exactly ten off-strand" is a finite list checked to 10^6; no general statement to prove |

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

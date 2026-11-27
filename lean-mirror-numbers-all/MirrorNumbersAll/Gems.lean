import Mathlib
import MirrorNumbersAll.TwoMirrors
import MirrorNumbersAll.UnifiedCode
import MirrorNumbersAll.WallMirror

/-!
# The PySR gems (tUrUq, Turaq Rayn-McLean, 11-27-2026)

From `gems-for-lean_v1.0_11-26-2026.txt`. `u`, `v`, `d` are `TwoMirrors.u` (leaves 1, 2, 3),
`TwoMirrors.v` (pure halving, leaves 1, 2; v 3 = 4) and `TwoMirrors.d c = 2 u c - u (c+1)`.

G1 `two_point`  : c ≥ 2, j ≤ 2^a:  u (c 2^a + j) = u c · v (2^a + j) - d c · v j   (over ℤ).
   Corollaries: `u_block_start`, `u_pow_one` (u (c 2^a + 1) = 2^(a+1) u c - d c), the strands
   `strand_pow`, `strand_three_pow`, the class-by-8 weights `u_8k1'` .. `u_8k7'`; each cross-checked
   against the theorem already in the library (`strands_agree`, `class_eight_agree`).
G2 `v_sum_low`, `v_sum_high`, `block_sum`, and the octave sum recovered as the c = 2 and c = 3
   blocks side by side (`octave_from_blocks`, agreeing with `UnifiedCode.octave_sum`).
G4 `gap_class_balance`: on any walk of seats off 2 and 3, #(gap ≡ 2 mod 6) - #(gap ≡ 4 mod 6)
   equals (seat 0 is 6k+5) - (seat n is 6k+5), so it is -1, 0 or 1; `gap_class_balance_primes`
   for a walk of primes ≥ 5.
G3 `small_block_le_sqrt` is the provable part named in the gem (smallest block of a composite
   below q is at most √q); the record equality stays checked by computer.
G5 stays checked (finite list of 10 off-strand breakers to 10^6).

No sorry, no admit, no native_decide.
-/

namespace Gems

open TwoMirrors Finset

/-! ## v's halving steps hold at every k (v 0 = 0 closes the k = 0 case) -/

theorem v_even' (k : ℕ) : v (2 * k) = 2 * v k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · exact v_even k hk

theorem v_odd' (k : ℕ) : v (2 * k + 1) = 2 * v k + v (k + 1) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · exact v_odd k hk

theorem v_pow_add_one' (a : ℕ) : v (2 ^ a + 1) = 2 ^ (a + 1) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  · exact v_pow_add_one a ha

/-! ## G1: the two-point law -/

/-- **G1.** For `c ≥ 2` and `j ≤ 2^a`: `u (c 2^a + j) = u c · v (2^a + j) - d c · v j`.
Both sides obey the same halving recursion in `j`; they agree at `j = 0, 1` (a = 0). -/
theorem two_point (c a j : ℕ) (hc : 2 ≤ c) (hj : j ≤ 2 ^ a) :
    (u (c * 2 ^ a + j) : ℤ) = u c * v (2 ^ a + j) - d c * v j := by
  induction a generalizing j with
  | zero =>
    simp only [pow_zero, mul_one] at hj ⊢
    interval_cases j
    · simp [d]
    · simp [d]; ring
  | succ a ih =>
    have h1 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
    rcases Nat.even_or_odd' j with ⟨i, rfl | rfl⟩
    · -- j = 2 i, i ≤ 2^a
      have hi : i ≤ 2 ^ a := by rw [pow_succ] at hj; omega
      rw [show c * 2 ^ (a + 1) + 2 * i = 2 * (c * 2 ^ a + i) by ring,
        u_even _ (by nlinarith), show 2 ^ (a + 1) + 2 * i = 2 * (2 ^ a + i) by ring, v_even', v_even']
      push_cast
      rw [ih i hi]; ring
    · -- j = 2 i + 1, i + 1 ≤ 2^a
      have hi : i + 1 ≤ 2 ^ a := by rw [pow_succ] at hj; omega
      rw [show c * 2 ^ (a + 1) + (2 * i + 1) = 2 * (c * 2 ^ a + i) + 1 by ring,
        u_odd _ (by nlinarith), show 2 ^ (a + 1) + (2 * i + 1) = 2 * (2 ^ a + i) + 1 by ring,
        v_odd', v_odd', show c * 2 ^ a + i + 1 = c * 2 ^ a + (i + 1) by ring,
        show 2 ^ a + i + 1 = 2 ^ a + (i + 1) by ring]
      push_cast
      rw [ih i (by omega), ih (i + 1) hi]; ring

/-- j = 0: the block starts at `2^a u c`. -/
theorem u_block_start (c a : ℕ) (hc : 2 ≤ c) : u (c * 2 ^ a) = 2 ^ a * u c := by
  have h := two_point c a 0 hc (Nat.zero_le _)
  rw [add_zero, add_zero, v_pow, v0] at h
  have h' : (u (c * 2 ^ a) : ℤ) = 2 ^ a * u c := by rw [h]; push_cast; ring
  exact_mod_cast h'

/-- j = 1: `u (c 2^a + 1) = 2^(a+1) u c - d c` (every a ≥ 0, c ≥ 2). -/
theorem u_pow_one (c a : ℕ) (hc : 2 ≤ c) :
    (u (c * 2 ^ a + 1) : ℤ) = 2 ^ (a + 1) * u c - d c := by
  have h := two_point c a 1 hc Nat.one_le_two_pow
  rw [v_pow_add_one', v1] at h
  push_cast at h
  linarith

/-! ### The strands from G1 (c = 2 and c = 3), cross-checked with the library -/

theorem strand_pow (a : ℕ) : (u (2 ^ (a + 1) + 1) : ℤ) = 2 ^ (a + 2) - 1 := by
  have h := u_pow_one 2 a le_rfl
  rw [show 2 * 2 ^ a = 2 ^ (a + 1) by ring, u2, d_exceptions.1] at h
  rw [h]; ring

theorem strand_three_pow (a : ℕ) : (u (3 * 2 ^ a + 1) : ℤ) = 2 * (3 * 2 ^ a - 1) := by
  have h := u_pow_one 3 a (by norm_num)
  rw [u3, d_exceptions.2.2.1] at h
  rw [h]; ring

/-- Same values as `TwoMirrors.u_pow_add_one` and `u_three_pow_add_one`. -/
theorem strands_agree (a : ℕ) :
    (u (2 ^ (a + 1) + 1) : ℤ) = ((2 ^ (a + 2) - 1 : ℕ) : ℤ) ∧
    (u (3 * 2 ^ a + 1) : ℤ) = ((2 * (3 * 2 ^ a - 1) : ℕ) : ℤ) := by
  have h1 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
  have h3 : 1 ≤ 3 * 2 ^ a := by omega
  have e1 : 1 ≤ 2 ^ (a + 2) := Nat.one_le_two_pow
  refine ⟨?_, ?_⟩
  · rw [strand_pow, Nat.cast_sub e1]; push_cast; ring
  · rw [strand_three_pow, Nat.cast_mul, Nat.cast_sub h3]; push_cast; ring

/-! ### The class-by-8 weights from G1 (a = 3, j = 1, 3, 5, 7) -/

theorem v5 : v 5 = 8 := by have := v_odd 2 (by norm_num); norm_num at this; exact this
theorem v6 : v 6 = 8 := by have := v_even 3 (by norm_num); norm_num at this; exact this
theorem v8 : v 8 = 8 := by have := v_pow 3; norm_num at this; exact this
theorem v9 : v 9 = 16 := by have := v_pow_add_one 3 (by norm_num); norm_num at this; exact this
theorem v11 : v 11 = 24 := by have := v_odd 5 (by norm_num); norm_num [v5, v6] at this; exact this
theorem v13 : v 13 = 28 := by have := v_odd 6 (by norm_num); norm_num [v6, v7] at this; exact this
theorem v15 : v 15 = 32 := by have := v_odd 7 (by norm_num); norm_num [v7, v8] at this; exact this

theorem u_8k1' (k : ℕ) (hk : 2 ≤ k) : u (8 * k + 1) = 14 * u k + u (k + 1) := by
  have h := two_point k 3 1 hk (by norm_num)
  rw [show k * 2 ^ 3 + 1 = 8 * k + 1 by ring, show 2 ^ 3 + 1 = 9 by norm_num, v9, v1, d] at h
  push_cast at h; omega

theorem u_8k3' (k : ℕ) (hk : 2 ≤ k) : u (8 * k + 3) = 16 * u k + 4 * u (k + 1) := by
  have h := two_point k 3 3 hk (by norm_num)
  rw [show k * 2 ^ 3 + 3 = 8 * k + 3 by ring, show 2 ^ 3 + 3 = 11 by norm_num, v11, v3, d] at h
  push_cast at h; omega

theorem u_8k5' (k : ℕ) (hk : 2 ≤ k) : u (8 * k + 5) = 12 * u k + 8 * u (k + 1) := by
  have h := two_point k 3 5 hk (by norm_num)
  rw [show k * 2 ^ 3 + 5 = 8 * k + 5 by ring, show 2 ^ 3 + 5 = 13 by norm_num, v13, v5, d] at h
  push_cast at h; omega

theorem u_8k7' (k : ℕ) (hk : 2 ≤ k) : u (8 * k + 7) = 8 * u k + 12 * u (k + 1) := by
  have h := two_point k 3 7 hk (by norm_num)
  rw [show k * 2 ^ 3 + 7 = 8 * k + 7 by ring, show 2 ^ 3 + 7 = 15 by norm_num, v15, v7, d] at h
  push_cast at h; omega

/-- Cross-check: the four weights derived from G1 are, statement for statement, the four already
proven by direct halving in `UnifiedCode` (this proof uses the library's route; the primed
theorems above use G1). -/
theorem class_eight_agree (k : ℕ) (hk : 2 ≤ k) :
    u (8 * k + 1) = 14 * u k + u (k + 1) ∧ u (8 * k + 3) = 16 * u k + 4 * u (k + 1) ∧
    u (8 * k + 5) = 12 * u k + 8 * u (k + 1) ∧ u (8 * k + 7) = 8 * u k + 12 * u (k + 1) :=
  ⟨UnifiedCode.u_8k1 k hk, UnifiedCode.u_8k3 k hk, UnifiedCode.u_8k5 k hk, UnifiedCode.u_8k7 k hk⟩

/-! ## G2: the block sums -/

/-- `3 Σ_{j<2^a} v j + 2^a = 5^a`, i.e. `Σ v j = (5^a - 2^a)/3`. -/
theorem v_sum_low (a : ℕ) : 3 * (∑ j ∈ range (2 ^ a), v j) + 2 ^ a = 5 ^ a := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pow_succ 2, mul_comm (2 ^ a) 2, UnifiedCode.sum_range_two_mul]
    have h1 : ∀ i ∈ range (2 ^ a), v (2 * i) + v (2 * i + 1) = 4 * v i + v (i + 1) := by
      intro i _; rw [v_even', v_odd']; ring
    rw [sum_congr rfl h1, sum_add_distrib, ← mul_sum]
    have e1 := sum_range_succ' v (2 ^ a)
    have e2 := sum_range_succ v (2 ^ a)
    rw [v0, add_zero] at e1
    rw [v_pow] at e2
    rw [pow_succ 5]
    omega

/-- `3 Σ_{j<2^a} v (2^a + j) + 2^a = 4 · 5^a`, i.e. `Σ v (2^a + j) = (4 · 5^a - 2^a)/3`. -/
theorem v_sum_high (a : ℕ) : 3 * (∑ j ∈ range (2 ^ a), v (2 ^ a + j)) + 2 ^ a = 4 * 5 ^ a := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pow_succ 2, mul_comm (2 ^ a) 2, UnifiedCode.sum_range_two_mul]
    have h1 : ∀ i ∈ range (2 ^ a),
        v (2 * 2 ^ a + 2 * i) + v (2 * 2 ^ a + (2 * i + 1)) = 4 * v (2 ^ a + i) + v (2 ^ a + (i + 1)) := by
      intro i _
      rw [show 2 * 2 ^ a + 2 * i = 2 * (2 ^ a + i) by ring,
        show 2 * 2 ^ a + (2 * i + 1) = 2 * (2 ^ a + i) + 1 by ring, v_even', v_odd',
        show 2 ^ a + i + 1 = 2 ^ a + (i + 1) by ring]
      ring
    rw [sum_congr rfl h1, sum_add_distrib, ← mul_sum]
    have e1 := sum_range_succ' (fun i => v (2 ^ a + i)) (2 ^ a)
    have e2 := sum_range_succ (fun i => v (2 ^ a + i)) (2 ^ a)
    rw [add_zero, v_pow] at e1
    rw [show 2 ^ a + 2 ^ a = 2 ^ (a + 1) by ring, v_pow, pow_succ] at e2
    rw [pow_succ 5]
    omega

/-- The gem's subtraction forms, over ℤ. -/
theorem v_sums_int (a : ℕ) :
    3 * (∑ j ∈ range (2 ^ a), (v j : ℤ)) = 5 ^ a - 2 ^ a ∧
    3 * (∑ j ∈ range (2 ^ a), (v (2 ^ a + j) : ℤ)) = 4 * 5 ^ a - 2 ^ a := by
  have hl : (3 : ℤ) * (∑ j ∈ range (2 ^ a), (v j : ℤ)) + 2 ^ a = 5 ^ a := by
    exact_mod_cast v_sum_low a
  have hh : (3 : ℤ) * (∑ j ∈ range (2 ^ a), (v (2 ^ a + j) : ℤ)) + 2 ^ a = 4 * 5 ^ a := by
    exact_mod_cast v_sum_high a
  constructor <;> linarith

/-- **G2.** For `c ≥ 2`:
`3 Σ_{j<2^a} u (c 2^a + j) = u c (4 · 5^a - 2^a) - d c (5^a - 2^a)`. -/
theorem block_sum (c a : ℕ) (hc : 2 ≤ c) :
    3 * (∑ j ∈ range (2 ^ a), (u (c * 2 ^ a + j) : ℤ)) =
      u c * (4 * 5 ^ a - 2 ^ a) - d c * (5 ^ a - 2 ^ a) := by
  have h1 : ∀ j ∈ range (2 ^ a),
      (u (c * 2 ^ a + j) : ℤ) = u c * v (2 ^ a + j) - d c * v j :=
    fun j hj => two_point c a j hc (le_of_lt (mem_range.1 hj))
  rw [sum_congr rfl h1, sum_sub_distrib, ← mul_sum, ← mul_sum]
  obtain ⟨hl, hh⟩ := v_sums_int a
  linear_combination (u c : ℤ) * hh - d c * hl

/-- The octave `[2^(a+1), 2^(a+2))` is the c = 2 block beside the c = 3 block; their G2 sums give
`3 S (a+1) + 2^(a+1) = 17 · 5^a`, the library's `UnifiedCode.octave_sum` by a second route. -/
theorem octave_from_blocks (a : ℕ) : 3 * UnifiedCode.S (a + 1) + 2 ^ (a + 1) = 17 * 5 ^ a := by
  have hsplit : UnifiedCode.S (a + 1) =
      (∑ j ∈ range (2 ^ a), u (2 * 2 ^ a + j)) + ∑ j ∈ range (2 ^ a), u (3 * 2 ^ a + j) := by
    unfold UnifiedCode.S
    rw [pow_succ, mul_comm (2 ^ a) 2, show 2 * 2 ^ a = 2 ^ a + 2 ^ a by ring, sum_range_add]
    congr 1
    all_goals (apply sum_congr rfl; intro j _; congr 1; ring)
  have h2 := block_sum 2 a le_rfl
  have h3 := block_sum 3 a (by norm_num)
  rw [u2, d_exceptions.1] at h2
  rw [u3, d_exceptions.2.2.1] at h3
  have h2' : (3 : ℤ) * (∑ j ∈ range (2 ^ a), (u (2 * 2 ^ a + j) : ℤ)) = 7 * 5 ^ a - 2 ^ a := by
    rw [h2]; ring
  have h3' : (3 : ℤ) * (∑ j ∈ range (2 ^ a), (u (3 * 2 ^ a + j) : ℤ)) = 10 * 5 ^ a - 2 ^ a := by
    rw [h3]; ring
  have : ((3 * UnifiedCode.S (a + 1) + 2 ^ (a + 1) : ℕ) : ℤ) = ((17 * 5 ^ a : ℕ) : ℤ) := by
    rw [hsplit]; push_cast
    linear_combination h2' + h3'
  exact_mod_cast this

/-! ## G4: gap classes mod 6 on a walk of seats off 2 and 3 -/

/-- Seats off 2 and 3 are 1 or 5 mod 6. A hop 5 → 1 has gap ≡ 2 (mod 6); a hop 1 → 5 has gap
≡ 4 (mod 6); a hop between like seats has gap ≡ 0. -/
theorem gap_class (x y : ℤ) (hx : x % 6 = 1 ∨ x % 6 = 5) (hy : y % 6 = 1 ∨ y % 6 = 5) :
    ((y - x) % 6 = 2 ↔ x % 6 = 5 ∧ y % 6 = 1) ∧ ((y - x) % 6 = 4 ↔ x % 6 = 1 ∧ y % 6 = 5) := by
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> omega

/-- **G4, exact form.** On a walk `p` of seats off 2 and 3,
`#(gap ≡ 2 mod 6) - #(gap ≡ 4 mod 6) = [p 0 ≡ 5] - [p n ≡ 5]`: the end seats pay the difference. -/
theorem gap_class_balance_exact (p : ℕ → ℤ) (hp : ∀ i, p i % 6 = 1 ∨ p i % 6 = 5) (n : ℕ) :
    (∑ i ∈ range n, (if (p (i + 1) - p i) % 6 = 2 then (1 : ℤ) else 0))
      - (∑ i ∈ range n, (if (p (i + 1) - p i) % 6 = 4 then (1 : ℤ) else 0))
      = (if p 0 % 6 = 5 then 1 else 0) - (if p n % 6 = 5 then 1 else 0) := by
  -- the facing g i = 1 at a 6k+5 seat, 0 at a 6k+1 seat
  set g : ℕ → ℤ := fun i => (p i % 6) / 4 with hg_def
  have hg : ∀ i, g i = 0 ∨ g i = 1 := by intro i; have := hp i; simp only [hg_def]; omega
  have h2 : ∀ i ∈ range n, (if (p (i + 1) - p i) % 6 = 2 then (1 : ℤ) else 0)
      = (if g i = 1 ∧ g (i + 1) = 0 then (1 : ℤ) else 0) := by
    intro i _; have := hp i; have := hp (i + 1); simp only [hg_def]; split_ifs <;> omega
  have h4 : ∀ i ∈ range n, (if (p (i + 1) - p i) % 6 = 4 then (1 : ℤ) else 0)
      = (if g i = 0 ∧ g (i + 1) = 1 then (1 : ℤ) else 0) := by
    intro i _; have := hp i; have := hp (i + 1); simp only [hg_def]; split_ifs <;> omega
  rw [sum_congr rfl h2, sum_congr rfl h4]
  have hb := WallMirror.flips_balance g hg n
  have e0 : (if p 0 % 6 = 5 then (1 : ℤ) else 0) = g 0 := by
    have := hp 0; simp only [hg_def]; split_ifs <;> omega
  have en : (if p n % 6 = 5 then (1 : ℤ) else 0) = g n := by
    have := hp n; simp only [hg_def]; split_ifs <;> omega
  rw [e0, en]; linarith

/-- **G4.** `|#(gap ≡ 2 mod 6) - #(gap ≡ 4 mod 6)| ≤ 1` on any finite walk of seats off 2 and 3. -/
theorem gap_class_balance (p : ℕ → ℤ) (hp : ∀ i, p i % 6 = 1 ∨ p i % 6 = 5) (n : ℕ) :
    |(∑ i ∈ range n, (if (p (i + 1) - p i) % 6 = 2 then (1 : ℤ) else 0))
      - (∑ i ∈ range n, (if (p (i + 1) - p i) % 6 = 4 then (1 : ℤ) else 0))| ≤ 1 := by
  rw [gap_class_balance_exact p hp n]
  have := hp 0; have := hp n
  split_ifs <;> simp

/-- A prime at or above 5 is a seat off 2 and 3. -/
theorem prime_seat (q : ℕ) (hq : q.Prime) (h5 : 5 ≤ q) : q % 6 = 1 ∨ q % 6 = 5 := by
  by_contra h
  have h23 : 2 ∣ q ∨ 3 ∣ q := by omega
  rcases h23 with h2 | h3
  · have := (Nat.Prime.eq_one_or_self_of_dvd hq 2 h2); omega
  · have := (Nat.Prime.eq_one_or_self_of_dvd hq 3 h3); omega

/-- **G4 on primes.** Any walk of primes ≥ 5 (consecutive primes from 5 up are one instance). -/
theorem gap_class_balance_primes (p : ℕ → ℕ) (hp : ∀ i, (p i).Prime) (h5 : ∀ i, 5 ≤ p i)
    (n : ℕ) :
    |(∑ i ∈ range n, (if ((p (i + 1) : ℤ) - p i) % 6 = 2 then (1 : ℤ) else 0))
      - (∑ i ∈ range n, (if ((p (i + 1) : ℤ) - p i) % 6 = 4 then (1 : ℤ) else 0))| ≤ 1 :=
  gap_class_balance (fun i => (p i : ℤ))
    (fun i => by have := prime_seat (p i) (hp i) (h5 i); omega) n

/-! ## G3, the provable part: a composite below q has its smallest block at most √q -/

theorem small_block_le_sqrt (y q : ℕ) (hy : 0 < y) (hc : ¬ y.Prime) (hq : y < q) :
    Nat.minFac y ≤ Nat.sqrt q := by
  rw [Nat.le_sqrt]
  have := Nat.minFac_sq_le_self hy hc
  nlinarith

end Gems

import Mathlib
import MirrorNumbersAll.Upgrades
import MirrorNumbersAll.PrimeHandOff
import MirrorNumbersAll.PySRFinds
import MirrorNumbersAll.UnitCountingLaws

/-!
# Claims A: rows 1 to 75 of the claim audit (tUrUq, 11-27-2026)

Upgrades the rows of the audit of `unit-counting-paper_v5.8_11-27-2026.tex` that were
definitions (D), range checks (C), measures (M) or readings (R), wherever the row holds an exact
mathematical statement. Each block names its audit row. The counting rule is `UnifiedCode.unitProd`
(bare units are counted, a factor holding the unit multiplies). No sorry, no admit, no native_decide.
-/

namespace ClaimsA

open UnifiedCode

/-! ## Rows 3 to 8: the counting rule `unitProd` -/

theorem unitProd_of_ne (l : List ℕ) (h : ∃ x ∈ l, x ≠ 1) : unitProd l = l.prod := by
  unfold unitProd
  rw [if_neg]
  obtain ⟨x, hx, hx1⟩ := h
  simp only [List.all_eq_true, decide_eq_true_eq, not_forall]
  exact ⟨x, hx, hx1⟩

theorem unitProd_of_all (l : List ℕ) (h : ∀ x ∈ l, x = 1) : unitProd l = l.length := by
  unfold unitProd
  rw [if_pos]
  simpa using h

/-- Row 3, containment: 1 x n = n and n x 1 = n for every n other than the bare unit. -/
theorem containment (n : ℕ) (hn : n ≠ 1) : unitProd [1, n] = n ∧ unitProd [n, 1] = n := by
  constructor
  · rw [unitProd_of_ne _ ⟨n, by simp, hn⟩]; simp
  · rw [unitProd_of_ne _ ⟨n, by simp, hn⟩]; simp

/-- Row 4, bare units: 1 x ... x 1 (n factors) = n; in particular 1 x 1 = 2 and 1 x 1 x 1 = 3. -/
theorem bare_units (n : ℕ) : unitProd (List.replicate n 1) = n := by
  rw [unitProd_of_all _ (fun x hx => (List.mem_replicate.mp hx).2)]; simp

theorem bare_units_small : unitProd [1, 1] = 2 ∧ unitProd [1, 1, 1] = 3 := by decide

/-- Row 5, the whole-expression examples: 1 x 1 x 3 = 3, 1 x 2 = 2, 2 x 3 = 6. -/
theorem whole_expression_examples :
    unitProd [1, 1, 3] = 3 ∧ unitProd [1, 2] = 2 ∧ unitProd [2, 3] = 6 := by decide

/-- Row 5: the rule reads the whole expression, so the order of the factors never matters. -/
theorem unitProd_perm {l₁ l₂ : List ℕ} (h : l₁.Perm l₂) : unitProd l₁ = unitProd l₂ := by
  by_cases ha : ∀ x ∈ l₁, x = 1
  · rw [unitProd_of_all _ ha, unitProd_of_all _ (fun x hx => ha x (h.symm.subset hx)), h.length_eq]
  · push_neg at ha
    obtain ⟨x, hx, hx1⟩ := ha
    rw [unitProd_of_ne _ ⟨x, hx, hx1⟩, unitProd_of_ne _ ⟨x, h.subset hx, hx1⟩, h.prod_eq]

/-- A product expression with brackets. The whole-expression rule reads its factors at once. -/
inductive PExpr
  | leaf : ℕ → PExpr
  | mul : PExpr → PExpr → PExpr

/-- The factors of an expression, brackets dropped. -/
def PExpr.factors : PExpr → List ℕ
  | .leaf n => [n]
  | .mul a b => a.factors ++ b.factors

/-- Its value under the counting rule. -/
def PExpr.val (e : PExpr) : ℕ := unitProd e.factors

/-- Row 5: grouping does not change a result. -/
theorem grouping (a b c : PExpr) : (PExpr.mul (.mul a b) c).val = (PExpr.mul a (.mul b c)).val := by
  simp [PExpr.val, PExpr.factors, List.append_assoc]

theorem grouping_swap (a b : PExpr) : (PExpr.mul a b).val = (PExpr.mul b a).val :=
  unitProd_perm (List.perm_append_comm)

/-- Row 5: 1 x (1 x 1) = (1 x 1) x 1 = 3. -/
theorem one_one_one_grouped :
    (PExpr.mul (.leaf 1) (.mul (.leaf 1) (.leaf 1))).val = 3 ∧
    (PExpr.mul (.mul (.leaf 1) (.leaf 1)) (.leaf 1)).val = 3 := by decide

/-- Row 6, agreement: wherever a factor holds the unit (is not 1), the rule is the ordinary product. -/
theorem agreement (l : List ℕ) (h : ∃ x ∈ l, x ≠ 1) : unitProd l = l.prod := unitProd_of_ne l h

/-- Row 6, no distributive law: 1 x (1 + 1) is 2, while 1 x 1 + 1 x 1 is 4. -/
theorem no_distributive : unitProd [1, 1 + 1] ≠ unitProd [1, 1] + unitProd [1, 1] := by decide

/-- Row 7, the two-valued 2/1: x x 1 = 2 has the two answers 1 and 2. -/
theorem two_over_one (x : ℕ) : unitProd [x, 1] = 2 ↔ x = 1 ∨ x = 2 := by
  by_cases hx : x = 1
  · subst hx; decide
  · rw [unitProd_of_ne _ ⟨x, by simp, hx⟩]; simp; omega

/-- Row 7: 2 is the only n for which n/1 has two values; for n other than 2, x x 1 = n has the one
answer x = n (and none for n = 1). -/
theorem over_one (n x : ℕ) : unitProd [x, 1] = n ↔ (x = 1 ∧ n = 2) ∨ (x ≠ 1 ∧ x = n) := by
  by_cases hx : x = 1
  · subst hx; simp [unitProd]; omega
  · rw [unitProd_of_ne _ ⟨x, by simp, hx⟩]; simp; omega

/-- Row 7, powers: 1^n = n (n bare units), so 1^0 is zero bare units (the empty count). -/
theorem one_pow_count (n : ℕ) : unitProd (List.replicate n 1) = n := bare_units n
theorem one_pow_zero : unitProd (List.replicate 0 1) = 0 := rfl

/-- For a factor holding the unit, the counting power is the ordinary power. -/
theorem pow_count (a n : ℕ) (ha : a ≠ 1) (hn : 1 ≤ n) : unitProd (List.replicate n a) = a ^ n := by
  rw [unitProd_of_ne _ ⟨a, List.mem_replicate.mpr ⟨by omega, rfl⟩, ha⟩, List.prod_replicate]

/-- Row 8, the count root: for n >= 1 the only x with x^n = n under the counting rule is x = 1. -/
theorem count_root (n x : ℕ) (hn : 1 ≤ n) : unitProd (List.replicate n x) = n ↔ x = 1 := by
  constructor
  · intro h
    by_contra hx
    rw [pow_count x n hx hn] at h
    rcases Nat.lt_or_ge x 2 with h2 | h2
    · interval_cases x
      · rw [zero_pow (by omega)] at h; omega
      · exact hx rfl
    · have : n < x ^ n := Nat.lt_pow_self h2
      omega
  · rintro rfl; exact bare_units n

/-- Row 47, cube form: a,|a|,a = a^3 when a holds the unit; 1,|1|,1 = 3. -/
theorem cube_form (a : ℕ) (ha : a ≠ 1) : unitProd [a, a, a] = a ^ 3 := by
  have := pow_count a 3 ha (by norm_num); simpa using this

theorem cube_examples : unitProd [2, 2, 2] = 8 ∧ unitProd [3, 3, 3] = 27 ∧ unitProd [4, 4, 4] = 64 ∧
    unitProd [1, 1, 1] = 3 := by decide

/-! ## Row 1: the four words are exactly the three-digit mirror words, and the word of n holds n units -/

def words : List (List ℕ) := [[0, 0, 0], [0, 1, 0], [1, 0, 1], [1, 1, 1]]

theorem words_mirror_units : ∀ i < 4, (words.getD i []).reverse = words.getD i [] ∧
    (words.getD i []).sum = i := by decide

/-- All eight three-digit 0/1 words. -/
def triples : List (List ℕ) :=
  [[0, 0, 0], [0, 0, 1], [0, 1, 0], [0, 1, 1], [1, 0, 0], [1, 0, 1], [1, 1, 0], [1, 1, 1]]

theorem mirror_words_are_words : triples.filter (fun l => l.reverse == l) = words := by decide

/-! ## Row 14: the rewrite 0 -> 000, 1 -> 010 on the four words gives the order-1 words -/

theorem rewrite_words :
    step [0, 0, 0] = [0, 0, 0, 0, 0, 0, 0, 0, 0] ∧ step [0, 1, 0] = [0, 0, 0, 0, 1, 0, 0, 0, 0] ∧
    step [1, 0, 1] = [0, 1, 0, 0, 0, 0, 0, 1, 0] ∧ step [1, 1, 1] = [0, 1, 0, 0, 1, 0, 0, 1, 0] := by
  decide

/-! ## Rows 9, 10: count root against measure root; the two yardsticks -/

theorem cube_lt_three_pow (n : ℕ) (hn : n ≠ 3) : n ^ 3 < 3 ^ n := by
  rcases Nat.lt_or_ge n 4 with h | h
  · interval_cases n <;> simp_all
  · induction n, h using Nat.le_induction with
    | base => norm_num
    | succ m hm ih =>
      have := ih (by omega)
      have h3 : (m + 1) ^ 3 ≤ 3 * m ^ 3 := by nlinarith [sq_nonneg (m : ℕ)]
      calc (m + 1) ^ 3 ≤ 3 * m ^ 3 := h3
        _ < 3 * 3 ^ m := by omega
        _ = 3 ^ (m + 1) := by ring

/-- Row 9: among whole numbers the measure root n^(1/n) peaks at 3 (strictly). -/
theorem measure_root_peak (n : ℕ) (hn1 : 1 ≤ n) (hn : n ≠ 3) :
    (n : ℝ) ^ ((n : ℝ)⁻¹) < (3 : ℝ) ^ ((3 : ℝ)⁻¹) := by
  have hx : 0 ≤ (n : ℝ) ^ ((n : ℝ)⁻¹) := Real.rpow_nonneg (by positivity) _
  have hy : 0 ≤ (3 : ℝ) ^ ((3 : ℝ)⁻¹) := Real.rpow_nonneg (by positivity) _
  rw [← pow_lt_pow_iff_left₀ hx hy (show 3 * n ≠ 0 by omega)]
  have e1 : ((n : ℝ) ^ ((n : ℝ)⁻¹)) ^ (3 * n) = (n : ℝ) ^ 3 := by
    rw [mul_comm, pow_mul, Real.rpow_inv_natCast_pow (by positivity) (by omega)]
  have e2 : ((3 : ℝ) ^ ((3 : ℝ)⁻¹)) ^ (3 * n) = (3 : ℝ) ^ n := by
    rw [pow_mul]
    have := Real.rpow_inv_natCast_pow (x := (3 : ℝ)) (n := 3) (by norm_num) (by norm_num)
    push_cast at this
    rw [this]
  rw [e1, e2]
  exact_mod_cast cube_lt_three_pow n hn

/-- Row 9: 2 and 4 have the same measure root (the table's equal entries). -/
theorem two_four_tie : (2 : ℝ) ^ ((2 : ℝ)⁻¹) = (4 : ℝ) ^ ((4 : ℝ)⁻¹) := by
  have hx : 0 ≤ (2 : ℝ) ^ ((2 : ℝ)⁻¹) := Real.rpow_nonneg (by positivity) _
  have hy : 0 ≤ (4 : ℝ) ^ ((4 : ℝ)⁻¹) := Real.rpow_nonneg (by positivity) _
  rw [← pow_left_inj₀ hx hy (show (4 : ℕ) ≠ 0 by norm_num)]
  have e1 : ((2 : ℝ) ^ ((2 : ℝ)⁻¹)) ^ 4 = 4 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]
    have := Real.rpow_inv_natCast_pow (x := (2 : ℝ)) (n := 2) (by norm_num) (by norm_num)
    push_cast at this; rw [this]; norm_num
  have e2 : ((4 : ℝ) ^ ((4 : ℝ)⁻¹)) ^ 4 = 4 := by
    have := Real.rpow_inv_natCast_pow (x := (4 : ℝ)) (n := 4) (by norm_num) (by norm_num)
    push_cast at this; exact this
  rw [e1, e2]

/-- Row 9: the count root and the measure root disagree at every finite n >= 2 (1^n = 1 is not n). -/
theorem measure_root_ne_one (n : ℕ) (hn : 2 ≤ n) : (n : ℝ) ^ ((n : ℝ)⁻¹) ≠ 1 := by
  intro h
  have := Real.rpow_inv_natCast_pow (x := (n : ℝ)) (n := n) (by positivity) (by omega)
  rw [h, one_pow] at this
  have : (2 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

/-- Row 10, the two yardsticks: a square of side s holds 2 s^2, so the side holding n is sqrt(n/2);
sqrt3/sqrt2 squared is 3/2, its reciprocal is sqrt(2/3), and the square-yardstick root of 1 is 1/sqrt2. -/
theorem yardsticks (n : ℝ) (hn : 0 ≤ n) :
    2 * (Real.sqrt (n / 2)) ^ 2 = n ∧
    (Real.sqrt 3 / Real.sqrt 2) ^ 2 = 3 / 2 ∧
    Real.sqrt (2 / 3) * (Real.sqrt 3 / Real.sqrt 2) = 1 ∧
    (1 / Real.sqrt 2) ^ 2 = 1 / 2 ∧
    Real.sqrt (1 / 2) = 1 / Real.sqrt 2 := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Real.sq_sqrt (by linarith)]; ring
  · rw [div_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt (by norm_num)]
  · rw [Real.sqrt_div' 2 (by norm_num : (0:ℝ) ≤ 3)]
    field_simp
  · rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_div' 1 (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_one]

/-- Row 10: on the unit cube the body diagonal is sqrt3 edges and the face diagonal sqrt2 edges. -/
theorem cube_diagonals : Real.sqrt (1 ^ 2 + 1 ^ 2 + 1 ^ 2) = Real.sqrt 3 ∧
    Real.sqrt (1 ^ 2 + 1 ^ 2) = Real.sqrt 2 := by norm_num

/-! ## Row 11: the halving build B, the paper's examples -/

open Upgrades in
theorem B_examples :
    B 4 = [1, 0, 1, 0, 0, 0, 1, 0, 1] ∧
    B 5 = [1, 0, 1, 1, 1, 1, 1, 0, 1] ∧
    B 6 = [1, 1, 1, 0, 0, 0, 1, 1, 1] ∧
    B 17 = [1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1,
            1, 0, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 1,
            1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [B]

/-- Row 11: the leaves of B are the words of 1, 2, 3 (and the zero word): every digit is 0 or 1. -/
theorem B_digits (n : ℕ) : ∀ x ∈ Upgrades.B n, x ≤ 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 4 with h | h
    · interval_cases n <;> simp [Upgrades.B]
    · rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
      · rw [Upgrades.B_even k (by omega)]
        intro x hx
        simp only [List.mem_append] at hx
        rcases hx with (hx | hx) | hx
        · exact ih k (by omega) x hx
        · simp at hx; omega
        · exact ih k (by omega) x hx
      · rw [Upgrades.B_odd k (by omega)]
        intro x hx
        simp only [List.mem_append] at hx
        rcases hx with (hx | hx) | hx
        · exact ih k (by omega) x hx
        · exact ih (k + 1) (by omega) x hx
        · exact ih k (by omega) x hx

/-! ## Row 13: the triple count T -/

/-- The number of triples of the build. -/
def T (n : ℕ) : ℕ := (Upgrades.B n).length / 3

theorem T_base : T 1 = 1 ∧ T 2 = 1 ∧ T 3 = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [T, Upgrades.B]

theorem T_even (k : ℕ) (hk : 2 ≤ k) : T (2 * k) = 2 * T k + 1 := by
  have h := Upgrades.B_length k
  unfold T; rw [Upgrades.B_even k hk]; simp only [List.length_append, List.length_cons,
    List.length_nil]; omega

theorem T_odd (k : ℕ) (hk : 2 ≤ k) : T (2 * k + 1) = 2 * T k + T (k + 1) := by
  have h := Upgrades.B_length k
  have h' := Upgrades.B_length (k + 1)
  unfold T; rw [Upgrades.B_odd k hk]; simp only [List.length_append]; omega

/-! ## Row 21: mirror-word counts for L = 2, 3, 4, 5 -/

open UnitCountingLaws in
theorem palCount_table :
    (palCount 2 0, palCount 2 1, palCount 2 2) = (1, 0, 1) ∧
    (palCount 3 0, palCount 3 1, palCount 3 2, palCount 3 3) = (1, 1, 1, 1) ∧
    (palCount 4 0, palCount 4 1, palCount 4 2, palCount 4 3, palCount 4 4) = (1, 0, 2, 0, 1) ∧
    (palCount 5 0, palCount 5 1, palCount 5 2, palCount 5 3, palCount 5 4, palCount 5 5) =
      (1, 1, 2, 2, 1, 1) := by decide

/-! ## Row 34: a prime of three or more digits; its mirror is never divisible by 3 or 11 -/

theorem prime_mirror_not_three_eleven (p : ℕ) (hp : p.Prime) (h100 : 100 ≤ p) :
    ¬ 3 ∣ Nat.ofDigits 10 (Nat.digits 10 p).reverse ∧
    ¬ 11 ∣ Nat.ofDigits 10 (Nat.digits 10 p).reverse := by
  set ds := Nat.digits 10 p
  set m := Nat.ofDigits 10 ds.reverse
  have hp' : Nat.ofDigits 10 ds = p := Nat.ofDigits_digits 10 p
  have h9 := UnitCountingLaws.mirror_mod_nine ds
  rw [hp'] at h9
  have hp3 : ¬ 3 ∣ p := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h; omega
  have hp11 : ¬ 11 ∣ p := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp h; omega
  constructor
  · intro h3; apply hp3; omega
  · intro h11
    apply hp11
    have hm : (11 : ℤ) ∣ (m : ℤ) := by exact_mod_cast h11
    have key : (11 : ℤ) ∣ (p : ℤ) := by
      rcases Nat.even_or_odd ds.length with he | ho
      · have := (UnitCountingLaws.mirror_mod_eleven_even ds he).dvd
        rw [hp'] at this
        omega
      · have := (UnitCountingLaws.mirror_mod_eleven_odd ds ho).dvd
        rw [hp'] at this
        omega
    exact_mod_cast key

/-! ## Row 36: the seven-segment mirrors swap 2 and 5 -/

/-- Segments a, b, c, d, e, f, g as 0..6 (a top, b top right, c bottom right, d bottom,
e bottom left, f top left, g middle). -/
def segTwo : Finset (Fin 7) := {0, 1, 6, 4, 3}
def segFive : Finset (Fin 7) := {0, 5, 6, 2, 3}
/-- Top-bottom mirror: a <-> d, b <-> c, f <-> e, g fixed. -/
def topBottom : Fin 7 → Fin 7 := ![3, 2, 1, 0, 5, 4, 6]
/-- Left-right mirror: b <-> f, c <-> e, a, d, g fixed. -/
def leftRight : Fin 7 → Fin 7 := ![0, 5, 4, 3, 2, 1, 6]

theorem seven_segment_swap :
    segTwo.image topBottom = segFive ∧ segFive.image topBottom = segTwo ∧
    segTwo.image leftRight = segFive ∧ segFive.image leftRight = segTwo := by decide

/-! ## Row 19: the left wing of 11 holds 10 ones at every order; its zeros grow 3, 30, 111, ... -/

/-- The left wing of a string: the digits before its centre digit. -/
def leftWing (l : List ℕ) : List ℕ := l.take (l.length / 2)

theorem step_digits (l : List ℕ) : ∀ x ∈ step l, x ≤ 1 := by
  intro x hx
  simp only [step, List.mem_flatMap] at hx
  obtain ⟨d, _, hd⟩ := hx
  split_ifs at hd <;> simp at hd <;> omega

theorem leftWing_step (l : List ℕ) (ho : l.length % 2 = 1) :
    leftWing (step l) = step (leftWing l) ++ [0] := by
  unfold leftWing
  obtain ⟨c, C, hc⟩ : ∃ c C, l.drop (l.length / 2) = c :: C := by
    cases h : l.drop (l.length / 2) with
    | nil => rw [List.drop_eq_nil_iff] at h; omega
    | cons c C => exact ⟨c, C, rfl⟩
  have hl : l = l.take (l.length / 2) ++ c :: C := by rw [← hc, List.take_append_drop]
  have hA : (l.take (l.length / 2)).length = l.length / 2 := by simp; omega
  have hs : step l = step (l.take (l.length / 2)) ++
      ([0, (if c = 0 then 0 else 1), 0] ++ step C) := by
    conv_lhs => rw [hl]
    rw [step_append, show c :: C = [c] ++ C from rfl, step_append]
    simp only [step, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    split_ifs <;> simp
  have e : (step l).length / 2 = (step (l.take (l.length / 2))).length + 1 := by
    rw [step_length, step_length, hA]; omega
  rw [e, hs, List.take_append]
  simp

theorem count_zero_add_sum (l : List ℕ) (h : ∀ x ∈ l, x ≤ 1) : l.count 0 + l.sum = l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := h a (by simp)
    have := ih (fun x hx => h x (by simp [hx]))
    rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl <;> simp <;> omega

/-- Every order of a 0/1 string of odd width keeps the units of its left wing. -/
theorem leftWing_order (l : List ℕ) (hd : ∀ x ∈ l, x ≤ 1) (ho : l.length % 2 = 1) (d : ℕ) :
    (leftWing (step^[d] l)).sum = (leftWing l).sum ∧ (step^[d] l).length = 3 ^ d * l.length ∧
    ∀ x ∈ step^[d] l, x ≤ 1 := by
  induction d with
  | zero => simpa using hd
  | succ d ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [Function.iterate_succ_apply']
    refine ⟨?_, ?_, step_digits _⟩
    · have hodd : (step^[d] l).length % 2 = 1 := by
        rw [h2, Nat.mul_mod, Nat.pow_mod]; norm_num [ho]
      rw [leftWing_step _ hodd, List.sum_append, step_sum]
      · simpa using h1
      · intro x hx; exact h3 x (List.mem_of_mem_take hx)
    · rw [step_length, h2]; ring

open Upgrades in
theorem B_eleven : B 11 = [1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1,
    1, 0, 1, 1, 1, 1, 1, 0, 1] := by simp [B]

/-- Row 19, every order d: the left wing of 11 holds 10 ones and (27 3^d - 1)/2 - 10 zeros. -/
theorem eleven_wing (d : ℕ) :
    (leftWing (step^[d] (Upgrades.B 11))).sum = 10 ∧
    (leftWing (step^[d] (Upgrades.B 11))).count 0 = (27 * 3 ^ d - 1) / 2 - 10 := by
  obtain ⟨h1, h2, h3⟩ := leftWing_order (Upgrades.B 11) (B_digits 11)
    (by rw [B_eleven]; rfl) d
  have hs : (leftWing (step^[d] (Upgrades.B 11))).sum = 10 := by
    rw [h1, B_eleven]; decide
  refine ⟨hs, ?_⟩
  have hc := count_zero_add_sum (leftWing (step^[d] (Upgrades.B 11)))
    (fun x hx => h3 x (List.mem_of_mem_take hx))
  have hlen : (leftWing (step^[d] (Upgrades.B 11))).length = (27 * 3 ^ d) / 2 := by
    unfold leftWing; rw [List.length_take, h2, B_eleven]
    simp only [List.length_cons, List.length_nil]
    rw [Nat.min_eq_left (Nat.div_le_self _ _), mul_comm]
  have hpos : 1 ≤ 3 ^ d := Nat.one_le_pow _ _ (by norm_num)
  have hodd : 3 ^ d % 2 = 1 := by rw [Nat.pow_mod]; norm_num
  omega

/-- Row 19: orders 0, 1, 2 give 3, 30, 111 zeros. -/
theorem eleven_wing_zeros :
    (leftWing (step^[0] (Upgrades.B 11))).count 0 = 3 ∧
    (leftWing (step^[1] (Upgrades.B 11))).count 0 = 30 ∧
    (leftWing (step^[2] (Upgrades.B 11))).count 0 = 111 := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [(eleven_wing _).2] <;> norm_num

/-! ## Rows 39 to 41: the divisor build -/

/-- `rep sep x d` is d copies of x with sep between neighbours (sep.join([x] * d)). -/
def rep (sep x : List ℕ) : ℕ → List ℕ
  | 0 => []
  | 1 => x
  | d + 2 => x ++ sep ++ rep sep x (d + 1)

/-- The words of 0, 1, 2, 3. -/
def wordOf (n : ℕ) : List ℕ := words.getD n []

/-- A leaf: 1, 2, 3 by their words; any larger p as p units 010 joined by 000. -/
def leaf (p : ℕ) : List ℕ := if p ≤ 3 then wordOf p else rep [0, 0, 0] [0, 1, 0] p

/-- One face of the divisor build, outermost factor first; the zero between copies at the level
with k factors below it is 3^(k+1) zeros (9, 27, 81, ...: one order per level). -/
def face : List ℕ → List ℕ
  | [] => []
  | [p] => leaf p
  | d :: r => rep (List.replicate (3 ^ (r.length + 1)) 0) (face r) d

theorem rep_sum (sep x : List ℕ) (hs : sep.sum = 0) (d : ℕ) : (rep sep x d).sum = d * x.sum := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    match d with
    | 0 => simp [rep]
    | 1 => simp [rep]
    | d + 2 => simp only [rep, List.sum_append, hs, ih (d + 1) (by omega)]; ring

theorem rep_succ' (sep x : List ℕ) (d : ℕ) : rep sep x (d + 2) = rep sep x (d + 1) ++ sep ++ x := by
  induction d with
  | zero => simp [rep]
  | succ d ih =>
    show x ++ sep ++ rep sep x (d + 2) = _
    conv_lhs => rw [ih]
    show _ = (x ++ sep ++ rep sep x (d + 1)) ++ sep ++ x
    simp

theorem rep_reverse (sep x : List ℕ) (hs : sep.reverse = sep) (hx : x.reverse = x) (d : ℕ) :
    (rep sep x d).reverse = rep sep x d := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    match d with
    | 0 => simp [rep]
    | 1 => simpa [rep] using hx
    | d + 2 =>
      conv_lhs => rw [rep]
      rw [List.reverse_append, List.reverse_append, ih (d + 1) (by omega), hs, hx, rep_succ']
      simp

theorem leaf_sum (p : ℕ) : (leaf p).sum = p := by
  unfold leaf
  split_ifs with h
  · interval_cases p <;> decide
  · rw [rep_sum _ _ (by decide)]; simp

theorem leaf_reverse (p : ℕ) : (leaf p).reverse = leaf p := by
  unfold leaf
  split_ifs with h
  · interval_cases p <;> decide
  · exact rep_reverse _ _ (by decide) (by decide) p

/-- Rows 40: every face holds exactly n units (n the product of its factors), every arrangement. -/
theorem face_sum : ∀ fs : List ℕ, fs ≠ [] → (face fs).sum = fs.prod
  | [], h => absurd rfl h
  | [p], _ => by simp [face, leaf_sum]
  | d :: e :: r, _ => by
    show (rep _ (face (e :: r)) d).sum = _
    rw [rep_sum _ _ (by simp), face_sum (e :: r) (by simp)]
    simp [List.prod_cons]

/-- Row 40: every face reads the same from either end. -/
theorem face_reverse : ∀ fs : List ℕ, (face fs).reverse = face fs
  | [] => rfl
  | [p] => by simp [face, leaf_reverse]
  | d :: e :: r => by
    show (rep _ (face (e :: r)) d).reverse = rep _ (face (e :: r)) d
    exact rep_reverse _ _ (by simp) (face_reverse (e :: r)) d

/-- Row 40: the paper's example 12 = 2 x 2 x 3 = 111, 9 zeros, 111, 27 zeros, 111, 9 zeros, 111. -/
theorem face_twelve : face [2, 2, 3] =
    [1, 1, 1] ++ List.replicate 9 0 ++ [1, 1, 1] ++ List.replicate 27 0 ++
    [1, 1, 1] ++ List.replicate 9 0 ++ [1, 1, 1] := by decide

theorem leaf_get (n : ℕ) (hn : 1 ≤ n) (i : ℕ) (hi : i < (rep [0, 0, 0] [0, 1, 0] n).length) :
    (rep [0, 0, 0] [0, 1, 0] n)[i]? = some (if i % 6 = 1 then 1 else 0) := by
  induction n using Nat.strong_induction_on generalizing i with
  | _ n ih =>
    match n, hn with
    | 1, _ => simp [rep] at hi ⊢; interval_cases i <;> simp_all
    | d + 2, _ =>
      have hr : rep [0, 0, 0] [0, 1, 0] (d + 2) = [0, 1, 0, 0, 0, 0] ++ rep [0, 0, 0] [0, 1, 0] (d + 1) := rfl
      rw [hr] at hi ⊢
      by_cases h1 : i < 6
      · rw [List.getElem?_append_left (by simpa using h1)]
        interval_cases i <;> simp
      · rw [List.getElem?_append_right (by simp; omega)]
        simp only [List.length_append, List.length_cons, List.length_nil] at hi
        rw [ih (d + 1) (by omega) (by omega) _ (by simp; omega)]
        have : (i - 6) % 6 = i % 6 := by omega
        simp [this]

theorem rep_length (sep x : List ℕ) (d : ℕ) (hd : 1 ≤ d) :
    (rep sep x d).length = d * x.length + (d - 1) * sep.length := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    match d, hd with
    | 1, _ => simp [rep]
    | d + 2, _ =>
      simp only [rep, List.length_append, ih (d + 1) (by omega) (by omega),
        show d + 2 - 1 = d + 1 from by omega, show d + 1 - 1 = d from by omega]
      ring

/-- A prime leaf never holds nine zeros in a row (its zero runs are 1, 5, 5, ..., 5, 1). -/
theorem leaf_no_nine (n : ℕ) : ¬ List.replicate 9 0 <:+: leaf n := by
  rintro ⟨s, t, hst⟩
  unfold leaf at hst
  split_ifs at hst with h
  · have := congrArg List.length hst
    interval_cases n <;> simp [wordOf, words] at this <;> omega
  · have hlen := congrArg List.length hst
    simp only [List.length_append, List.length_replicate] at hlen
    set j := (7 - s.length % 6) % 6 with hj
    have hj9 : j < 9 := by omega
    have hidx : s.length + j < (rep [0, 0, 0] [0, 1, 0] n).length := by omega
    have e1 := leaf_get n (by omega) (s.length + j) hidx
    have e2 : (rep [0, 0, 0] [0, 1, 0] n)[s.length + j]? = some 0 := by
      rw [← hst, List.append_assoc, List.getElem?_append_right (by omega),
        List.getElem?_append_left (by simp; omega), List.getElem?_replicate, if_pos (by omega)]
    rw [e1, if_pos (by omega)] at e2
    exact absurd e2 (by simp)

theorem nine_in_face (d e : ℕ) (r : List ℕ) (hd : 2 ≤ d) :
    List.replicate 9 0 <:+: face (d :: e :: r) := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 2 := ⟨d - 2, by omega⟩
  show List.replicate 9 0 <:+: rep _ (face (e :: r)) (d' + 2)
  rw [rep]
  have h9 : 9 ≤ 3 ^ ((e :: r).length + 1) := by
    simp only [List.length_cons]
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ (r.length + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsep : List.replicate 9 0 <:+: List.replicate (3 ^ ((e :: r).length + 1)) 0 := by
    refine ⟨[], List.replicate (3 ^ ((e :: r).length + 1) - 9) 0, ?_⟩
    rw [List.nil_append, List.replicate_append_replicate]; congr 1; omega
  exact hsep.trans ⟨face (e :: r),
    rep (List.replicate (3 ^ ((e :: r).length + 1)) 0) (face (e :: r)) (d' + 1), rfl⟩

/-- Row 40: no composite face reads like a prime: a face with two or more factors (the outer
one at least 2) is never the leaf string of any number. -/
theorem composite_face_not_leaf (d e : ℕ) (r : List ℕ) (hd : 2 ≤ d) (n : ℕ) :
    face (d :: e :: r) ≠ leaf n := fun h =>
  leaf_no_nine n (h ▸ nine_in_face d e r hd)

/-- Row 41, the error of v2.0: with the first gap at the zero of a prime (000), 35 = 5 x 7 reads
exactly as 35 written as a prime. -/
theorem v20_error : rep [0, 0, 0] (leaf 7) 5 = leaf 35 := by decide

theorem rep_succ_of_pos (g x : List ℕ) (m : ℕ) (hm : 1 ≤ m) : rep g x (m + 1) = x ++ g ++ rep g x m := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rfl

theorem rep_add (g x : List ℕ) (n : ℕ) (hn : 1 ≤ n) :
    ∀ m, 1 ≤ m → rep g x (m + n) = rep g x m ++ g ++ rep g x n := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => rw [add_comm, rep_succ_of_pos g x n hn]; rfl
  | succ m hm ih =>
    rw [show m + 1 + n = (m + n) + 1 by ring, rep_succ_of_pos g x _ (by omega), ih,
      rep_succ_of_pos g x m hm]
    simp

/-- Row 41: with one fixed zero between copies at every level, the levels flatten:
copies of copies are just copies (a x b copies of the inner string). -/
theorem rep_rep (g x : List ℕ) (a : ℕ) (ha : 1 ≤ a) :
    ∀ b, 1 ≤ b → rep g (rep g x a) b = rep g x (a * b) := by
  intro b hb
  induction b, hb using Nat.le_induction with
  | base => simp [rep]
  | succ b hb ih =>
    rw [rep_succ_of_pos g _ b hb, ih, show a * (b + 1) = a + a * b by ring,
      rep_add g x (a * b) (Nat.one_le_iff_ne_zero.mpr (by positivity)) a ha]

/-- Row 41: so 24 = 2 x 2 x 2 x 3 with one fixed gap g reads only as eight copies of 3. -/
theorem twentyfour_flattens (g : List ℕ) :
    rep g (rep g (rep g (leaf 3) 2) 2) 2 = rep g (leaf 3) 8 := by
  rw [rep_rep g _ 2 (by norm_num) 2 (by norm_num), rep_rep g _ 2 (by norm_num) 4 (by norm_num)]

/-! ## Row 32: the ternary build has no excess at any n (the old list {3^k, 2 3^k} was too narrow) -/

/-- Row 32 (corrected statement): every level of the ternary build holds exactly n units. -/
theorem ternary_no_excess (d n : ℕ) : (levels blocks3 d n).sum = n := tern_sum d n

/-- Row 32: the old sentence is false as an "exactly these" list: 5 has no excess but is neither
3^k nor 2 3^k. -/
theorem five_not_three_pow : (levels blocks3 2 5).sum = 5 ∧ ¬ ∃ k, 5 = 3 ^ k ∨ 5 = 2 * 3 ^ k := by
  refine ⟨tern_sum 2 5, ?_⟩
  rintro ⟨k, hk⟩
  rcases Nat.lt_or_ge k 2 with h | h
  · interval_cases k <;> simp at hk
  · have : 9 ≤ 3 ^ k := by
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) h
    omega

/-! ## Rows 43, 45: facing marks -/

/-- `ab|`: the mark folds back on the digit it touches (shared, written once): a, b, a. -/
def markR (a b : ℕ) : List ℕ := [a, b, a]
/-- `|ab`: b, a, b. -/
def markL (a b : ℕ) : List ℕ := [b, a, b]
/-- `x|x`: a zero centre holds the mark in the place of absence. -/
def markZero (x : ℕ) : List ℕ := [x, 0, x]
/-- `x|1|x`: a unit centre keeps its seat, the mark bracketed. -/
def markUnit (x : ℕ) : List ℕ := [x, 1, x]
/-- A whole number written to its centre and folded on the last piece written. -/
def foldWhole (ws : List (List ℕ)) : List ℕ := (ws ++ ws.dropLast.reverse).flatten

/-- Row 43: the half-words |00, |10, |01, |11 give back 000, 010, 101, 111; 10| = |01 = 101. -/
theorem half_words : markL 0 0 = [0, 0, 0] ∧ markL 1 0 = [0, 1, 0] ∧ markL 0 1 = [1, 0, 1] ∧
    markL 1 1 = [1, 1, 1] ∧ markR 1 0 = [1, 0, 1] ∧ markL 0 1 = markR 1 0 := by decide

open Upgrades in
/-- Row 43: 4 = 10|,00|,|01; 4 = 101,000,| ; 8 = 10|,,00|,,10|,,00| unfolds to
101,000,101,000,101,000,101; 8 = 4,,0,,| (blocks 4, 0 folded on the zero block). -/
theorem mark_examples :
    markR 1 0 ++ markR 0 0 ++ markL 0 1 = B 4 ∧
    foldWhole [[1, 0, 1], [0, 0, 0]] = B 4 ∧
    foldWhole [markR 1 0, markR 0 0, markR 1 0, markR 0 0] = B 8 ∧
    foldWhole [B 4, B 0] = B 8 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [B, markR, markL, foldWhole]

/-- Row 45: 11 = 5,6,5 = 10|,1|1|1,|01 ,, 11|,0|0,|11 ,, 10|,1|1|1,|01 unfolds to the build of 11. -/
theorem eleven_marked :
    (markR 1 0 ++ markUnit 1 ++ markL 0 1) ++ (markR 1 1 ++ markZero 0 ++ markL 1 1) ++
      (markR 1 0 ++ markUnit 1 ++ markL 0 1) = Upgrades.B 11 := by
  rw [B_eleven]; decide

/-! ### Row 45, every n: the mark rule of the eleven-mirror script unfolds to the build -/

/-- A marked word: `ab|`, `|ab`, `x|x` (mark in the zero), `x|1|x` (unit kept, mark bracketed). -/
inductive Tok
  | r : ℕ → ℕ → Tok
  | l : ℕ → ℕ → Tok
  | z : ℕ → Tok
  | u : ℕ → Tok
  deriving DecidableEq

/-- Mark one word at seat position p in its block (0 left, 1 centre, 2 right). -/
def markWord (p : ℕ) (w : List ℕ) : Tok :=
  match w with
  | [a, b, c] => if p % 3 = 0 then .r a b else if p % 3 = 2 then .l b c
      else if b = 0 then .z a else .u a
  | _ => .z 0

def unmarkTok : Tok → List ℕ
  | .r a b => markR a b
  | .l a b => markL a b
  | .z x => markZero x
  | .u x => markUnit x

/-- Cut a digit string into its words. -/
def chunk3 : List ℕ → List (List ℕ)
  | a :: b :: c :: t => [a, b, c] :: chunk3 t
  | _ => []

/-- The marked form of a string: each word marked by its seat in its block (a lone word is a centre). -/
def markAll (ws : List (List ℕ)) : List Tok :=
  ws.mapIdx (fun i w => markWord (if 1 < ws.length then i else 1) w)

theorem unmark_markWord (p : ℕ) (w : List ℕ) (hw : w ∈ words) : unmarkTok (markWord p w) = w := by
  simp only [words, List.mem_cons, List.mem_nil_iff, or_false] at hw
  rcases (by omega : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2) with h | h | h <;>
    rcases hw with rfl | rfl | rfl | rfl <;>
    simp [markWord, h, unmarkTok, markR, markL, markZero, markUnit]

theorem unmark_mapIdx (ws : List (List ℕ)) (hw : ∀ w ∈ ws, w ∈ words) (g : ℕ → ℕ) :
    (ws.mapIdx (fun i w => markWord (g i) w)).flatMap unmarkTok = ws.flatten := by
  induction ws generalizing g with
  | nil => simp
  | cons w ws ih =>
    rw [List.mapIdx_cons, List.flatMap_cons, unmark_markWord _ _ (hw w (by simp)), List.flatten_cons]
    congr 1
    exact ih (fun x hx => hw x (by simp [hx])) (fun i => g (i + 1))

theorem chunk3_flatten (ws : List (List ℕ)) (hw : ∀ w ∈ ws, w ∈ words) : chunk3 ws.flatten = ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    have h := hw w (by simp)
    have e := ih (fun x hx => hw x (by simp [hx]))
    simp only [words, List.mem_cons, List.mem_nil_iff, or_false] at h
    rw [List.flatten_cons]
    rcases h with rfl | rfl | rfl | rfl <;> simp [chunk3, e]

/-- Every build B(n) is a string of the four words. -/
theorem B_words (n : ℕ) : ∃ ws : List (List ℕ), (∀ w ∈ ws, w ∈ words) ∧ Upgrades.B n = ws.flatten := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 4 with h | h
    · interval_cases n
      · exact ⟨[[0, 0, 0]], by simp [words], by simp [Upgrades.B]⟩
      · exact ⟨[[0, 1, 0]], by simp [words], by simp [Upgrades.B]⟩
      · exact ⟨[[1, 0, 1]], by simp [words], by simp [Upgrades.B]⟩
      · exact ⟨[[1, 1, 1]], by simp [words], by simp [Upgrades.B]⟩
    · rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
      · obtain ⟨ws, hw, hb⟩ := ih k (by omega)
        refine ⟨ws ++ [[0, 0, 0]] ++ ws, ?_, ?_⟩
        · intro w hw'; simp only [List.mem_append, List.mem_singleton] at hw'
          rcases hw' with (h1 | rfl) | h1
          · exact hw w h1
          · simp [words]
          · exact hw w h1
        · rw [Upgrades.B_even k (by omega), hb]; simp
      · obtain ⟨ws, hw, hb⟩ := ih k (by omega)
        obtain ⟨vs, hv, hb'⟩ := ih (k + 1) (by omega)
        refine ⟨ws ++ vs ++ ws, ?_, ?_⟩
        · intro w hw'; simp only [List.mem_append] at hw'
          rcases hw' with (h1 | h1) | h1
          · exact hw w h1
          · exact hv w h1
          · exact hw w h1
        · rw [Upgrades.B_odd k (by omega), hb, hb']; simp

/-- The marked string of n (the eleven-mirror script's `mark`, commas aside). -/
def marked (n : ℕ) : List Tok := markAll (chunk3 (Upgrades.B n))

/-- Row 45, every n (the script checked n < 400): the marked string unfolds to the build exactly. -/
theorem marked_unfolds (n : ℕ) : (marked n).flatMap unmarkTok = Upgrades.B n := by
  obtain ⟨ws, hw, hb⟩ := B_words n
  rw [marked, hb, chunk3_flatten ws hw, markAll, unmark_mapIdx ws hw]

/-- Row 45: the marked string of 11 is 10|,1|1|1,|01 ,, 11|,0|0,|11 ,, 10|,1|1|1,|01. -/
theorem marked_eleven : marked 11 =
    [.r 1 0, .u 1, .l 0 1, .r 1 1, .z 0, .l 1 1, .r 1 0, .u 1, .l 0 1] := by
  rw [marked, B_eleven]; decide

/-! ## Row 48: only the neighbours k, k+1 occur at each level -/

/-- The blocks of the halving build of m one level down, hinges left out: k,k or k,k+1,k. -/
def halves (m : ℕ) : List ℕ := if m % 2 = 0 then [m / 2, m / 2] else [m / 2, m / 2 + 1, m / 2]

/-- The blocks at level d. -/
def lvl : ℕ → ℕ → List ℕ
  | 0, n => [n]
  | d + 1, n => (lvl d n).flatMap halves

/-- Row 48, every n and every level: each block at level d is n/2^d or n/2^d + 1. -/
theorem neighbours (n d : ℕ) : ∀ x ∈ lvl d n, x = n / 2 ^ d ∨ x = n / 2 ^ d + 1 := by
  induction d with
  | zero => simp [lvl]
  | succ d ih =>
    intro x hx
    simp only [lvl, List.mem_flatMap] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    have hk := ih y hy
    rw [pow_succ, ← Nat.div_div_eq_div_mul]
    unfold halves at hxy
    split_ifs at hxy <;> simp at hxy <;> omega

theorem lvl_nineteen : lvl 1 19 = [9, 10, 9] ∧ lvl 2 19 = [4, 5, 4, 5, 5, 4, 5, 4] := by decide

/-- Row 48: the ladders of 19 and 97. -/
theorem ladder_examples :
    PySRFinds.ladder 19 = [(9, 10), (4, 5), (2, 3)] ∧
    PySRFinds.ladder 97 = [(48, 49), (24, 25), (12, 13), (6, 7), (3, 4), (1, 2)] := by
  constructor <;> simp [PySRFinds.ladder, PySRFinds.ladderFrom]

/-! ## Row 50: the unit count u, its values, u(19) = 44 -/

open RatioTwoLine in
theorem u_values :
    [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16].map u =
      [1, 2, 3, 4, 7, 6, 10, 8, 15, 14, 20, 12, 22, 20, 28, 16] := by simp [u]

open RatioTwoLine in
/-- Row 50: 19 climbs (2,3) -> (4,7) -> (15,14) -> 44. -/
theorem u_nineteen : (u 2, u 3) = (2, 3) ∧ (u 4, u 5) = (4, 7) ∧ (u 9, u 10) = (15, 14) ∧
    u 19 = 44 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [u]

/-! ## Row 58: decimal mirrors below the ratio-two line up to 2^20 -/

open RatioTwoLine in
theorem u_pow_mul (m : ℕ) (hm : 1 ≤ m) (j : ℕ) : u (2 ^ j * m) = 2 ^ j * u m := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, mul_comm (2 ^ j) 2, mul_assoc, u_even _ (Nat.one_le_iff_ne_zero.mpr (by positivity)),
      ih]
    ring

open RatioTwoLine in
/-- Every n below the line is 2^j m with m odd on a strand or a pair point (and back). -/
theorem below_shape (n : ℕ) (hn : 1 ≤ n) : u n < 2 * n ↔ ∃ j m, n = 2 ^ j * m ∧ onStrand m := by
  constructor
  · induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro h
      rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
      · rw [u_even k (by omega)] at h
        obtain ⟨j, m, hk, hm⟩ := ih k (by omega) (by omega) (by omega)
        exact ⟨j + 1, m, by rw [hk, pow_succ]; ring, hm⟩
      · exact ⟨0, 2 * k + 1, by simp, (ratio_two_line _ (by simp)).mp h⟩
  · rintro ⟨j, m, rfl, hm⟩
    have hm1 : 1 ≤ m := by
      rcases hm with rfl | rfl | rfl | ⟨a, _, rfl⟩ | ⟨a, _, rfl⟩ <;> norm_num
    rw [u_pow_mul m hm1]
    have := strand_below m hm
    have : 0 < 2 ^ j := by positivity
    nlinarith

/-- Decimal digits with fuel (least significant first). -/
def dig : ℕ → ℕ → List ℕ
  | 0, _ => []
  | f + 1, n => if n = 0 then [] else n % 10 :: dig f (n / 10)

theorem dig_eq (f n : ℕ) (h : n < 10 ^ f) : dig f n = Nat.digits 10 n := by
  induction f generalizing n with
  | zero => simp at h; subst h; rfl
  | succ f ih =>
    rw [dig]
    split_ifs with h0
    · subst h0; rfl
    · rw [Nat.digits_def' (by norm_num) (by omega), ih (n / 10) (by rw [pow_succ] at h; omega)]

def palB (n : ℕ) : Bool := (dig 20 n).reverse == dig 20 n

theorem pal_iff (n : ℕ) (h : n < 10 ^ 20) :
    (Nat.digits 10 n).reverse = Nat.digits 10 n ↔ palB n = true := by
  rw [palB, dig_eq 20 n h]; simp

def mirrorsBelow : List ℕ := [11, 22, 33, 44, 66, 88, 272, 2112, 4224, 8448]

def okC (c : ℕ) : Prop := 10 ≤ c → c < 2 ^ 20 → palB c = true → c ∈ mirrorsBelow
instance : DecidablePred okC := fun c => by unfold okC; infer_instance

theorem ok_pow : ∀ j < 20, okC (2 ^ j * 1) := by decide +kernel
theorem ok_eleven : ∀ j < 20, okC (2 ^ j * 11) := by decide +kernel
theorem ok_fifteen : ∀ j < 20, okC (2 ^ j * 15) := by decide +kernel
theorem ok_strand_one : ∀ j < 20, ∀ a < 20, okC (2 ^ j * (2 ^ a + 1)) := by decide +kernel
theorem ok_strand_two : ∀ j < 20, ∀ a < 20, okC (2 ^ j * (3 * 2 ^ a + 1)) := by decide +kernel

open RatioTwoLine in
/-- Row 58: the decimal mirrors of two or more digits below the line u = 2n, for n < 2^20, are
exactly 11, 22, 33, 44, 66, 88, 272, 2112, 4224, 8448. -/
theorem decimal_mirrors_below (n : ℕ) (h10 : 10 ≤ n) (h20 : n < 2 ^ 20) :
    (u n < 2 * n ∧ (Nat.digits 10 n).reverse = Nat.digits 10 n) ↔ n ∈ mirrorsBelow := by
  rw [pal_iff n (by omega)]
  constructor
  · rintro ⟨hu, hp⟩
    obtain ⟨j, m, rfl, hm⟩ := (below_shape _ (by omega)).mp hu
    have hm1 : 1 ≤ m := by
      rcases hm with rfl | rfl | rfl | ⟨a, _, rfl⟩ | ⟨a, _, rfl⟩ <;> norm_num
    have hj : j < 20 := by
      have : 2 ^ j < 2 ^ 20 := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ hm1) h20
      exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
    have hmle : m < 2 ^ 20 := lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (by positivity)) h20
    rcases hm with rfl | rfl | rfl | ⟨a, _, rfl⟩ | ⟨a, _, rfl⟩
    · exact ok_pow j hj h10 h20 hp
    · exact ok_eleven j hj h10 h20 hp
    · exact ok_fifteen j hj h10 h20 hp
    · have h' : 2 ^ a < 2 ^ 20 := by omega
      have ha : a < 20 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h'
      exact ok_strand_one j hj a ha h10 h20 hp
    · have h' : 2 ^ a < 2 ^ 20 := by omega
      have ha : a < 20 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h'
      exact ok_strand_two j hj a ha h10 h20 hp
  · intro h
    simp only [mirrorsBelow, List.mem_cons, List.mem_nil_iff, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by simp [u], by decide⟩

/-! ## Row 63: the even line -/

/-- The product of places on the even line: place i (the number 2i) times place j. -/
def otimes (i j : ℕ) : ℕ := 2 * i * j

/-- Row 63: (2i)(2j) is the number at place i (x) j; 1 (x) 1 = 2, which is 2 x 2 = 4. -/
theorem even_line_product (i j : ℕ) : (2 * i) * (2 * j) = 2 * otimes i j ∧ otimes 1 1 = 2 ∧
    2 * otimes 1 1 = 2 * 2 := by
  unfold otimes; refine ⟨by ring, rfl, rfl⟩

open PySRFinds in
/-- Row 63: every 2p with p an odd prime is an even-line prime (2 mod 4, not 2). -/
theorem two_p_even_world (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) : evenWorldPrime (2 * p) := by
  have ho := hp.odd_of_ne_two h2
  have h2p : 0 < 2 * p := by have := hp.two_le; omega
  rw [evenWorldPrime_iff _ h2p]
  have h3 := hp.two_le
  obtain ⟨k, hk⟩ := ho
  subst hk
  constructor <;> omega

open PySRFinds in
/-- Row 63: the two readings first part at 18 = 2 x 9: every even-line prime below 18 is twice a
prime, 18 is not. (Reading 2p with p = 2 gives 4, which is not an even-line prime.) -/
theorem first_part_eighteen : evenWorldPrime 18 ∧ ¬ (18 / 2).Prime ∧
    (∀ n < 18, 0 < n → evenWorldPrime n → (n / 2).Prime) ∧ ¬ evenWorldPrime 4 := by decide

/-- Splits of n into two even-line factors (each 2 or an even-line prime), a <= n/a. -/
def splits (n : ℕ) : List (ℕ × ℕ) :=
  ((List.range (n + 1)).filter (fun a => 2 ≤ a ∧ a % 2 = 0 ∧ a * a ≤ n ∧ n % a = 0 ∧
    (a = 2 ∨ (a % 4 = 2 ∧ a ≠ 2)) ∧ (n / a = 2 ∨ ((n / a) % 4 = 2 ∧ n / a ≠ 2)))).map
    (fun a => (a, n / a))

/-- Row 63: 36 = 2 x 18 = 6 x 6; 60 = 2 x 30 = 6 x 10; 180 = 2 x 90 = 6 x 30 = 10 x 18 (three splits). -/
theorem splits_examples : splits 36 = [(2, 18), (6, 6)] ∧ splits 60 = [(2, 30), (6, 10)] ∧
    splits 180 = [(2, 90), (6, 30), (10, 18)] := by decide

/-! ## Row 65: p = 1 mod 4 exactly when p is a sum of two squares (odd p prime) -/

/-- Row 65 (the same set reached by Fermat and Euler by another route; Mathlib's
`Nat.Prime.sq_add_sq` is used for one direction). -/
theorem one_mod_four_iff_two_squares (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) :
    p % 4 = 1 ↔ ∃ x y : ℕ, x ^ 2 + y ^ 2 = p := by
  have ho := hp.odd_of_ne_two h2
  constructor
  · intro h
    have := Fact.mk hp
    exact Nat.Prime.sq_add_sq (by omega)
  · rintro ⟨x, y, rfl⟩
    have := Upgrades.two_squares_mod_four x y
    obtain ⟨k, hk⟩ := ho
    omega

/-- Row 65 with row 64: an odd prime 2k+1 has odd midpoint k+1 exactly when it is a sum of two squares. -/
theorem odd_midpoint_iff_two_squares (k : ℕ) (hp : (2 * k + 1).Prime) (_hk : 1 ≤ k) :
    (k + 1) % 2 = 1 ↔ ∃ x y : ℕ, x ^ 2 + y ^ 2 = 2 * k + 1 := by
  rw [← one_mod_four_iff_two_squares _ hp (by omega)]; omega

/-! ## Row 68: the paradox, a triple read by the wrong mirror -/

theorem paradox : read 9 9 2 = 18 ∧ read 9 9 3 = 27 ∧ read 1 1 2 = 2 ∧ read 1 1 3 = 3 := by decide

/-! ## Row 69: the imbalance -/

/-- Row 69: no imbalance exactly at 2^a and 3 2^a (and 0). -/
theorem imb_zero_iff (n : ℕ) : TwoMirrors.imb n = 0 ↔ n = 0 ∨ ∃ a, n = 2 ^ a ∨ n = 3 * 2 ^ a := by
  have h := TwoMirrors.u_eq_add_imb n
  rw [PrimeHandOff.u_eq] at h
  rw [← RatioTwoLine.fixed_iff]
  omega

/-- Row 69: 22 = 11,0,11 carries 5+2+2+5+2+2 = 18 = 40 - 22. -/
theorem twentytwo_imb : TwoMirrors.imb 22 = 18 ∧ RatioTwoLine.u 22 = 40 ∧
    5 + 2 + 2 + 5 + 2 + 2 = 40 - 22 := by
  refine ⟨?_, ?_, rfl⟩
  · simp [TwoMirrors.imb]
  · simp [RatioTwoLine.u]

/-! ## Row 71: the reflection mark notation (notation A of the two-mirrors script) -/

def wordC (n : ℕ) : List Char :=
  if n = 0 then ['0', '0', '0'] else if n = 1 then ['0', '1', '0']
  else if n = 2 then ['1', '0', '1'] else ['1', '1', '1']

/-- Notation A of the reflection build, L|,C,|R with h commas at height h (fuel f >= depth). -/
def markRf : ℕ → ℕ → List Char × ℕ
  | 0, n => (wordC n, 0)
  | f + 1, n =>
    if n ≤ 3 then (wordC n, 0) else
    let l := markRf f (n / 2)
    let c := if n % 2 = 0 then (wordC 0, 0) else markRf f (n / 2 + 1)
    let h := max l.2 c.2 + 1
    (l.1 ++ ['|'] ++ List.replicate h ',' ++ c.1 ++ List.replicate h ',' ++ ['|'] ++ l.1, h)

/-- Row 71: 27 takes 189 symbols as a reflection and 49 as a turn. -/
theorem twentyseven_marks : (markRf 27 27).1.length = 189 ∧ (PySRFinds.markT 2).length = 49 :=
  ⟨by decide +kernel, PySRFinds.markT_27⟩

end ClaimsA

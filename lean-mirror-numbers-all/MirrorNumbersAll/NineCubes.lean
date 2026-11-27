import Mathlib

/-!
# Nine, cubes, 18 (tUrUq's mirror method, 11-26-2026)

The mark |^1 = base + 1 (3 in base 2, 11 in base 10). Its square is 1,2,1 and its cube 1,3,3,1 in that base
(mark_square, mark_cube): 9 = 3² is the 1,2,1 of base 2, 27 = 3³ its 1,3,3,1. Decimal reversal has two mirrors,
11 = 10 + 1 and 9 = 10 − 1 (rev_sum, rev_diff); on the nines it is the 11-line k ↔ 11 − k (nine_rev): 18 ↔ 81.
A cube's own picture is p's halving scaled by p (cube_picture); its halving reads p² ± p + 1 (cube_halving).
The squares of 3, 5, 7 sit one past a self-counting number (nine_self_counting). The lake of the turn tower: 10³ ≡ 1 mod 27, 10⁹ ≡ 1 mod 81
(period_27, period_81). Strands: a seat with a second picture of wing d ≥ 2 is closed (picture_closed); a sum of
two cubes is closed unless 1 + 1 = 2 (cube_sum_closed). 18 facts (eighteen). No sorry, no native_decide.
-/

namespace NineCubes

/-- (|^1)² = 1,2,1 in its base: (b+1)² = b² + 2b + 1. 9 = 4 + 2·2 + 1, 121 = 100 + 20 + 1. -/
theorem mark_square (b : ℕ) : (b + 1) ^ 2 = b ^ 2 + 2 * b + 1 := by ring

/-- (|^1)³ = 1,3,3,1 in its base: (b+1)³ = b³ + 3b² + 3b + 1. 27 = 8 + 12 + 6 + 1, 1331. -/
theorem mark_cube (b : ℕ) : (b + 1) ^ 3 = b ^ 3 + 3 * b ^ 2 + 3 * b + 1 := by ring

/-- Two-digit reversal, the sum mirror: n + rev n = 11 × digit sum. -/
theorem rev_sum (a b : ℕ) : (10 * a + b) + (10 * b + a) = 11 * (a + b) := by ring

/-- Two-digit reversal, the difference mirror: n − rev n = 9 × digit difference. -/
theorem rev_diff (a b : ℤ) : (10 * a + b) - (10 * b + a) = 9 * (a - b) := by ring

/-- The nines: 9k has digits (k−1, 10−k); reversed it is 9(11 − k). The 11-line on the nines is digit reversal. -/
theorem nine_rev (k : ℕ) (h1 : 1 ≤ k) (h2 : k ≤ 10) :
    9 * k = 10 * (k - 1) + (10 - k) ∧ 10 * (10 - k) + (k - 1) = 9 * (11 - k) := by
  constructor <;> omega

/-- 18 reversed is 81 = 9²; 27 reversed is 72 = 2³·3². -/
theorem eighteen_rev : 10 * 8 + 1 = 9 ^ 2 ∧ 10 * 2 + 7 = 3 ^ 3 ∧ 10 * 7 + 2 = 2 ^ 3 * 3 ^ 2 := by norm_num

/-- The square's own picture has no wing: p² = p² − 0². -/
theorem square_picture (p : ℤ) : p ^ 2 - 0 ^ 2 = p * p := by ring

/-- The cube's own picture is p's halving (m, m+1, m), p = 2m+1, scaled by p: (p(m+1))² − (pm)² = p³. -/
theorem cube_picture (m : ℤ) :
    ((2 * m + 1) * (m + 1)) ^ 2 - ((2 * m + 1) * m) ^ 2 = (2 * m + 1) ^ 3 := by ring

/-- The cube's halving: wing (p³−1)/2 = m(p²+p+1), center (p³+1)/2 = (m+1)(p²−p+1), p = 2m+1. For 3: 13, 2·7. -/
theorem cube_halving (m : ℤ) :
    (2 * m + 1) ^ 3 - 1 = 2 * (m * ((2 * m + 1) ^ 2 + (2 * m + 1) + 1)) ∧
    (2 * m + 1) ^ 3 + 1 = 2 * ((m + 1) * ((2 * m + 1) ^ 2 - (2 * m + 1) + 1)) := by
  constructor <;> ring

/-- 7 × 13 = 91 = 1,1,1 in base 9, and 1001 = 11 × 91. -/
theorem ninety_one : 7 * 13 = 9 ^ 2 + 9 + 1 ∧ 1001 = 11 * (7 * 13) := by norm_num

/-- The squares of 3, 5, 7 sit one past the self-counting numbers 2³, 3·2³, 3·2⁴. -/
theorem nine_self_counting : 3 ^ 2 = 2 ^ 3 + 1 ∧ 5 ^ 2 = 3 * 2 ^ 3 + 1 ∧ 7 ^ 2 = 3 * 2 ^ 4 + 1 := by norm_num

/-- Two powers of 2 that differ by 2 are 2 and 4: so (p−1)(p+1) = 2^a only at p = 3. -/
theorem pow_two_gap (i j : ℕ) (h : 2 ^ j = 2 ^ i + 2) : i = 1 ∧ j = 2 := by
  have hij : i < j := by
    by_contra hc
    have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (not_lt.mp hc)
    omega
  rcases i with _ | _ | i
  · exfalso
    simp at h
    rcases j with _ | j
    · simp at h
    · rw [pow_succ] at h; omega
  · have h4 : 2 ^ j = 2 ^ 2 := by simpa using h
    exact ⟨rfl, Nat.pow_right_injective le_rfl h4⟩
  · exfalso
    have h4 : 4 ∣ 2 ^ (i + 2) := ⟨2 ^ i, by ring⟩
    have h4' : 4 ∣ 2 ^ j := by
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hij
      exact ⟨2 ^ (i + d + 1), by ring⟩
    omega

/-- The lake of 27: 10³ ≡ 1 mod 27 and 10 ≢ 1: period 3. 1/27 = 0.(037). -/
theorem period_27 : 10 ^ 3 % 27 = 1 ∧ 10 % 27 ≠ 1 := by norm_num

/-- The lake of 81: 10⁹ ≡ 1 mod 81 and 10³ ≢ 1: period 9. 1/81 = 0.(012345679). -/
theorem period_81 : 10 ^ 9 % 81 = 1 ∧ 10 ^ 3 % 81 ≠ 1 := by norm_num

/-- Cubing the base: 10³ − 1 = 27 × 37 (3³ appears), 10³ + 1 = 7 × 11 × 13. -/
theorem base_cubed : 10 ^ 3 - 1 = 3 ^ 3 * 37 ∧ 10 ^ 3 + 1 = 7 * 11 * 13 := by norm_num

/-- STRAND (pictures). A seat y with a second picture y + w² = c², c = w + d, d ≥ 2, is y = d(2w + d): closed. -/
theorem picture_faces (w d y : ℕ) (hy : y + w ^ 2 = (w + d) ^ 2) : y = d * (2 * w + d) := by
  nlinarith

theorem picture_closed (w d y : ℕ) (hd : 2 ≤ d) (hy : y + w ^ 2 = (w + d) ^ 2) : ¬ Nat.Prime y := by
  rw [picture_faces w d y hy]
  intro hp
  rcases hp.eq_one_or_self_of_dvd d (Dvd.intro _ rfl) with h | h
  · omega
  · nlinarith

/-- STRAND (cube sums). a³ + b³ = (a + b)(a² − ab + b²). -/
theorem cube_sum_faces (a b : ℤ) : a ^ 3 + b ^ 3 = (a + b) * (a ^ 2 - a * b + b ^ 2) := by ring

/-- A sum of two cubes a³ + b³ with 1 ≤ b ≤ a and a ≥ 2 is closed; only 1³ + 1³ = 2 (the even prime) is open. -/
theorem cube_sum_closed (a b : ℕ) (hb : 1 ≤ b) (hab : b ≤ a) (ha : 2 ≤ a) : ¬ Nat.Prime (a ^ 3 + b ^ 3) := by
  intro hp
  have hdvd : a + b ∣ a ^ 3 + b ^ 3 := by
    have : a ^ 3 + b ^ 3 = (a + b) * (a ^ 2 + b ^ 2 - a * b) := by
      have hle : a * b ≤ a ^ 2 + b ^ 2 := by nlinarith
      zify [hle]; ring
    rw [this]; exact Dvd.intro _ rfl
  rcases hp.eq_one_or_self_of_dvd (a + b) hdvd with h | h
  · omega
  · have h1 : 2 * a ≤ a * a := Nat.mul_le_mul_right a ha
    have h2 : 2 * a * a ≤ a * a * a := Nat.mul_le_mul_right a h1
    have h3 : b ≤ b ^ 3 := Nat.le_self_pow (by norm_num) b
    have h4 : a ^ 3 = a * a * a := by ring
    nlinarith

/-- 18: center of 17|19, sum of 7|11 (center 9), 2 × 9, first 2 × odd that is not 2 × prime (9 = 3 × 3). -/
theorem eighteen : (17 + 19) / 2 = 18 ∧ 7 + 11 = 18 ∧ (7 + 11) / 2 = 9 ∧ 18 = 2 * 9 ∧ 9 = 3 * 3 ∧
    (6 + 9 + 12 + 15 + 18 + 21 : ℕ) = 81 := by norm_num

/-- The m line: 11 − 2 = 9 and 22 − 4 = 18: the even prime and its square land on 9 and 18. -/
theorem m_line : 11 - 2 = 9 ∧ 22 - 2 ^ 2 = 18 := by norm_num

end NineCubes

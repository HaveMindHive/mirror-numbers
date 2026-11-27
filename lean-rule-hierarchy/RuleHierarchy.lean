import Mathlib

/-!
# Rule hierarchy (tUrUq's mirror method, 11-26-2026): the 5 and 7 inside the 2,3 structure

Seat rules read the hop h from p: the r-strand closes the seat p + 2h exactly when h ≡ c_r · p (mod r),
with c_5 = 2, c_7 = 3, c_11 = 5, c_13 = 6. The hand-off (2,3) names the first seat off 2 and 3 past p;
the 5 rule sits above it exactly from the classes p ≡ 1, 23 (mod 30), the 7 rule exactly from p ≡ 5, 31
(mod 42). Pentagonal wings: the wing (y-1)/2 of a seat is 12 × (generalized pentagonal) exactly when y is
the square of a 6k ± 1 number. The even-centre picture k, k+1, k lives on n ≡ 3 (mod 4) and recurses one
level exactly on n ≡ 7 (mod 8). The per-11-block mirror of an odd number is even (a frame, not a seat rule).
No sorry, no native_decide.
-/

namespace RuleHierarchy

/-- The 5-strand as a hop rule: p + 2h is a 5-seat exactly when h ≡ 2p (mod 5). -/
theorem five_class (p h : ℕ) : (p + 2 * h) % 5 = 0 ↔ h % 5 = (2 * p) % 5 := by omega

/-- The 7-strand: p + 2h is a 7-seat exactly when h ≡ 3p (mod 7). -/
theorem seven_class (p h : ℕ) : (p + 2 * h) % 7 = 0 ↔ h % 7 = (3 * p) % 7 := by omega

/-- The 11-strand: h ≡ 5p (mod 11). -/
theorem eleven_class (p h : ℕ) : (p + 2 * h) % 11 = 0 ↔ h % 11 = (5 * p) % 11 := by omega

/-- The 13-strand: h ≡ 6p (mod 13). -/
theorem thirteen_class (p h : ℕ) : (p + 2 * h) % 13 = 0 ↔ h % 13 = (6 * p) % 13 := by omega

/-- The hand-off's first seat past an off-2,3 number p: p + 4 from the first seat 6k+1, p + 2 from 6k+5. -/
def handOff (p : ℕ) : ℕ := if p % 6 = 1 then p + 4 else p + 2

/-- The hand-off's seat is off 2 and 3. -/
theorem handOff_off (p : ℕ) (h2 : p % 2 = 1) (_h3 : p % 3 ≠ 0) :
    handOff p % 2 = 1 ∧ handOff p % 3 ≠ 0 := by
  unfold handOff; split_ifs <;> omega

/-- 5 sits above the hand-off exactly from p ≡ 1 or 23 (mod 30). -/
theorem five_above_handoff (p : ℕ) (h2 : p % 2 = 1) (h3 : p % 3 ≠ 0) :
    handOff p % 5 = 0 ↔ p % 30 = 1 ∨ p % 30 = 23 := by
  obtain ⟨k, r, hr, rfl⟩ : ∃ k r, r < 30 ∧ p = 30 * k + r :=
    ⟨p / 30, p % 30, Nat.mod_lt p (by norm_num), (Nat.div_add_mod p 30).symm⟩
  unfold handOff; interval_cases r <;> split_ifs <;> omega

/-- 7 sits above the hand-off exactly from p ≡ 5 or 31 (mod 42). -/
theorem seven_above_handoff (p : ℕ) (h2 : p % 2 = 1) (h3 : p % 3 ≠ 0) :
    handOff p % 7 = 0 ↔ p % 42 = 5 ∨ p % 42 = 31 := by
  unfold handOff; split_ifs <;> constructor <;> intro hh <;> omega

/-- 11 sits above the hand-off exactly from p ≡ 7 or 53 (mod 66). -/
theorem eleven_above_handoff (p : ℕ) (h2 : p % 2 = 1) (h3 : p % 3 ≠ 0) :
    handOff p % 11 = 0 ↔ p % 66 = 7 ∨ p % 66 = 53 := by
  obtain ⟨k, r, hr, rfl⟩ : ∃ k r, r < 66 ∧ p = 66 * k + r :=
    ⟨p / 66, p % 66, Nat.mod_lt p (by norm_num), (Nat.div_add_mod p 66).symm⟩
  unfold handOff; interval_cases r <;> split_ifs <;> omega

/-- Pentagonal wing, minus side: (6k-1)² = 24·P + 1 with 2P = k(3k-1). -/
theorem pent_square_minus (k P : ℤ) (hP : 2 * P = k * (3 * k - 1)) :
    (6 * k - 1) ^ 2 = 24 * P + 1 := by
  have : 24 * P = 12 * (2 * P) := by ring
  rw [this, hP]; ring

/-- Pentagonal wing, plus side: (6k+1)² = 24·P + 1 with 2P = k(3k+1). -/
theorem pent_square_plus (k P : ℤ) (hP : 2 * P = k * (3 * k + 1)) :
    (6 * k + 1) ^ 2 = 24 * P + 1 := by
  have : 24 * P = 12 * (2 * P) := by ring
  rw [this, hP]; ring

/-- The wing of (6k±1)² is 12 × P: the wing is (y-1)/2 = 12 P. -/
theorem pent_wing (k P : ℤ) (hP : 2 * P = k * (3 * k + 1)) :
    ((6 * k + 1) ^ 2 - 1) / 2 = 12 * P := by
  rw [pent_square_plus k P hP]; omega

/-- Even centre: odd n = k, k+1, k has k+1 even exactly when n ≡ 3 (mod 4). -/
theorem even_centre_iff (n : ℕ) (hn : n % 2 = 1) : ((n + 1) / 2) % 2 = 0 ↔ n % 4 = 3 := by omega

/-- The picture recurses one level (the wing k is again k', k'+1, k' with even centre) exactly on n ≡ 7 (mod 8). -/
theorem two_levels (n : ℕ) (hn : n % 2 = 1) :
    (n % 4 = 3 ∧ ((n - 1) / 2) % 4 = 3) ↔ n % 8 = 7 := by omega

/-- A prime wing needs the even centre: if n ≡ 1 (mod 4) the wing (n-1)/2 is even. -/
theorem odd_centre_even_wing (n : ℕ) (hn : n % 4 = 1) : ((n - 1) / 2) % 2 = 0 := by omega

/-- The per-11-block mirror 11a + r ↦ 11a + 11 - r sends an odd number to an even one: a frame, not a seat rule. -/
theorem block_mirror_even (a r : ℕ) (_hr : r ≤ 11) (hodd : (11 * a + r) % 2 = 1) :
    (11 * a + 11 - r) % 2 = 0 := by omega

/-- The offset mirror n ↦ O - n keeps the gap, so keeps every h-rule's verdict. -/
theorem offset_keeps_gap (O p q : ℤ) : (O - p) - (O - q) = q - p := by ring

/-- Combined allowed classes: off 2, 3 and 5, every off-class of p leaves 16 of 30 half-gap classes h mod 30. -/
theorem allowed_mod_30 :
    ∀ r ∈ ({1, 7, 11, 13, 17, 19, 23, 29} : Finset ℕ),
      ((Finset.range 30).filter
        (fun h => (r + 2 * h) % 2 ≠ 0 ∧ (r + 2 * h) % 3 ≠ 0 ∧ (r + 2 * h) % 5 ≠ 0)).card = 16 := by
  decide

end RuleHierarchy

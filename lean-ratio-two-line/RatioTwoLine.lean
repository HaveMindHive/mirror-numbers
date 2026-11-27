import Mathlib

/-!
# The ratio-two line of the units count (tUrUq, 11-26-2026)

`u n` = units of `n` in the facing number line:
u 0 = 0, u 1 = 1, u 2 = 2, u 3 = 3, and for n > 3
u (2k) = 2 u k,  u (2k+1) = 2 u k + u (k+1).

Proven here (no sorry, no native_decide):
1. `u_pow_add_one`    : u (2^a + 1) = 2^(a+1) - 1            (a ≥ 1)
2. `u_three_pow_add_one` : u (3*2^a + 1) = 2*(3*2^a - 1)    (all a ≥ 0; a = 0 is n = 4)
3. `u_ne_two_mul`     : u n ≠ 2n                              (n ≥ 1)
4. `ratio_two_line`   : for odd n, u n < 2n ↔ n ∈ {1, 11, 15} or n = 2^a+1 (a ≥ 1)
                        or n = 3*2^a+1 (a ≥ 1).
-/

namespace RatioTwoLine

def u : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | n + 4 =>
    if (n + 4) % 2 = 0 then 2 * u ((n + 4) / 2)
    else 2 * u ((n + 4) / 2) + u ((n + 4) / 2 + 1)
  decreasing_by all_goals omega

@[simp] theorem u0 : u 0 = 0 := by simp [u]
@[simp] theorem u1 : u 1 = 1 := by simp [u]
@[simp] theorem u2 : u 2 = 2 := by simp [u]
@[simp] theorem u3 : u 3 = 3 := by simp [u]

theorem u_even (k : ℕ) (hk : 1 ≤ k) : u (2 * k) = 2 * u k := by
  rcases Nat.lt_or_ge k 2 with h | h
  · obtain rfl : k = 1 := by omega
    simp
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
    have e : 2 * (m + 2) = 2 * m + 4 := by ring
    rw [e, u]
    have h1 : (2 * m + 4) % 2 = 0 := by omega
    have h2 : (2 * m + 4) / 2 = m + 2 := by omega
    simp [h1, h2]

theorem u_odd (k : ℕ) (hk : 2 ≤ k) : u (2 * k + 1) = 2 * u k + u (k + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have e : 2 * (m + 2) + 1 = (2 * m + 1) + 4 := by ring
  rw [e, u]
  have h1 : ¬ (2 * m + 1 + 4) % 2 = 0 := by omega
  have h2 : (2 * m + 1 + 4) / 2 = m + 2 := by omega
  simp [h1, h2]

theorem u_pow (a : ℕ) : u (2 ^ a) = 2 ^ a := by
  induction a with
  | zero => simp
  | succ a ih => rw [pow_succ, mul_comm, u_even _ (Nat.one_le_two_pow), ih]

theorem u_three_pow (a : ℕ) : u (3 * 2 ^ a) = 3 * 2 ^ a := by
  induction a with
  | zero => simp
  | succ a ih =>
    have e : 3 * 2 ^ (a + 1) = 2 * (3 * 2 ^ a) := by ring
    rw [e, u_even _ (by have := Nat.one_le_two_pow (n := a); omega), ih]

/-! ## 1. The power strand -/

theorem u_pow_add_one (a : ℕ) (ha : 1 ≤ a) : u (2 ^ a + 1) = 2 ^ (a + 1) - 1 := by
  induction a, ha using Nat.le_induction with
  | base => simp
  | succ a ha ih =>
    have h2 : 2 ≤ 2 ^ a := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
    have e : 2 ^ (a + 1) + 1 = 2 * 2 ^ a + 1 := by ring
    rw [e, u_odd _ h2, u_pow, ih]
    have : 2 ^ (a + 1 + 1) = 4 * 2 ^ a := by ring
    have : 2 ^ (a + 1) = 2 * 2 ^ a := by ring
    omega

/-! ## 2. The wall strand (holds for every a ≥ 0; a = 0 gives n = 4, u 4 = 4) -/

theorem u_three_pow_add_one (a : ℕ) : u (3 * 2 ^ a + 1) = 2 * (3 * 2 ^ a - 1) := by
  induction a with
  | zero => rw [show 3 * 2 ^ 0 + 1 = 2 * 2 by norm_num, u_even _ (by norm_num)]; simp
  | succ a ih =>
    have h1 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
    have e : 3 * 2 ^ (a + 1) + 1 = 2 * (3 * 2 ^ a) + 1 := by ring
    rw [e, u_odd _ (by omega), u_three_pow, ih]
    have : 3 * 2 ^ (a + 1) = 2 * (3 * 2 ^ a) := by ring
    omega

/-! ## Bounds -/

theorem u_ge (m : ℕ) : m ≤ u m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp
      · rw [u_even k hk]; have := ih k (by omega); omega
    · rcases Nat.lt_or_ge k 2 with h | h
      · interval_cases k <;> simp
      · rw [u_odd k h]; have := ih k (by omega); have := ih (k + 1) (by omega); omega

/-- Odd `m ≥ 5` sits well above the unit line: `u m ≥ m + k`. -/
theorem u_odd_ge (k : ℕ) (hk : 2 ≤ k) : 3 * k + 1 ≤ u (2 * k + 1) := by
  rw [u_odd k hk]; have := u_ge k; have := u_ge (k + 1); omega

/-- Dichotomy: either `u m = m`, or `5 u m ≥ 7 m`. -/
theorem dich (m : ℕ) : u m = m ∨ 7 * m ≤ 5 * u m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp
      · rw [u_even k hk]; rcases ih k (by omega) with h | h <;> omega
    · rcases Nat.lt_or_ge k 2 with h | h
      · interval_cases k <;> simp
      · right; have := u_odd_ge k h; omega

/-- An odd fixed point `u m = m` is at most 3. -/
theorem odd_fixed_le (k : ℕ) (h : u (2 * k + 1) = 2 * k + 1) : k ≤ 1 := by
  by_contra hk; have := u_odd_ge k (by omega); omega

/-- Fixed points of `u` are exactly `0`, `2^a`, `3*2^a`. -/
theorem fixed_iff (m : ℕ) : u m = m ↔ m = 0 ∨ ∃ a, m = 2 ^ a ∨ m = 3 * 2 ^ a := by
  constructor
  · induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm
      rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
      · rcases Nat.eq_zero_or_pos k with rfl | hk
        · simp
        · rw [u_even k hk] at hm
          rcases ih k (by omega) (by omega) with rfl | ⟨a, rfl | rfl⟩
          · omega
          · exact Or.inr ⟨a + 1, Or.inl (by ring)⟩
          · exact Or.inr ⟨a + 1, Or.inr (by ring)⟩
      · have := odd_fixed_le k hm
        interval_cases k
        · exact Or.inr ⟨0, Or.inl rfl⟩
        · exact Or.inr ⟨0, Or.inr rfl⟩
  · rintro (rfl | ⟨a, rfl | rfl⟩)
    · simp
    · exact u_pow a
    · exact u_three_pow a

/-! ## 3. Never on the line -/

theorem u_ne_two_mul (n : ℕ) (hn : 1 ≤ n) : u n ≠ 2 * n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
    · rw [u_even k (by omega)]; have := ih k (by omega) (by omega); omega
    · rcases Nat.lt_or_ge k 2 with h | h
      · interval_cases k <;> simp
      · rw [u_odd k h]
        intro heq
        rcases dich k with hk | hk
        · exact ih (k + 1) (by omega) (by omega) (by omega)
        rcases dich (k + 1) with hk1 | hk1
        · -- k + 1 fixed; then k is odd ≥ 5
          rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
          · have := odd_fixed_le j hk1
            interval_cases j <;> simp_all
          · rcases Nat.lt_or_ge j 2 with hj | hj
            · interval_cases j <;> simp_all
            · rw [u_odd j hj] at hk heq
              have e : 2 * j + 1 + 1 = 2 * (j + 1) := by ring
              have hc : u (2 * j + 1 + 1) = 2 * u (j + 1) := by rw [e, u_even _ (by omega)]
              omega
        · have : k ≤ 3 := by omega
          interval_cases k <;> simp_all

/-! ## 4. The ratio-two classification for odd n -/

def onStrand (n : ℕ) : Prop :=
  n = 1 ∨ n = 11 ∨ n = 15 ∨ (∃ a, 1 ≤ a ∧ n = 2 ^ a + 1) ∨ (∃ a, 1 ≤ a ∧ n = 3 * 2 ^ a + 1)

theorem strand_below (n : ℕ) (h : onStrand n) : u n < 2 * n := by
  rcases h with rfl | rfl | rfl | ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
  · simp
  · rw [show 11 = 2 * 5 + 1 by rfl, u_odd 5 (by norm_num), show 5 = 2 * 2 + 1 by rfl,
      u_odd 2 le_rfl, show 2 + 1 = 3 by rfl, show 5 + 1 = 2 * 3 by rfl, u_even 3 (by norm_num)]
    simp
  · rw [show 15 = 2 * 7 + 1 by rfl, u_odd 7 (by norm_num), show 7 = 2 * 3 + 1 by rfl,
      u_odd 3 (by norm_num), show 3 + 1 = 2 * 2 by rfl, u_even 2 (by norm_num),
      show 2 * 3 + 1 + 1 = 2 ^ 3 by rfl, u_pow]
    simp
  · rw [u_pow_add_one a ha]
    have : 2 ^ (a + 1) = 2 * 2 ^ a := by ring
    omega
  · rw [u_three_pow_add_one a]
    have : 1 ≤ 2 ^ a := Nat.one_le_two_pow
    omega

theorem below_strand (k : ℕ) (h : u (2 * k + 1) < 2 * (2 * k + 1)) : onStrand (2 * k + 1) := by
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · interval_cases k
    · left; rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨1, le_rfl, rfl⟩)))
  rw [u_odd k hk2] at h
  rcases dich k with hk | hk
  · -- k is a fixed point: k = 2^a or 3*2^a, a ≥ 1 after doubling
    rcases (fixed_iff k).1 hk with h0 | ⟨a, rfl | rfl⟩
    · omega
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a + 1, by omega, by ring⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a + 1, by omega, by ring⟩)))
  rcases dich (k + 1) with hk1 | hk1
  · rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
    · have := odd_fixed_le j hk1
      interval_cases j <;> simp_all
    · rcases Nat.lt_or_ge j 2 with hj | hj
      · interval_cases j <;> simp_all
      · rw [u_odd j hj] at hk h
        have e : 2 * j + 1 + 1 = 2 * (j + 1) := by ring
        have hc : u (2 * j + 1 + 1) = 2 * u (j + 1) := by rw [e, u_even _ (by omega)]
        have hj1 : u (j + 1) = j + 1 := by omega
        have hjj : u j = j := by have := u_ge j; omega
        -- j and j+1 both fixed, j ≥ 2: one is odd, so j ∈ {2, 3}
        have : j ≤ 3 := by
          rcases Nat.even_or_odd' j with ⟨i, rfl | rfl⟩
          · have := odd_fixed_le i hj1; omega
          · have := odd_fixed_le i hjj; omega
        interval_cases j
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inl rfl))
  · have : k ≤ 2 := by omega
    interval_cases k; simp_all

theorem ratio_two_line (n : ℕ) (hn : Odd n) : u n < 2 * n ↔ onStrand n := by
  obtain ⟨k, rfl⟩ := hn
  exact ⟨below_strand k, strand_below _⟩

end RatioTwoLine

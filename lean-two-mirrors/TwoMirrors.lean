import Mathlib

/-!
# Two mirrors (tUrUq, 11-26-2026)

`u` = units of the facing number line (copied from RatioTwoLine.lean):
u 0..3 = 0,1,2,3; for n ≥ 4: u (2k) = 2 u k, u (2k+1) = 2 u k + u (k+1).

No sorry, no admit, no native_decide.
-/

namespace TwoMirrors

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

@[simp] theorem u4 : u 4 = 4 := by rw [show 4 = 2 * 2 by rfl, u_even 2 (by norm_num)]; simp

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

theorem u_three_pow_add_one (a : ℕ) : u (3 * 2 ^ a + 1) = 2 * (3 * 2 ^ a - 1) := by
  induction a with
  | zero => simp
  | succ a ih =>
    have h1 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
    have e : 3 * 2 ^ (a + 1) + 1 = 2 * (3 * 2 ^ a) + 1 := by ring
    rw [e, u_odd _ (by omega), u_three_pow, ih]
    have : 3 * 2 ^ (a + 1) = 2 * (3 * 2 ^ a) := by ring
    omega

/-! ## 1. Step defect `d n = 2 u n − u (n+1)` -/

def d (n : ℕ) : ℤ := 2 * (u n : ℤ) - (u (n + 1) : ℤ)

/-- `d (2k) = d k` for `k = 0` or `k ≥ 2` (fails at `k = 1`: d 2 = 1, d 1 = 0). -/
theorem d_even (k : ℕ) (hk : k = 0 ∨ 2 ≤ k) : d (2 * k) = d k := by
  rcases hk with rfl | hk
  · rfl
  · unfold d
    rw [u_even k (by omega), u_odd k hk]; push_cast; ring

/-- `d (2k+1) = 4 u k` for `k = 0` or `k ≥ 2` (fails at `k = 1`: d 3 = 2, 4 u 1 = 4). -/
theorem d_odd (k : ℕ) (hk : k = 0 ∨ 2 ≤ k) : d (2 * k + 1) = 4 * (u k : ℤ) := by
  rcases hk with rfl | hk
  · simp [d]
  · unfold d
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, u_even (k + 1) (by omega), u_odd k hk]
    push_cast; ring

theorem d_exceptions : d 2 = 1 ∧ d 1 = 0 ∧ d 3 = 2 ∧ 4 * (u 1 : ℤ) = 4 := by
  simp [d]

/-! ## 2. Mod-4 strand law -/

/-- odd strand: `n = 1` or `n = 2^a + 1`, `a ≥ 1`. -/
def P (n : ℕ) : Prop := n = 1 ∨ ∃ a, 1 ≤ a ∧ n = 2 ^ a + 1

/-- `u n ≡ 2 (mod 4)` set over all n. -/
def Q (n : ℕ) : Prop :=
  n = 2 ∨ (∃ a, 1 ≤ a ∧ n = 2 ^ (a + 1) + 2) ∨ (∃ a, 1 ≤ a ∧ n = 3 * 2 ^ a + 1)

theorem P_odd (n : ℕ) (h : P n) : u n % 2 = 1 := by
  rcases h with rfl | ⟨a, ha, rfl⟩
  · simp
  · rw [u_pow_add_one a ha]
    have : 2 ^ (a + 1) = 2 * 2 ^ a := by ring
    have : 1 ≤ 2 ^ a := Nat.one_le_two_pow
    omega

theorem Q_two (n : ℕ) (h : Q n) : u n % 4 = 2 := by
  rcases h with rfl | ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
  · simp
  · rw [show 2 ^ (a + 1) + 2 = 2 * (2 ^ a + 1) by ring, u_even _ (Nat.le_add_left 1 _), u_pow_add_one a ha]
    have : 2 ^ (a + 1) = 2 * 2 ^ a := by ring
    have : 1 ≤ 2 ^ a := Nat.one_le_two_pow
    omega
  · rw [u_three_pow_add_one a]
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    have : 2 ^ (b + 1) = 2 * 2 ^ b := by ring
    have : 1 ≤ 2 ^ b := Nat.one_le_two_pow
    omega

theorem odd_P (n : ℕ) (h : u n % 2 = 1) : P n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp at h
      · rw [u_even k hk] at h; omega
    · rcases Nat.lt_or_ge k 2 with hk | hk
      · interval_cases k
        · left; rfl
        · exact Or.inr ⟨1, le_rfl, rfl⟩
      · rw [u_odd k hk] at h
        rcases ih (k + 1) (by omega) (by omega) with h1 | ⟨a, ha, h1⟩
        · omega
        · exact Or.inr ⟨a + 1, by omega, by rw [pow_succ]; omega⟩

theorem two_Q (n : ℕ) (h : u n % 4 = 2) : Q n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp at h
      · rw [u_even k hk] at h
        rcases odd_P k (by omega) with rfl | ⟨a, ha, rfl⟩
        · left; rfl
        · exact Or.inr (Or.inl ⟨a, ha, by ring⟩)
    · rcases Nat.lt_or_ge k 2 with hk | hk
      · interval_cases k <;> simp at h
      · rw [u_odd k hk] at h
        rcases Nat.mod_two_eq_zero_or_one (u k) with hu | hu
        · -- u k even, so u (k+1) ≡ 2
          rcases ih (k + 1) (by omega) (by omega) with h1 | ⟨b, hb, h1⟩ | ⟨b, hb, h1⟩
          · omega
          · have := P_odd k (Or.inr ⟨b + 1, by omega, by omega⟩); omega
          · exact Or.inr (Or.inr ⟨b + 1, by omega, by rw [pow_succ]; omega⟩)
        · -- u k odd, so k = 2^a + 1 and u (k+1) ≡ 0
          rcases odd_P k hu with h1 | ⟨a, ha, rfl⟩
          · omega
          · rcases Nat.lt_or_ge a 2 with ha2 | ha2
            · obtain rfl : a = 1 := by omega
              exact Or.inr (Or.inr ⟨1, le_rfl, rfl⟩)
            · obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
              have := Q_two (2 ^ (b + 1) + 1 + 1) (Or.inr (Or.inl ⟨b, by omega, by ring⟩))
              omega

/-- Mod-4 strand law over all `n`. -/
theorem u_odd_iff (n : ℕ) : u n % 2 = 1 ↔ P n := ⟨odd_P n, P_odd n⟩
theorem u_two_mod_four_iff (n : ℕ) : u n % 4 = 2 ↔ Q n := ⟨two_Q n, Q_two n⟩

/-- Restricted to odd `n` (the stated law). -/
theorem strand_law_odd (n : ℕ) (hn : Odd n) :
    (u n % 2 = 1 ↔ n = 1 ∨ ∃ a, 1 ≤ a ∧ n = 2 ^ a + 1) ∧
    (u n % 4 = 2 ↔ ∃ a, 1 ≤ a ∧ n = 3 * 2 ^ a + 1) := by
  obtain ⟨m, rfl⟩ := hn
  refine ⟨u_odd_iff _, ?_⟩
  rw [u_two_mod_four_iff]
  constructor
  · rintro (h | ⟨a, -, h⟩ | h)
    · omega
    · rw [pow_succ] at h; omega
    · exact h
  · exact fun h => Or.inr (Or.inr h)

theorem four_dvd_rest (n : ℕ) (hn : Odd n) (h1 : ¬ P n) (h2 : ¬ ∃ a, 1 ≤ a ∧ n = 3 * 2 ^ a + 1) :
    4 ∣ u n := by
  have e := (strand_law_odd n hn)
  have a1 : u n % 2 ≠ 1 := fun h => h1 ((u_odd_iff n).1 h)
  have a2 : u n % 4 ≠ 2 := fun h => h2 (e.2.1 h)
  omega

/-! ## 3. Imbalance law -/

/-- Sum of the wing `k` over every filled-centre triple of the halving tree. -/
def imb : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | n + 4 =>
    if (n + 4) % 2 = 0 then 2 * imb ((n + 4) / 2)
    else (n + 4) / 2 + 2 * imb ((n + 4) / 2) + imb ((n + 4) / 2 + 1)
  decreasing_by all_goals omega

theorem imb_even (k : ℕ) (hk : 2 ≤ k) : imb (2 * k) = 2 * imb k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  rw [show 2 * (m + 2) = 2 * m + 4 by ring, imb]
  have h1 : (2 * m + 4) % 2 = 0 := by omega
  have h2 : (2 * m + 4) / 2 = m + 2 := by omega
  simp [h1, h2]

theorem imb_odd (k : ℕ) (hk : 2 ≤ k) : imb (2 * k + 1) = k + 2 * imb k + imb (k + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  rw [show 2 * (m + 2) + 1 = (2 * m + 1) + 4 by ring, imb]
  have h1 : ¬ (2 * m + 1 + 4) % 2 = 0 := by omega
  have h2 : (2 * m + 1 + 4) / 2 = m + 2 := by omega
  simp [h1, h2]

theorem u_eq_add_imb (n : ℕ) : u n = n + imb n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 4 with hn | hn
    · interval_cases n <;> simp [imb]
    rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
    · rw [u_even k (by omega), imb_even k (by omega), ih k (by omega)]; ring
    · rw [u_odd k (by omega), imb_odd k (by omega), ih k (by omega), ih (k + 1) (by omega)]; ring

/-! ## 4. Pure halving variant `v` (3 is not a leaf: v 3 = 4) -/

def v : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | n + 3 =>
    if (n + 3) % 2 = 0 then 2 * v ((n + 3) / 2)
    else 2 * v ((n + 3) / 2) + v ((n + 3) / 2 + 1)
  decreasing_by all_goals omega

@[simp] theorem v0 : v 0 = 0 := by simp [v]
@[simp] theorem v1 : v 1 = 1 := by simp [v]
@[simp] theorem v2 : v 2 = 2 := by simp [v]

theorem v_even (k : ℕ) (hk : 1 ≤ k) : v (2 * k) = 2 * v k := by
  rcases Nat.lt_or_ge k 2 with h | h
  · obtain rfl : k = 1 := by omega
    simp
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
    rw [show 2 * (m + 2) = (2 * m + 1) + 3 by ring, v]
    have h1 : (2 * m + 1 + 3) % 2 = 0 := by omega
    have h2 : (2 * m + 1 + 3) / 2 = m + 2 := by omega
    simp [h1, h2]

theorem v_odd (k : ℕ) (hk : 1 ≤ k) : v (2 * k + 1) = 2 * v k + v (k + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [show 2 * (m + 1) + 1 = 2 * m + 3 by ring, v]
  have h1 : ¬ (2 * m + 3) % 2 = 0 := by omega
  have h2 : (2 * m + 3) / 2 = m + 1 := by omega
  simp [h2]

@[simp] theorem v3 : v 3 = 4 := by rw [show 3 = 2 * 1 + 1 by rfl, v_odd 1 le_rfl]; simp

theorem v_pow (a : ℕ) : v (2 ^ a) = 2 ^ a := by
  induction a with
  | zero => simp
  | succ a ih => rw [pow_succ, mul_comm, v_even _ (Nat.one_le_two_pow), ih]

theorem v_ge (m : ℕ) : m ≤ v m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp
      · rw [v_even k hk]; have := ih k (by omega); omega
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp
      · rw [v_odd k hk]; have := ih k (by omega); have := ih (k + 1) (by omega); omega

theorem v_odd_ge (k : ℕ) (hk : 1 ≤ k) : 3 * k + 1 ≤ v (2 * k + 1) := by
  rw [v_odd k hk]; have := v_ge k; have := v_ge (k + 1); omega

theorem v_fixed_iff (n : ℕ) : v n = n ↔ n = 0 ∨ ∃ a, n = 2 ^ a := by
  constructor
  · induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
      · rcases Nat.eq_zero_or_pos k with rfl | hk
        · simp
        · rw [v_even k hk] at hn
          rcases ih k (by omega) (by omega) with rfl | ⟨a, rfl⟩
          · omega
          · exact Or.inr ⟨a + 1, by ring⟩
      · rcases Nat.eq_zero_or_pos k with rfl | hk
        · exact Or.inr ⟨0, rfl⟩
        · have := v_odd_ge k hk; omega
  · rintro (rfl | ⟨a, rfl⟩)
    · simp
    · exact v_pow a

/-- No two consecutive fixed points of `v` beyond `1, 2`. -/
theorem two_fixed (k : ℕ) (hk : 2 ≤ k) (h1 : v k = k) (h2 : v (k + 1) = k + 1) : False := by
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · have := v_odd_ge j (by omega); omega
  · have := v_odd_ge j (by omega); omega

/-- Trichotomy: `v m = m`, or `3 v m = 4 m`, or `5 v m ≥ 8 m`. -/
theorem v_tri (m : ℕ) : v m = m ∨ 3 * v m = 4 * m ∨ 8 * m ≤ 5 * v m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp
      · rw [v_even k hk]; rcases ih k (by omega) with h | h | h <;> omega
    · rcases Nat.lt_or_ge k 2 with hk | hk
      · interval_cases k <;> simp
      · right; right
        rw [v_odd k (by omega)]
        have := v_ge k; have := v_ge (k + 1)
        rcases ih k (by omega) with h | h | h <;> rcases ih (k + 1) (by omega) with h' | h' | h'
        all_goals first | omega | exact (two_fixed k hk h h').elim

theorem v_ne_two_mul (n : ℕ) (hn : 1 ≤ n) : v n ≠ 2 * n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
    · rw [v_even k (by omega)]; have := ih k (by omega) (by omega); omega
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp
      · rw [v_odd k hk]
        intro heq
        rcases v_tri k with h | h | h
        · exact ih (k + 1) (by omega) (by omega) (by omega)
        all_goals
          rcases v_tri (k + 1) with h' | h' | h'
          · rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
            · have := v_odd_ge j (by omega); omega
            · rcases Nat.eq_zero_or_pos j with rfl | hj
              · simp at h
              · rw [v_odd j hj] at h heq
                have hc : v (2 * j + 1 + 1) = 2 * v (j + 1) := by
                  rw [show 2 * j + 1 + 1 = 2 * (j + 1) by ring, v_even _ (by omega)]
                omega
          all_goals omega

theorem v_pow_add_one (a : ℕ) (ha : 1 ≤ a) : v (2 ^ a + 1) = 2 ^ (a + 1) := by
  induction a, ha using Nat.le_induction with
  | base => simp
  | succ a ha ih =>
    rw [show 2 ^ (a + 1) + 1 = 2 * 2 ^ a + 1 by ring, v_odd _ Nat.one_le_two_pow, v_pow, ih]
    ring

theorem v7 : v 7 = 12 := by
  rw [show 7 = 2 * 3 + 1 by rfl, v_odd 3 (by norm_num), show 3 + 1 = 2 * 2 by rfl,
    v_even 2 (by norm_num)]; simp

def vStrand (n : ℕ) : Prop := n = 1 ∨ n = 7 ∨ ∃ a, 1 ≤ a ∧ n = 2 ^ a + 1

/-- Odd `n`: `v n < 2n` iff `n ∈ {1, 7}` or `n = 2^a + 1` (a ≥ 1). -/
theorem v_below_iff (n : ℕ) (hn : Odd n) : v n < 2 * n ↔ vStrand n := by
  obtain ⟨k, rfl⟩ := hn
  constructor
  · intro hlt
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · left; rfl
    rw [v_odd k hk] at hlt
    rcases v_tri k with h | h | h
    · rcases (v_fixed_iff k).1 h with h0 | ⟨a, rfl⟩
      · omega
      · exact Or.inr (Or.inr ⟨a + 1, by omega, by ring⟩)
    all_goals
      rcases v_tri (k + 1) with h' | h' | h'
      · rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
        · have := v_odd_ge j (by omega); omega
        · rcases Nat.eq_zero_or_pos j with rfl | hj
          · simp at h
          · rw [v_odd j hj] at h hlt
            have hc : v (2 * j + 1 + 1) = 2 * v (j + 1) := by
              rw [show 2 * j + 1 + 1 = 2 * (j + 1) by ring, v_even _ (by omega)]
            have hj1 : v (j + 1) = j + 1 := by omega
            have hjj : v j = j := by have := v_ge j; omega
            rcases Nat.lt_or_ge j 2 with hj2 | hj2
            · obtain rfl : j = 1 := by omega
              exact Or.inr (Or.inl rfl)
            · exact (two_fixed j hj2 hjj hj1).elim
      all_goals omega
  · rintro (h | h | ⟨a, ha, h⟩)
    · rw [h]; simp
    · rw [h, v7]; norm_num
    · rw [h, v_pow_add_one a ha]
      have : 2 ^ (a + 1) = 2 * 2 ^ a := by ring
      omega

/-! ## 5. Shared wings: halving wing = thirding wing only at n ∈ {2, 3, 5} -/

def thirdWing (n : ℕ) : ℕ := if n % 3 = 2 then n / 3 + 1 else n / 3

theorem shared_wings (n : ℕ) (hn : 2 ≤ n) : n / 2 = thirdWing n ↔ n = 2 ∨ n = 3 ∨ n = 5 := by
  unfold thirdWing; split_ifs <;> omega

end TwoMirrors

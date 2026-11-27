import Mathlib

/-!
# Many turns (tUrUq, 11-26-2026)

Same builds as lean-turn-roots: a build is its turn set `T` (odd t ≥ 3, u t = t), halving
elsewhere: u 1 = 1, u 2 = 2, u (2k) = 2 u k, u (2k+1) = 2 u k + u (k+1).
Definitions and the turn-roots lemmas are copied from TurnRoots.lean (namespace ManyTurns).

New, proven for every turn set T (no sorry, no native_decide):
* `three_quarter` : m not self-count ⇒ 4m ≤ 3 u m.
* `no_sporadic`   : odd non-turn n = 2k+1 with neither k nor k+1 self-count sits above the line.
* `line_never`    : u n ≠ 2n for every n ≥ 1 (the line u = 2n is untouched in every build).
* `below_classify`: every odd non-turn n below the line is strand, pair point or near-turn
                    (below_cases without its side hypothesis).
* `strand_deficit`: k self-count ⇒ 2n - u n at n = 2k+1 equals 2(k+1) - u(k+1).
-/

namespace ManyTurns
variable (T : ℕ → Bool)

def u : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | n + 3 =>
    if T (n + 3) then n + 3
    else if (n + 3) % 2 = 0 then 2 * u ((n + 3) / 2)
    else 2 * u ((n + 3) / 2) + u ((n + 3) / 2 + 1)
  decreasing_by all_goals omega

variable {T}

@[simp] theorem u0 : u T 0 = 0 := by simp [u]
@[simp] theorem u1 : u T 1 = 1 := by simp [u]
@[simp] theorem u2 : u T 2 = 2 := by simp [u]

theorem u_turn (t : ℕ) (ht3 : 3 ≤ t) (ht : T t = true) : u T t = t := by
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 3 := ⟨t - 3, by omega⟩
  rw [u]; simp [ht]

/-- Turns are odd. -/
def OddTurns (T : ℕ → Bool) : Prop := ∀ t, T t = true → t % 2 = 1 ∧ 3 ≤ t

theorem u_even (hT : OddTurns T) (k : ℕ) (hk : 1 ≤ k) : u T (2 * k) = 2 * u T k := by
  rcases Nat.lt_or_ge k 2 with h | h
  · obtain rfl : k = 1 := by omega
    simp
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
    have e : 2 * (m + 2) = (2 * m + 1) + 3 := by ring
    have hn : T (2 * m + 1 + 3) = false := by
      cases h' : T (2 * m + 1 + 3)
      · rfl
      · have := (hT _ h').1; omega
    rw [e, u]
    have h1 : (2 * m + 1 + 3) % 2 = 0 := by omega
    have h2 : (2 * m + 1 + 3) / 2 = m + 2 := by omega
    simp [hn, h1, h2]

theorem u_odd (k : ℕ) (hk : 1 ≤ k) (hn : T (2 * k + 1) = false) :
    u T (2 * k + 1) = 2 * u T k + u T (k + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have e : 2 * (m + 1) + 1 = 2 * m + 3 := by ring
  rw [e] at hn ⊢
  rw [u]
  have h1 : ¬ (2 * m + 3) % 2 = 0 := by omega
  have h2 : (2 * m + 3) / 2 = m + 1 := by omega
  simp [hn, h1, h2]

theorem u_ge (hT : OddTurns T) (m : ℕ) : m ≤ u T m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp
      · rw [u_even hT k hk]; have := ih k (by omega); omega
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp
      · cases h : T (2 * k + 1)
        · rw [u_odd k hk h]; have := ih k (by omega); have := ih (k + 1) (by omega); omega
        · rw [u_turn _ (by omega) h]

/-- An odd self-count point is 1 or a turn. -/
theorem odd_fixed (hT : OddTurns T) (k : ℕ) (h : u T (2 * k + 1) = 2 * k + 1) :
    k = 0 ∨ T (2 * k + 1) = true := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · left; rfl
  · cases hn : T (2 * k + 1)
    · rw [u_odd k hk hn] at h; have := u_ge hT k; have := u_ge hT (k + 1); omega
    · right; rfl

/-- Pair point: two neighbouring self-count points j, j+1 give 4j+3 two units short of 2n. -/
theorem pair_point (hT : OddTurns T) (j : ℕ) (hj : 1 ≤ j) (h0 : u T j = j)
    (h1 : u T (j + 1) = j + 1) (n1 : T (2 * j + 1) = false) (n2 : T (4 * j + 3) = false) :
    u T (4 * j + 3) + 2 = 2 * (4 * j + 3) := by
  have e : 4 * j + 3 = 2 * (2 * j + 1) + 1 := by ring
  rw [e, u_odd _ (by omega) (by rw [← e]; exact n2), u_odd j hj n1,
    show 2 * j + 1 + 1 = 2 * (j + 1) by ring, u_even hT _ (by omega), h0, h1]
  omega

/-- Strand law: on a self-count point k, 2k+1 sits below the line exactly when k+1 does. -/
theorem strand_iff (k : ℕ) (hk : 1 ≤ k) (h0 : u T k = k) (hn : T (2 * k + 1) = false) :
    u T (2 * k + 1) < 2 * (2 * k + 1) ↔ u T (k + 1) < 2 * (k + 1) := by
  rw [u_odd k hk hn, h0]; omega

theorem below_cases (hT : OddTurns T) (k : ℕ) (hk : 1 ≤ k) (hn : T (2 * k + 1) = false)
    (hb : u T (2 * k + 1) < 2 * (2 * k + 1)) (hf : u T k = k ∨ u T (k + 1) = k + 1) :
    (u T k = k ∧ u T (k + 1) < 2 * (k + 1)) ∨
    (∃ j, 1 ≤ j ∧ k = 2 * j + 1 ∧ u T j = j ∧ u T (j + 1) = j + 1) ∨
    (T (k + 1) = true ∧ 2 * u T k + 2 < 3 * (k + 1)) := by
  have hu := u_odd k hk hn
  by_cases h0 : u T k = k
  · left; exact ⟨h0, by omega⟩
  have h1 : u T (k + 1) = k + 1 := by tauto
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · -- k + 1 odd self-count: a turn
    rcases odd_fixed hT j h1 with rfl | ht
    · omega
    · right; right; exact ⟨ht, by omega⟩
  · -- k = 2j+1 odd, not self-count, so not a turn
    have hj : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with rfl | h
      · exfalso; simp_all
      · exact h
    have nk : T (2 * j + 1) = false := by
      cases h' : T (2 * j + 1)
      · rfl
      · exact absurd (u_turn _ (by omega) h') h0
    have e : 2 * j + 1 + 1 = 2 * (j + 1) := by ring
    rw [e, u_even hT _ (by omega)] at h1
    rw [u_odd j hj nk, e, u_even hT _ (by omega)] at hu
    have hj1 : u T (j + 1) = j + 1 := by omega
    have := u_ge hT j
    right; left; exact ⟨j, hj, rfl, by omega, hj1⟩

theorem three_quarter (hT : OddTurns T) (m : ℕ) (hm : 1 ≤ m) (h : u T m ≠ m) :
    4 * m ≤ 3 * u T m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
    · have hk : 1 ≤ k := by omega
      rw [u_even hT k hk] at h ⊢
      have hk' : u T k ≠ k := by intro e; apply h; rw [e]
      have := ih k (by omega) hk hk'
      omega
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp at h
      · cases hn : T (2 * k + 1)
        · rw [u_odd k hk hn]; have := u_ge hT k; have := u_ge hT (k + 1); omega
        · exact absurd (u_turn _ (by omega) hn) h

theorem no_sporadic (hT : OddTurns T) (k : ℕ) (hk : 1 ≤ k) (hn : T (2 * k + 1) = false)
    (h0 : u T k ≠ k) (h1 : u T (k + 1) ≠ k + 1) : 2 * (2 * k + 1) < u T (2 * k + 1) := by
  rw [u_odd k hk hn]
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · have hj : 1 ≤ j := by omega
    rw [u_even hT j hj] at h0 ⊢
    have hj' : u T j ≠ j := by intro e; apply h0; rw [e]
    have n1 : T (2 * j + 1) = false := by
      cases h' : T (2 * j + 1)
      · rfl
      · exact absurd (u_turn _ (by omega) h') h1
    rw [u_odd j hj n1]
    have := three_quarter hT j hj hj'
    have := u_ge hT (j + 1)
    have : j ≠ 1 := by rintro rfl; simp at hj'
    omega
  · have hj : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with rfl | h
      · simp at h0
      · exact h
    have n1 : T (2 * j + 1) = false := by
      cases h' : T (2 * j + 1)
      · rfl
      · exact absurd (u_turn _ (by omega) h') h0
    have e : 2 * j + 1 + 1 = 2 * (j + 1) := by ring
    rw [e, u_even hT _ (by omega)] at h1 ⊢
    rw [u_odd j hj n1]
    have := u_ge hT j
    have := u_ge hT (j + 1)
    have : u T (j + 1) ≠ j + 1 := by intro x; apply h1; omega
    omega

theorem line_never (hT : OddTurns T) (n : ℕ) (hn : 1 ≤ n) : u T n ≠ 2 * n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
    · have hk : 1 ≤ k := by omega
      rw [u_even hT k hk]; have := ih k (by omega) hk; omega
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp
      cases hn' : T (2 * k + 1)
      swap
      · rw [u_turn _ (by omega) hn']; omega
      by_cases h0 : u T k = k
      · rw [u_odd k hk hn', h0]; have := ih (k + 1) (by omega) (by omega); omega
      by_cases h1 : u T (k + 1) = k + 1
      · rw [u_odd k hk hn', h1]
        rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
        · rw [u_even hT j (by omega)]; omega
        · have hj : 1 ≤ j := by
            rcases Nat.eq_zero_or_pos j with rfl | h
            · simp at h0
            · exact h
          have n1 : T (2 * j + 1) = false := by
            cases h' : T (2 * j + 1)
            · rfl
            · exact absurd (u_turn _ (by omega) h') h0
          have e : 2 * j + 1 + 1 = 2 * (j + 1) := by ring
          rw [e, u_even hT _ (by omega)] at h1
          rw [u_odd j hj n1]
          omega
      · have := no_sporadic hT k hk hn' h0 h1; omega

theorem below_classify (hT : OddTurns T) (k : ℕ) (hk : 1 ≤ k) (hn : T (2 * k + 1) = false)
    (hb : u T (2 * k + 1) < 2 * (2 * k + 1)) :
    (u T k = k ∧ u T (k + 1) < 2 * (k + 1)) ∨
    (∃ j, 1 ≤ j ∧ k = 2 * j + 1 ∧ u T j = j ∧ u T (j + 1) = j + 1) ∨
    (T (k + 1) = true ∧ 2 * u T k + 2 < 3 * (k + 1)) := by
  apply below_cases hT k hk hn hb
  by_cases a : u T k = k
  · exact Or.inl a
  by_cases b : u T (k + 1) = k + 1
  · exact Or.inr b
  have := no_sporadic hT k hk hn a b
  omega

theorem strand_deficit (k : ℕ) (hk : 1 ≤ k) (h0 : u T k = k) (hn : T (2 * k + 1) = false) :
    u T (2 * k + 1) + 2 * (k + 1) = 2 * (2 * k + 1) + u T (k + 1) := by
  rw [u_odd k hk hn, h0]; ring

#print axioms line_never
#print axioms below_classify

end ManyTurns

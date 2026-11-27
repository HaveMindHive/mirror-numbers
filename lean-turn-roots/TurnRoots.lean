import Mathlib

/-!
# Turn roots of the halving build (tUrUq, 11-26-2026)

A build is fixed by its set of turns `T` (odd numbers t ≥ 3 written as t equal unit copies,
so u t = t). Everything else uses halving:
u 0 = 0, u 1 = 1, u 2 = 2, u t = t for a turn t, u (2k) = 2 u k, u (2k+1) = 2 u k + u (k+1).
T = {3}: the halving build with the 3-turn root. T = ∅: pure halving. T = {5}, {7}, ...

Proven for every turn set (no sorry, no native_decide):
* `u_ge`        : m ≤ u m.
* `odd_fixed`   : an odd self-count point is 1 or a turn.
* `pair_point`  : j, j+1 self-count (j ≥ 1), 2j+1 and 4j+3 not turns ⇒ u (4j+3) = 2(4j+3) - 2.
* `strand_iff`  : k self-count ⇒ (u (2k+1) < 2(2k+1) ↔ u (k+1) < 2(k+1)).
* `below_cases` : odd n = 2k+1 below the line, not a turn, with k or k+1 self-count ⇒
                  strand (k self-count, k+1 below), pair point (k = 2j+1, j and j+1 self-count),
                  or near-turn (k+1 a turn t with 2 u (t-1) < 3t - 2).
-/

namespace TurnRoots

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

/-- The 3-turn build reproduces 11 and 15 as pair points; the 5-turn build gives 19; the
7-turn build gives 31; pure halving gives 7. -/
def t3 : ℕ → Bool := fun n => n = 3
def t5 : ℕ → Bool := fun n => n = 5
def t7 : ℕ → Bool := fun n => n = 7
def t0 : ℕ → Bool := fun _ => false

theorem ot3 : OddTurns t3 := by intro t h; simp [t3] at h; omega
theorem ot5 : OddTurns t5 := by intro t h; simp [t5] at h; omega
theorem ot7 : OddTurns t7 := by intro t h; simp [t7] at h; omega
theorem ot0 : OddTurns t0 := by intro t h; simp [t0] at h

theorem pow_fixed (hT : OddTurns T) (a : ℕ) : u T (2 ^ a) = 2 ^ a := by
  induction a with
  | zero => simp
  | succ a ih => rw [pow_succ, mul_comm, u_even hT _ (Nat.one_le_two_pow), ih]

theorem eleven : u t3 11 + 2 = 22 := by
  have := pair_point ot3 2 (by norm_num) (by simpa using pow_fixed ot3 1)
    (u_turn 3 le_rfl (by simp [t3])) (by simp [t3]) (by simp [t3]); simpa using this
theorem fifteen : u t3 15 + 2 = 30 := by
  have := pair_point ot3 3 (by norm_num) (u_turn 3 le_rfl (by simp [t3]))
    (by simpa using pow_fixed ot3 2) (by simp [t3]) (by simp [t3]); simpa using this
theorem nineteen : u t5 19 + 2 = 38 := by
  have := pair_point ot5 4 (by norm_num) (by simpa using pow_fixed ot5 2)
    (u_turn 5 (by norm_num) (by simp [t5])) (by simp [t5]) (by simp [t5]); simpa using this
theorem thirtyone : u t7 31 + 2 = 62 := by
  have := pair_point ot7 7 (by norm_num) (u_turn 7 (by norm_num) (by simp [t7]))
    (by simpa using pow_fixed ot7 3) (by simp [t7]) (by simp [t7]); simpa using this
theorem seven : u t0 7 + 2 = 14 := by
  have := pair_point ot0 1 le_rfl (by simp) (by simp) (by simp [t0]) (by simp [t0])
  simpa using this

end TurnRoots

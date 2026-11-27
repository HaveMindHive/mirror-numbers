import Mathlib
import MirrorNumbersAll.TheSolve
import MirrorNumbersAll.Gems

/-!
# One formula for the primes, in wall coordinates (tUrUq, 11-27-2026)

A seat beside a wall is n = 6k + f with f = +-1. Every block is itself a seat r = 6j + g (j >= 1,
g = +-1), named by its own wall j and wing g; no list of primes is needed. The wall law for any block
prime to 6 (`TheSolve.wing_closed`) gives one closed test:

* `wall_formula` : a seat n = 6k + f (n >= 5) is prime exactly when no block 6j + g with
  (6j + g)^2 <= n divides k - f g j.

So the prime test is one formula in k and f alone, and the count of primes up to N is 2 plus the
number of seats that pass it. No sorry, no admit, no native_decide.
-/

namespace WallFormula

/-- A seat r = 6j + g (g = +-1) is prime to 6: (6j + 1) - 6j = 1 and -(6j - 1) + 6j = 1. -/
theorem seat_coprime (j g : ℤ) (hg : g = 1 ∨ g = -1) : IsCoprime (6 * j + g) 6 := by
  rcases hg with rfl | rfl
  · exact ⟨1, -j, by ring⟩
  · exact ⟨-1, j, by ring⟩

/-- ONE FORMULA FOR THE PRIMES: a seat n = 6k + f (f = +-1, n >= 5) is prime exactly when no block
6j + g (j >= 1, g = +-1) with (6j + g)^2 <= n divides k - f g j. -/
theorem wall_formula (k f : ℤ) (hf : f = 1 ∨ f = -1) (n : ℕ) (hn : (n : ℤ) = 6 * k + f) (h5 : 5 ≤ n) :
    n.Prime ↔ ∀ j g : ℤ, 1 ≤ j → (g = 1 ∨ g = -1) → (6 * j + g) * (6 * j + g) ≤ n →
      ¬ (6 * j + g) ∣ k - f * g * j := by
  constructor
  · intro hp j g hj hg hsq hd
    have hgg : g * g = 1 := by rcases hg with rfl | rfl <;> norm_num
    have h1 : (6 * j + g) ∣ (n : ℤ) := by
      rw [hn]; exact (TheSolve.wing_closed k j f g hgg (seat_coprime j g hg)).2 hd
    have hpos : 5 ≤ 6 * j + g := by rcases hg with rfl | rfl <;> omega
    obtain ⟨t, ht⟩ : ∃ t : ℕ, (t : ℤ) = 6 * j + g := ⟨(6 * j + g).toNat, Int.toNat_of_nonneg (by omega)⟩
    rw [← ht] at h1 hsq hpos
    have h2 : t ∣ n := Int.natCast_dvd_natCast.1 h1
    have hsq' : t * t ≤ n := by exact_mod_cast hsq
    rcases (Nat.dvd_prime hp).1 h2 with h | h
    · omega
    · subst h; have : 5 ≤ t := by exact_mod_cast hpos
      nlinarith
  · intro hall
    by_contra hnp
    have hn0 : 0 < n := by omega
    set m := n.minFac with hm
    have hmp : m.Prime := Nat.minFac_prime (by omega)
    have hmd : m ∣ n := Nat.minFac_dvd n
    have hsq : m ^ 2 ≤ n := Nat.minFac_sq_le_self hn0 hnp
    have hn6 : n % 6 = 1 ∨ n % 6 = 5 := by omega
    have hm2 : m ≠ 2 := by intro h; rw [h] at hmd; omega
    have hm3 : m ≠ 3 := by intro h; rw [h] at hmd; omega
    have hm5 : 5 ≤ m := by
      have := hmp.two_le
      rcases (show m = 2 ∨ m = 3 ∨ m = 4 ∨ 5 ≤ m by omega) with h | h | h | h
      · exact absurd h hm2
      · exact absurd h hm3
      · rw [h] at hmp; exact absurd hmp (by decide)
      · exact h
    have hseat := Gems.prime_seat m hmp hm5
    set j : ℤ := ((m : ℤ) + 1) / 6 with hj
    set g : ℤ := (m : ℤ) - 6 * j with hgdef
    have hg : g = 1 ∨ g = -1 := by rcases hseat with h | h <;> omega
    have hgg : g * g = 1 := by rcases hg with h | h <;> rw [h] <;> norm_num
    have hme : (m : ℤ) = 6 * j + g := by omega
    have hj1 : 1 ≤ j := by omega
    have hdz : (6 * j + g) ∣ 6 * k + f := by
      rw [← hme, ← hn]; exact Int.natCast_dvd_natCast.2 hmd
    have hd := (TheSolve.wing_closed k j f g hgg (seat_coprime j g hg)).1 hdz
    refine hall j g hj1 hg ?_ hd
    rw [← hme]; exact_mod_cast (by nlinarith : m * m ≤ n)

/-- The n-th prime (counting from p_0 = 2) is a count: for any bound B >= p_n, p_n + 1 is the number of
a <= B with at most n primes below a. -/
theorem nth_prime_count (n B : ℕ) (hB : Nat.nth Nat.Prime n ≤ B) :
    Nat.nth Nat.Prime n + 1 = ((Finset.range (B + 1)).filter (fun a => Nat.count Nat.Prime a ≤ n)).card := by
  have hinf : (Set.ofPred Nat.Prime).Infinite := Nat.infinite_setOfPred_prime
  have : (Finset.range (B + 1)).filter (fun a => Nat.count Nat.Prime a ≤ n) = Finset.range (Nat.nth Nat.Prime n + 1) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range, Nat.count_le_iff_le_nth hinf]
    omega
  rw [this, Finset.card_range]

/-- The next prime is at most twice the last (from Bertrand's postulate in Mathlib). -/
theorem nth_prime_succ_le (n : ℕ) : Nat.nth Nat.Prime (n + 1) ≤ 2 * Nat.nth Nat.Prime n := by
  have hinf : (Set.ofPred Nat.Prime).Infinite := Nat.infinite_setOfPred_prime
  have h0 : Nat.nth Nat.Prime n ≠ 0 := (Nat.prime_nth_prime n).ne_zero
  obtain ⟨q, hq, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul _ h0
  have hc : n < Nat.count Nat.Prime q := (Nat.lt_nth_iff_count_lt hinf).2 hlt
  calc Nat.nth Nat.Prime (n + 1) ≤ Nat.nth Nat.Prime (Nat.count Nat.Prime q) := Nat.nth_monotone hinf hc
    _ = q := Nat.nth_count hq
    _ ≤ 2 * Nat.nth Nat.Prime n := hle

/-- p_n <= 2^(n+1). -/
theorem nth_prime_le_pow (n : ℕ) : Nat.nth Nat.Prime n ≤ 2 ^ (n + 1) := by
  induction n with
  | zero => simp [Nat.nth_prime_zero_eq_two]
  | succ k ih => calc Nat.nth Nat.Prime (k + 1) ≤ 2 * Nat.nth Nat.Prime k := nth_prime_succ_le k
      _ ≤ 2 * 2 ^ (k + 1) := by omega
      _ = 2 ^ (k + 1 + 1) := by ring

/-- ONE FORMULA FOR THE n-TH PRIME: p_n + 1 = #{a <= 2^(n+1) : at most n primes below a}, and the primes
below a are 2, 3 and the seats that pass `wall_formula`. -/
theorem nth_prime_formula (n : ℕ) :
    Nat.nth Nat.Prime n + 1 =
      ((Finset.range (2 ^ (n + 1) + 1)).filter (fun a => Nat.count Nat.Prime a ≤ n)).card :=
  nth_prime_count n _ (nth_prime_le_pow n)

end WallFormula

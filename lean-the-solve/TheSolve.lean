import Mathlib

/-!
# The solve, in the wall frame (Turaq Rayn-McLean's mirror method, 11-26-2026)

With 2 as the zero, 0 halves into -1, 0, 1, and the stacked zero of 2 and 3 is the wall 6k.
Every prime past 3 is a wing of a wall: p = 6k + f with f = 1 or -1 (his two families).
The new exact relationship this frame opens (wing_closed): a block r = 6 kr + fr, itself a wing of the
wall kr, closes the wing f of the wall k exactly when k = f * fr * kr (mod r): the block's OWN wall index,
signed by the product of the two facings. Same facing -> +kr, opposite facing -> -kr. One residue of the
wall index k reads both wings at once (wall_reads_both_wings). The two families are one strand read through
zero (family_through_zero, family_count_mirror). The step of 2 lands on 3's zero on one side per family
(two_step_minus, two_step_plus). No sorry, no native_decide.
-/

namespace TheSolve

/-- The key identity: 6k + f = 6 (k - f fr kr) + f fr (6 kr + fr) when fr^2 = 1. -/
theorem wing_identity (k kr f fr : ℤ) (hfr : fr * fr = 1) :
    6 * k + f = 6 * (k - f * fr * kr) + f * fr * (6 * kr + fr) := by
  linear_combination (-f) * hfr

/-- A block r = 6 kr + fr off 2 and 3 closes the wing f of the wall k exactly when the wall index k sits
    at f * fr * kr (mod r). -/
theorem wing_closed (k kr f fr : ℤ) (hfr : fr * fr = 1) (hc : IsCoprime (6 * kr + fr) 6) :
    (6 * kr + fr) ∣ (6 * k + f) ↔ (6 * kr + fr) ∣ (k - f * fr * kr) := by
  have key := wing_identity k kr f fr hfr
  constructor
  · intro h
    have h1 : (6 * kr + fr) ∣ f * fr * (6 * kr + fr) := dvd_mul_left _ _
    have h2 : (6 * kr + fr) ∣ (6 * k + f) - f * fr * (6 * kr + fr) := dvd_sub h h1
    have h3 : (6 * kr + fr) ∣ (k - f * fr * kr) * 6 := by
      have : (6 * k + f) - f * fr * (6 * kr + fr) = (k - f * fr * kr) * 6 := by rw [key]; ring
      rw [this] at h2; exact h2
    exact hc.dvd_of_dvd_mul_right h3
  · intro h
    rw [key]
    exact dvd_add (dvd_mul_of_dvd_right h 6) (dvd_mul_left _ _)

/-- The two wings of one wall are closed at mirror classes: f = +1 at k = fr kr, f = -1 at k = -fr kr. -/
theorem wings_mirror (k kr fr : ℤ) (hfr : fr * fr = 1) (hc : IsCoprime (6 * kr + fr) 6) :
    ((6 * kr + fr) ∣ (6 * k + 1) ↔ (6 * kr + fr) ∣ (k - fr * kr)) ∧
    ((6 * kr + fr) ∣ (6 * k - 1) ↔ (6 * kr + fr) ∣ (k + fr * kr)) := by
  constructor
  · have := wing_closed k kr 1 fr hfr hc
    simpa using this
  · have := wing_closed k kr (-1) fr hfr hc
    have e1 : 6 * k + (-1 : ℤ) = 6 * k - 1 := by ring
    have e2 : k - (-1) * fr * kr = k + fr * kr := by ring
    rw [e1, e2] at this
    exact this

/-- One residue of the wall index reads both wings: both wings of wall k stay open under the block r
    exactly when k avoids both mirror classes +-fr kr (mod r). -/
theorem wall_reads_both_wings (k kr fr : ℤ) (hfr : fr * fr = 1) (hc : IsCoprime (6 * kr + fr) 6) :
    (¬ (6 * kr + fr) ∣ (6 * k + 1) ∧ ¬ (6 * kr + fr) ∣ (6 * k - 1)) ↔
    (¬ (6 * kr + fr) ∣ (k - fr * kr) ∧ ¬ (6 * kr + fr) ∣ (k + fr * kr)) := by
  have h := wings_mirror k kr fr hfr hc
  rw [h.1, h.2]

/-- A prime off 2 and 3 is coprime to 6 (the hypothesis of wing_closed holds for every block r >= 5). -/
theorem prime_coprime_six (r : ℕ) (hr : r.Prime) (h2 : r ≠ 2) (h3 : r ≠ 3) : IsCoprime (r : ℤ) 6 := by
  have hc : Nat.Coprime r 6 := by
    rw [Nat.Prime.coprime_iff_not_dvd hr]
    intro h
    have h6 : (6 : ℕ) = 2 * 3 := by norm_num
    rw [h6] at h
    rcases (Nat.Prime.dvd_mul hr).1 h with h | h
    · exact h2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h)
    · exact h3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 h)
  have := Nat.isCoprime_iff_coprime.2 hc
  exact_mod_cast this

/-- The block 5 = 6 * 1 - 1 closes the wing -1 at k = 1 (mod 5) and the wing +1 at k = -1 = 4 (mod 5). -/
theorem five_closes (k : ℤ) : ((5 : ℤ) ∣ (6 * k - 1) ↔ (5 : ℤ) ∣ (k - 1)) ∧ ((5 : ℤ) ∣ (6 * k + 1) ↔ (5 : ℤ) ∣ (k + 1)) := by
  have hc : IsCoprime (6 * (1 : ℤ) + (-1)) 6 := by norm_num [Int.isCoprime_iff_gcd_eq_one]
  have h := wings_mirror k 1 (-1) (by norm_num) hc
  norm_num at h
  exact ⟨h.2, h.1⟩

/-- The block 7 = 6 * 1 + 1 closes the wing +1 at k = 1 (mod 7) and the wing -1 at k = -1 = 6 (mod 7). -/
theorem seven_closes (k : ℤ) : ((7 : ℤ) ∣ (6 * k + 1) ↔ (7 : ℤ) ∣ (k - 1)) ∧ ((7 : ℤ) ∣ (6 * k - 1) ↔ (7 : ℤ) ∣ (k + 1)) := by
  have hc : IsCoprime (6 * (1 : ℤ) + 1) 6 := by norm_num [Int.isCoprime_iff_gcd_eq_one]
  have h := wings_mirror k 1 1 (by norm_num) hc
  norm_num at h
  exact h

/-- The two families are one strand read through zero: the wing -1 of wall k is the wing +1 of wall -k, negated. -/
theorem family_through_zero (k : ℤ) : 6 * (-k) + 1 = -(6 * k - 1) := by ring

/-- Walking down through zero swaps the families seat for seat: n = 5 (mod 6) exactly when -n = 1 (mod 6). -/
theorem neg_swaps_family (n : ℕ) : n % 6 = 5 ↔ (-(n : ℤ)) % 6 = 1 := by
  omega

/-- So the 6k-1 primes up to x are exactly the primes whose negation sits in the 6k+1 class: equal count. -/
theorem family_count_mirror (x : ℕ) :
    ((Finset.Icc 1 x).filter (fun n : ℕ => n.Prime ∧ n % 6 = 5)).card =
    ((Finset.Icc 1 x).filter (fun n : ℕ => n.Prime ∧ (-(n : ℤ)) % 6 = 1)).card := by
  congr 1
  apply Finset.filter_congr
  intro n _
  rw [neg_swaps_family]

/-- Rule 9, proven: from a 6k-1 prime the step of 2 down lands on 3's zero; from 6k+1 the step up does. -/
theorem two_step_minus (k : ℤ) : (6 * k - 1) - 2 = 3 * (2 * k - 1) := by ring
theorem two_step_plus (k : ℤ) : (6 * k + 1) + 2 = 3 * (2 * k + 1) := by ring

/-- The hop in the wall frame: from wall k wing f to wall k' wing f', the half gap is 3 (k' - k) + (f' - f) / 2;
    with s = (f' - f)/2 in {-1, 0, 1} this is his h = 3w + 2s... written without division: 2h = 6w + (f' - f). -/
theorem hop_wall_frame (k k' f f' : ℤ) : (6 * k' + f') - (6 * k + f) = 6 * (k' - k) + (f' - f) := by ring

end TheSolve

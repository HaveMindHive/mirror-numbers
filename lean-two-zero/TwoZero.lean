import Mathlib

/-!
# Two as the zero (tUrUq's mirror method, 11-26-2026)

His words: "2 is like 0. its the only common prime"; "2 is the 0 of primes both odd and even".
In the unified code every number is w, c, w with centre c = 0 (hinge, even) or 1 (unit, odd).
0 halves into -1, 0, 1; 2 is 1, 0, 1: the same picture with the facings dropped (two_pictures).
2 is the one prime whose centre is the hinge (hinge_prime); every other prime reads the unit at its centre
(odd_prime_unit_centre): measured from 2's mirror, every odd prime is a 1.
Zeros stack: 2 with 3 at 6, with 3 and 5 at 30, with 3, 5, 7 at 210. Primes past the stack sit on the seats
coprime to the stack (stacked_six, stacked_thirty); twin primes above 3 sit as the +-1 pair around a
stacked zero of 2 and 3 (twin_straddles_wall). With 2 in the stack the mirror r <-> W - r keeps parity and
no open seat is its own mirror once a second block is in the stack (mirror_keeps_parity; the lone 2-zero's seat 1 faces itself); with 2 out (odd offset, his 11-line) it crosses parity
(odd_offset_crosses_parity). Near a stacked zero of 2, 3, 5, 7 the seats within half a turn are 1 and primes
(near_zero_seats_210); at 2310 that frays, 169 = 13 x 13 sits inside the half turn (fray_at_2310).
The stacked zero of 2 and an odd prime p is 2p, the even prime E1 (stack_two_p).
No sorry, no native_decide.
-/

namespace TwoZero

/-- 0 = -1, 0, 1 and 2 = 1, 0, 1 are one picture: the wings cancel as facings and count as units. -/
theorem two_pictures : ((-1 : ℤ) + 0 + 1 = 0) ∧ (|(-1 : ℤ)| + |(0 : ℤ)| + |(1 : ℤ)| = 2) := by
  constructor <;> norm_num

/-- 2 is the one prime whose centre is the hinge (even). -/
theorem hinge_prime (p : ℕ) (hp : p.Prime) (h : p % 2 = 0) : p = 2 := by
  rcases hp.eq_two_or_odd with h2 | h1
  · exact h2
  · omega

/-- Every other prime carries the unit at its centre: p = w, 1, w with w = p / 2. -/
theorem odd_prime_unit_centre (p : ℕ) (hp : p.Prime) (h : p ≠ 2) : p = 2 * (p / 2) + 1 := by
  rcases hp.eq_two_or_odd with h2 | h1
  · exact absurd h2 h
  · omega

/-- Measured from 2's mirror (mod 2) every odd prime reads 1. -/
theorem odd_prime_reads_one (p : ℕ) (hp : p.Prime) (h : p ≠ 2) : p % 2 = 1 := by
  have := odd_prime_unit_centre p hp h
  omega

/-- Past the stack of 2 and 3 a prime sits at +-1 around the stacked zeros 6k. -/
theorem stacked_six (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) : p % 6 = 1 ∨ p % 6 = 5 := by
  have h2 : p % 2 = 1 := odd_prime_reads_one p hp (by omega)
  have h3 : p % 3 ≠ 0 := by
    intro h
    have hd : 3 ∣ p := Nat.dvd_of_mod_eq_zero h
    rcases (Nat.dvd_prime hp).1 hd with h | h <;> omega
  omega

/-- Twin primes above 3 are the +-1 pair around a stacked zero of 2 and 3. -/
theorem twin_straddles_wall (p : ℕ) (hp : p.Prime) (hq : (p + 2).Prime) (h5 : 5 ≤ p) :
    (p + 1) % 6 = 0 := by
  rcases stacked_six p hp h5 with h | h
  · exfalso
    have hd : 3 ∣ p + 2 := Nat.dvd_of_mod_eq_zero (by omega)
    rcases (Nat.dvd_prime hq).1 hd with h' | h' <;> omega
  · omega

/-- Past the stack of 2, 3, 5 a prime sits on one of eight seats around the stacked zeros 30k,
    four mirror pairs r <-> 30 - r: (1,29), (7,23), (11,19), (13,17). -/
theorem stacked_thirty (p : ℕ) (hp : p.Prime) (h7 : 7 ≤ p) :
    p % 30 = 1 ∨ p % 30 = 7 ∨ p % 30 = 11 ∨ p % 30 = 13 ∨
    p % 30 = 17 ∨ p % 30 = 19 ∨ p % 30 = 23 ∨ p % 30 = 29 := by
  have h6 := stacked_six p hp (by omega)
  have h5 : p % 5 ≠ 0 := by
    intro h
    have hd : 5 ∣ p := Nat.dvd_of_mod_eq_zero h
    rcases (Nat.dvd_prime hp).1 hd with h | h <;> omega
  omega

/-- With 2 in the stack (W even) the mirror seat W - r of an odd seat r is odd and never r itself:
    every prime seat has a distinct partner of the same parity. -/
theorem mirror_keeps_parity (W r : ℕ) (hW : W % 2 = 0) (hW2 : 2 < W) (hlt : r < W) (hc : Nat.Coprime r W) :
    (W - r) % 2 = 1 ∧ W - r ≠ r := by
  have hr1 : r % 2 = 1 := by
    rcases Nat.even_or_odd r with h | h
    · exfalso
      have h2 : 2 ∣ Nat.gcd r W := Nat.dvd_gcd (even_iff_two_dvd.1 h) (Nat.dvd_of_mod_eq_zero hW)
      rw [hc.gcd_eq_one] at h2
      omega
    · exact Nat.odd_iff.1 h
  refine ⟨by omega, ?_⟩
  intro h
  have hdvd : r ∣ W := ⟨2, by omega⟩
  have h1 : r = 1 := by
    have := Nat.gcd_eq_left hdvd
    rw [hc.gcd_eq_one] at this
    omega
  omega

/-- With 2 out of the stack (W odd, his offset 11) the mirror crosses parity: odd seats land on evens. -/
theorem odd_offset_crosses_parity (W r : ℕ) (hW : W % 2 = 1) (hr : r % 2 = 1) (hlt : r < W) :
    (W - r) % 2 = 0 := by
  omega

/-- Within half a turn of the stacked zero 210 (= 2 x 3 x 5 x 7) every open seat is 1 or a prime. -/
theorem near_zero_seats_210 (r : ℕ) (hr : r ≤ 105) (hc : Nat.Coprime r 210) : r = 1 ∨ r.Prime := by
  interval_cases r <;> first | exact Or.inl rfl | (exfalso; unfold Nat.Coprime at hc; norm_num at hc; done) | (right; norm_num; done)

/-- At the next stack 2310 (= 2 x 3 x 5 x 7 x 11) this frays: 169 = 13 x 13 is an open seat inside the half turn. -/
theorem fray_at_2310 : Nat.Coprime 169 2310 ∧ ¬ Nat.Prime 169 ∧ 169 ≠ 1 ∧ 169 ≤ 1155 := by
  refine ⟨by unfold Nat.Coprime; norm_num, ?_, by norm_num, by norm_num⟩
  have : 169 = 13 * 13 := by norm_num
  rw [this]
  exact Nat.not_prime_mul (by norm_num) (by norm_num)

/-- The stacked zero of 2 and an odd prime p is 2p (the even prime E1): anything both halve is a multiple of 2p. -/
theorem stack_two_p (p m : ℕ) (hp : p.Prime) (h : p ≠ 2) (h2 : 2 ∣ m) (hpm : p ∣ m) : 2 * p ∣ m := by
  have hc : Nat.Coprime 2 p := (hp.odd_of_ne_two h).coprime_two_left
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hc h2 hpm

/-- The even prime E1 = 2p is the whole odd line one zoom up: its gaps are twice the odd gaps. -/
theorem e1_gap (p q : ℕ) (h : p ≤ q) : 2 * q - 2 * p = 2 * (q - p) := by
  omega

end TwoZero

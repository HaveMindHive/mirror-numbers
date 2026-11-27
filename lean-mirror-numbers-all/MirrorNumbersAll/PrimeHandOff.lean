import Mathlib
import MirrorNumbersAll.HandOff
import MirrorNumbersAll.TwoZero
import MirrorNumbersAll.TheSolve
import MirrorNumbersAll.RatioTwoLine
import MirrorNumbersAll.TwoMirrors

/-!
# The hand-off, the hop and the wall law read on primes; u(n) = 2(n-1) (tUrUq, 11-26-2026)

New module for the combined library. The seat theorems of HandOff, WallMirror and TheSolve are
stated for seats off 2 and 3; here they are read on primes past 3, which take those seats
(TwoZero.stacked_six), so the paper's statements about consecutive primes are proven as stated:

* `hand_off_primes`     : for primes 3 < p < q with q = p + 2h, the 2-mirror sits on exactly one of
  the centre p + h and the half gap h, and so does the 3-mirror.
* `centre_fixes_half_gap` : the four cases of the walker section (6 | m, odd multiple of 3, even
  prime to 3, prime to 6) read off the centre m = p + h.
* `never_both_primes`   : no block r >= 2 passes through both the centre and the half gap.
* `hop_primes`          : the hop in the wall frame, h = 3w + 2s with s in {-1, 0, 1}, w the walls
  crossed; the side mod 4 flips exactly when w is odd, the facing mod 3 exactly when s is not 0.
* `wall_law_prime`      : a prime block r = 6 kr + fr closes the wing f of wall k exactly when
  k = f fr kr (mod r).
* `two_eleven_fifteen`  : u(n) = 2(n - 1) exactly at n = 2, 11, 15 (from the ratio-two classification).
No sorry, no admit, no native_decide.
-/

namespace PrimeHandOff

/-- A prime past 3 is at least 5 (4 is not prime). -/
theorem five_le (p : ℕ) (hp : p.Prime) (h : 3 < p) : 5 ≤ p := by
  have h4 : p ≠ 4 := by rintro rfl; norm_num at hp
  omega

/-- A prime past 3 is off the 2-mirror and the 3-mirror. -/
theorem prime_off (p : ℕ) (hp : p.Prime) (h : 3 < p) : p % 2 = 1 ∧ p % 3 ≠ 0 := by
  have := TwoZero.stacked_six p hp (five_le p hp h)
  omega

/-- A split of primes p < q past 3 with half gap h (q = p + 2h) is an Off23 split. -/
theorem split_of_primes (p q h : ℕ) (hp : p.Prime) (hq : q.Prime) (h3 : 3 < p)
    (hh : q = p + 2 * h) : HandOff.Off23 p h := by
  have h1 := prime_off p hp h3
  have h2 := prime_off q hq (by omega)
  subst hh
  exact ⟨h1.1, h2.1, h1.2, h2.2⟩

/-- The gap between two primes past 2 is even: the half gap exists. -/
theorem half_gap_exists (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (h3 : 3 < p) (hpq : p < q) :
    ∃ h, q = p + 2 * h := by
  have h1 := prime_off p hp h3
  have h2 := prime_off q hq (by omega)
  exact ⟨(q - p) / 2, by omega⟩

/-- THE HAND-OFF LAW on primes: both small mirrors split between the centre and the half gap. -/
theorem hand_off_primes (p q h : ℕ) (hp : p.Prime) (hq : q.Prime) (h3 : 3 < p) (hh : q = p + 2 * h) :
    (((p + h) % 2 = 0) ↔ ¬ (h % 2 = 0)) ∧ (((p + h) % 3 = 0) ↔ ¬ (h % 3 = 0)) :=
  let hs := split_of_primes p q h hp hq h3 hh
  ⟨HandOff.two_hand_off p h hs, HandOff.three_hand_off p h hs⟩

/-- The centre's seat fixes the half gap's seat (the walker section), for primes past 3. -/
theorem centre_fixes_half_gap (p q h m : ℕ) (hp : p.Prime) (hq : q.Prime) (h3 : 3 < p)
    (hh : q = p + 2 * h) (hm : m = p + h) :
    (m % 6 = 0 → h % 2 = 1 ∧ h % 3 ≠ 0) ∧
    (m % 2 = 1 ∧ m % 3 = 0 → h % 2 = 0 ∧ h % 3 ≠ 0) ∧
    (m % 2 = 0 ∧ m % 3 ≠ 0 → h % 2 = 1 ∧ h % 3 = 0) ∧
    (m % 2 = 1 ∧ m % 3 ≠ 0 → h % 6 = 0) := by
  have hs := split_of_primes p q h hp hq h3 hh
  have t2 := HandOff.two_hand_off p h hs
  have t3 := HandOff.three_hand_off p h hs
  subst hm
  have e2 : (p + h) % 2 = 1 → h % 2 = 0 := fun e => by
    by_contra hc; exact absurd (t2.2 hc) (by omega)
  have e3 : (p + h) % 3 ≠ 0 → h % 3 = 0 := fun e => by
    by_contra hc; exact e (t3.2 hc)
  refine ⟨fun hm6 => ?_, fun hm => ?_, fun hm => ?_, fun hm => ?_⟩
  · have a := t2.1 (by omega)
    have b := t3.1 (by omega)
    exact ⟨by omega, b⟩
  · exact ⟨e2 hm.1, t3.1 hm.2⟩
  · have a := t2.1 hm.1
    exact ⟨by omega, e3 hm.2⟩
  · have a := e2 hm.1
    have b := e3 hm.2
    omega

/-- No block r >= 2 passes through both the centre and the half gap of a prime split. -/
theorem never_both_primes (p h r : ℕ) (hp : p.Prime) (hr : 2 ≤ r) (hlt : r < p) :
    ¬ (r ∣ p + h ∧ r ∣ h) := by
  rintro ⟨hm, hg⟩
  have := HandOff.never_both p h r hm hg
  rcases (Nat.dvd_prime hp).1 this.1 with h1 | h1 <;> omega

/-- The side (p mod 4) is kept exactly when the half gap is even; the facing (p mod 3) exactly
when 3 divides the half gap. -/
theorem side_and_facing_primes (p q h : ℕ) (hp : p.Prime) (hq : q.Prime) (h3 : 3 < p)
    (hh : q = p + 2 * h) :
    ((h % 2 = 0) ↔ q % 4 = p % 4) ∧ ((h % 3 = 0) ↔ q % 3 = p % 3) := by
  have hs := split_of_primes p q h hp hq h3 hh
  subst hh
  exact ⟨HandOff.side_kept p h hs, HandOff.facing_kept p h hs⟩

/-- THE HOP in the wall frame, on primes: half gap h = 3w + 2s, w = walls crossed, s in {-1,0,1};
the side mod 4 flips exactly when w is odd; the facing mod 3 flips exactly when s is not 0. -/
theorem hop_primes (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (h3 : 3 < p) (hpq : p < q) :
    ∃ w s : ℤ, (s = -1 ∨ s = 0 ∨ s = 1) ∧ ((q : ℤ) - p) / 2 = 3 * w + 2 * s ∧
      w = (q : ℤ) / 6 - (p : ℤ) / 6 ∧
      (((q : ℤ) % 4 = (p : ℤ) % 4) ↔ w % 2 = 0) ∧ (((q : ℤ) % 3 = (p : ℤ) % 3) ↔ s = 0) := by
  have h6p := TwoZero.stacked_six p hp (five_le p hp h3)
  have h6q := TwoZero.stacked_six q hq (by omega)
  refine ⟨(q : ℤ) / 6 - (p : ℤ) / 6, ((q : ℤ) % 6 - (p : ℤ) % 6) / 4, ?_, ?_, rfl, ?_, ?_⟩ <;> omega

/-- The hop written without division: 2h = 6w + (f_q - f_p), with f the facings. -/
theorem hop_facings (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (h3 : 3 < p) (hpq : p < q) :
    ∃ kp kq fp fq : ℤ, (fp = 1 ∨ fp = -1) ∧ (fq = 1 ∨ fq = -1) ∧
      (p : ℤ) = 6 * kp + fp ∧ (q : ℤ) = 6 * kq + fq ∧
      (q : ℤ) - p = 6 * (kq - kp) + (fq - fp) := by
  have h6p := TwoZero.stacked_six p hp (five_le p hp h3)
  have h6q := TwoZero.stacked_six q hq (by omega)
  refine ⟨((p : ℤ) + 1) / 6, ((q : ℤ) + 1) / 6, (p : ℤ) - 6 * (((p : ℤ) + 1) / 6),
    (q : ℤ) - 6 * (((q : ℤ) + 1) / 6), ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- THE WALL LAW on a prime block r = 6 kr + fr (r >= 5): r closes the wing f of wall k exactly when
k = f fr kr (mod r). -/
theorem wall_law_prime (r : ℕ) (hr : r.Prime) (h5 : 5 ≤ r) (kr fr k f : ℤ) (hfr : fr * fr = 1)
    (hrr : (r : ℤ) = 6 * kr + fr) :
    (r : ℤ) ∣ 6 * k + f ↔ (r : ℤ) ∣ k - f * fr * kr := by
  have hc : IsCoprime (6 * kr + fr) 6 := by
    rw [← hrr]; exact TheSolve.prime_coprime_six r hr (by omega) (by omega)
  rw [hrr]; exact TheSolve.wing_closed k kr f fr hfr hc

/-- One residue of k answers for both wings of a wall, on a prime block. -/
theorem wall_both_wings_prime (r : ℕ) (hr : r.Prime) (h5 : 5 ≤ r) (kr fr k : ℤ) (hfr : fr * fr = 1)
    (hrr : (r : ℤ) = 6 * kr + fr) :
    (¬ (r : ℤ) ∣ 6 * k + 1 ∧ ¬ (r : ℤ) ∣ 6 * k - 1) ↔
    (¬ (r : ℤ) ∣ k - fr * kr ∧ ¬ (r : ℤ) ∣ k + fr * kr) := by
  have hc : IsCoprime (6 * kr + fr) 6 := by
    rw [← hrr]; exact TheSolve.prime_coprime_six r hr (by omega) (by omega)
  rw [hrr]; exact TheSolve.wall_reads_both_wings k kr fr hfr hc

/-! ## u(n) = 2(n-1) exactly at 2, 11, 15 -/

/-- The two copies of u (RatioTwoLine and TwoMirrors) are one function. -/
theorem u_eq (n : ℕ) : TwoMirrors.u n = RatioTwoLine.u n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 4 with h | h
    · interval_cases n <;> simp
    · rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
      · rw [TwoMirrors.u_even k (by omega), RatioTwoLine.u_even k (by omega), ih k (by omega)]
      · rw [TwoMirrors.u_odd k (by omega), RatioTwoLine.u_odd k (by omega), ih k (by omega),
          ih (k + 1) (by omega)]

open RatioTwoLine in
theorem r4 : u 4 = 4 := by have := u_even 2 (by norm_num); norm_num at this; exact this
open RatioTwoLine in
theorem r5 : u 5 = 7 := by have := u_odd 2 le_rfl; norm_num at this; exact this
open RatioTwoLine in
theorem r6 : u 6 = 6 := by have := u_even 3 (by norm_num); norm_num at this; exact this
open RatioTwoLine in
theorem r7 : u 7 = 10 := by have := u_odd 3 (by norm_num); norm_num [r4] at this; exact this
open RatioTwoLine in
theorem r8 : u 8 = 8 := by have := u_even 4 (by norm_num); norm_num [r4] at this; exact this
open RatioTwoLine in
theorem r11 : u 11 = 20 := by have := u_odd 5 (by norm_num); norm_num [r5, r6] at this; exact this
open RatioTwoLine in
theorem r15 : u 15 = 28 := by have := u_odd 7 (by norm_num); norm_num [r7, r8] at this; exact this

open RatioTwoLine in
/-- u(n) = 2(n - 1) holds exactly at n = 2, 11, 15. -/
theorem two_eleven_fifteen (n : ℕ) (hn : 1 ≤ n) :
    u n = 2 * (n - 1) ↔ n = 2 ∨ n = 11 ∨ n = 15 := by
  constructor
  · intro h
    rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
    · have hk : 1 ≤ k := by omega
      rw [u_even k hk] at h
      have hodd : TwoMirrors.u k % 2 = 1 := by rw [u_eq]; omega
      rcases (TwoMirrors.u_odd_iff k).1 hodd with rfl | ⟨a, ha, rfl⟩
      · left; rfl
      · exfalso
        rw [u_pow_add_one a ha] at h
        have : 2 ^ (a + 1) = 2 * 2 ^ a := by ring
        have : 1 ≤ 2 ^ a := Nat.one_le_two_pow
        omega
    · have hlt : u (2 * k + 1) < 2 * (2 * k + 1) := by omega
      rcases (ratio_two_line _ (odd_two_mul_add_one k)).1 hlt with h1 | h1 | h1 | ⟨a, ha, h1⟩ | ⟨a, ha, h1⟩
      · rw [h1] at h; simp at h
      · right; left; exact h1
      · right; right; exact h1
      · exfalso
        rw [h1, u_pow_add_one a ha] at h
        have : 2 ^ (a + 1) = 2 * 2 ^ a := by ring
        have : 1 ≤ 2 ^ a := Nat.one_le_two_pow
        omega
      · exfalso
        rw [h1, u_three_pow_add_one a] at h
        have : 1 ≤ 2 ^ a := Nat.one_le_two_pow
        omega
  · rintro (rfl | rfl | rfl)
    · simp
    · norm_num [r11]
    · norm_num [r15]

end PrimeHandOff

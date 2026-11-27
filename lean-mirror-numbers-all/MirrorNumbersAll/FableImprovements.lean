import Mathlib
import MirrorNumbersAll.PrimeHandOff
import MirrorNumbersAll.WallWalk
import MirrorNumbersAll.WallFormula

/-!
# Improvements on the wall work (tUrUq's method; module by Fable, 11-27-2026)

* `wall_law_width`    : THE WALL LAW AT ANY WIDTH. For any wall width W and any block r = W kr + fr with
  fr gr = 1 (mod r): r closes wing f of wall k exactly when k = f gr kr (mod r). No coprimality
  hypothesis is needed; at W = 6 and fr = +-1 (so gr = fr) this is `TheSolve.wing_closed` with its
  IsCoprime hypothesis dropped (`wall_law_six`), and at W = 30 it is the law the walls-of-thirty walker
  runs on (`wall_law_thirty`).
* `wall_law_inverse`  : the same law read through W^(-1): if W m = 1 (mod r) then r closes wing f of wall
  k exactly when k = -f m (mod r). This is the form that also covers the blocks that are wings of wall 0.
* `walk_width`        : a number n prime to W is prime exactly when no prime block r prime to W with
  r * r <= n divides it. `wall_walk_width` says it in wall coordinates for any width;
  `wall_walk_thirty` is the instance for walls of 30 and their eight wings.
* `prime_count_walls` : THE COUNT IN WALL COORDINATES. For N >= 3, Nat.primeCounting N = 2 + the number of
  n <= N that pass the seat test of `WallFormula.wall_formula`. The paper's sentence "the count of primes up
  to N is 2 plus the number of seats that pass" is now a theorem about Mathlib's prime counting function.
* `hand_off_every_block` : ONE HAND-OFF FOR EVERY BLOCK. For primes p < q = p + 2h, centre m = p + h and any
  prime block r other than p and q: m is not h and not -h (mod r). At r = 2 this is the 2-hand-off and at
  r = 3 the 3-hand-off (`two_hand_off_of_block`, `three_hand_off_of_block`, `hand_off_primes'`): both
  small-mirror hand-offs are the r = 2 and r = 3 cases of one statement.
* `hop_reads_centre`  : THE HOP AND THE HAND-OFF ARE ONE. With h = 3w + 2s as in `PrimeHandOff.hop_primes`,
  w is even exactly when the centre is odd, and s = 0 exactly when the centre is off the 3-mirror.
* `same_wall_twin`    : two primes past 3 beside the same wall are a twin pair 6k - 1, 6k + 1; so a prime
  6k + 1 never hands to a prime on its own wall.
No sorry, no admit, no native_decide.
-/

namespace FableImprovements

/-! ## The wall law at any width -/

/-- THE WALL LAW AT ANY WIDTH: a block r = W kr + fr with fr gr = 1 (mod r) closes wing f of wall k
exactly when k = f gr kr (mod r). -/
theorem wall_law_width (W k f kr fr gr : ℤ) (hg : (W * kr + fr) ∣ fr * gr - 1) :
    (W * kr + fr) ∣ W * k + f ↔ (W * kr + fr) ∣ k - f * gr * kr := by
  constructor
  · intro h
    have e : k - f * gr * kr =
        -(gr * kr) * (W * k + f) + (gr * k) * (W * kr + fr) - k * (fr * gr - 1) := by ring
    rw [e]
    exact dvd_sub (dvd_add (dvd_mul_of_dvd_right h _) (dvd_mul_left _ _)) (dvd_mul_of_dvd_right hg _)
  · intro h
    have e : W * k + f = W * (k - f * gr * kr) + (f * gr) * (W * kr + fr) - f * (fr * gr - 1) := by ring
    rw [e]
    exact dvd_sub (dvd_add (dvd_mul_of_dvd_right h _) (dvd_mul_left _ _)) (dvd_mul_of_dvd_right hg _)

/-- The wall law through the inverse of the width: if W m = 1 (mod r) then r closes wing f of wall k
exactly when k = -f m (mod r). Covers every block, including the wings of wall 0 (kr = 0). -/
theorem wall_law_inverse (W k f r m : ℤ) (hm : r ∣ W * m - 1) :
    r ∣ W * k + f ↔ r ∣ k + f * m := by
  constructor
  · intro h
    have e : k + f * m = m * (W * k + f) - k * (W * m - 1) := by ring
    rw [e]; exact dvd_sub (dvd_mul_of_dvd_right h _) (dvd_mul_of_dvd_right hm _)
  · intro h
    have e : W * k + f = W * (k + f * m) - f * (W * m - 1) := by ring
    rw [e]; exact dvd_sub (dvd_mul_of_dvd_right h _) (dvd_mul_of_dvd_right hm _)

/-- Walls of six: `TheSolve.wing_closed` without its IsCoprime hypothesis (fr = +-1 is its own inverse). -/
theorem wall_law_six (k kr f fr : ℤ) (hfr : fr * fr = 1) :
    (6 * kr + fr) ∣ 6 * k + f ↔ (6 * kr + fr) ∣ k - f * fr * kr :=
  wall_law_width 6 k f kr fr fr (by rw [hfr, sub_self]; exact dvd_zero _)

/-- Walls of thirty: the law the walls-of-thirty walker runs on. -/
theorem wall_law_thirty (k f kr fr gr : ℤ) (hg : (30 * kr + fr) ∣ fr * gr - 1) :
    (30 * kr + fr) ∣ 30 * k + f ↔ (30 * kr + fr) ∣ k - f * gr * kr :=
  wall_law_width 30 k f kr fr gr hg

/-! ## The walk at any width -/

/-- A number prime to W is prime exactly when no prime block prime to W with r * r <= n divides it. -/
theorem walk_width (W n : ℕ) (hn : Nat.Coprime n W) (h2 : 2 ≤ n) :
    n.Prime ↔ ∀ r : ℕ, r.Prime → Nat.Coprime r W → r * r ≤ n → ¬ r ∣ n := by
  constructor
  · intro hp r hr _ hrr hd
    rcases (Nat.dvd_prime hp).1 hd with h | h
    · exact hr.one_lt.ne' h
    · subst h; nlinarith [hp.two_le]
  · intro hall
    by_contra hnp
    have hmp : n.minFac.Prime := Nat.minFac_prime (by omega)
    have hmd : n.minFac ∣ n := Nat.minFac_dvd n
    have hsq : n.minFac ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hnp
    rw [pow_two] at hsq
    exact hall _ hmp (Nat.Coprime.coprime_dvd_left hmd hn) hsq hmd

/-- THE WALL WALK AT ANY WIDTH: a seat n = W k + f prime to W (n >= 2) is prime exactly when no prime
block r prime to W with r * r <= n has k = -f m (mod r), m the inverse of W modulo r. -/
theorem wall_walk_width (W : ℕ) (k f : ℤ) (n : ℕ) (hn : (n : ℤ) = W * k + f) (hcop : Nat.Coprime n W)
    (h2 : 2 ≤ n) :
    n.Prime ↔ ∀ r : ℕ, r.Prime → Nat.Coprime r W → r * r ≤ n →
      ∀ m : ℤ, (r : ℤ) ∣ W * m - 1 → ¬ (r : ℤ) ∣ k + f * m := by
  rw [walk_width W n hcop h2]
  constructor
  · intro hall r hr hrW hrr m hm hd
    apply hall r hr hrW hrr
    have h1 : (r : ℤ) ∣ (W : ℤ) * k + f := (wall_law_inverse W k f r m hm).2 hd
    rw [← hn] at h1; exact Int.natCast_dvd_natCast.1 h1
  · intro hall r hr hrW hrr hd
    obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hrW.symm hr.one_lt
    have hm' : (r : ℤ) ∣ (W : ℤ) * m - 1 := by
      have h1 : ((W : ℤ) * m) % (r : ℤ) = 1 := by exact_mod_cast hm
      have h2 := Int.emod_def ((W : ℤ) * m) (r : ℤ)
      exact ⟨((W : ℤ) * m) / r, by linarith⟩
    exact hall r hr hrW hrr m hm'
      ((wall_law_inverse W k f r m hm').1 (by rw [← hn]; exact Int.natCast_dvd_natCast.2 hd))

/-- The eight wings of a wall of thirty are prime to 30. -/
theorem seat_thirty_coprime (n : ℕ)
    (hw : n % 30 = 1 ∨ n % 30 = 7 ∨ n % 30 = 11 ∨ n % 30 = 13 ∨
          n % 30 = 17 ∨ n % 30 = 19 ∨ n % 30 = 23 ∨ n % 30 = 29) : Nat.Coprime n 30 := by
  rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec]
  rcases hw with h | h | h | h | h | h | h | h <;> rw [h] <;> decide

/-- Every prime past 5 is one of the eight wings of a wall of thirty. -/
theorem prime_seat_thirty (p : ℕ) (hp : p.Prime) (h7 : 7 ≤ p) :
    p % 30 = 1 ∨ p % 30 = 7 ∨ p % 30 = 11 ∨ p % 30 = 13 ∨
    p % 30 = 17 ∨ p % 30 = 19 ∨ p % 30 = 23 ∨ p % 30 = 29 := by
  have h2 : p % 2 ≠ 0 := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 (Nat.dvd_of_mod_eq_zero h); omega
  have h3 : p % 3 ≠ 0 := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 (Nat.dvd_of_mod_eq_zero h); omega
  have h5 : p % 5 ≠ 0 := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_five hp).1 (Nat.dvd_of_mod_eq_zero h); omega
  rw [← Nat.mod_mod_of_dvd p (by norm_num : 2 ∣ 30)] at h2
  rw [← Nat.mod_mod_of_dvd p (by norm_num : 3 ∣ 30)] at h3
  rw [← Nat.mod_mod_of_dvd p (by norm_num : 5 ∣ 30)] at h5
  have h30 : p % 30 < 30 := Nat.mod_lt _ (by norm_num)
  generalize p % 30 = x at *
  interval_cases x <;> omega

/-- THE WALK ON WALLS OF THIRTY: a wing n = 30 k + f (n >= 7) is prime exactly when no prime block r prime
to 30 with r * r <= n has k = -f m (mod r), m the inverse of 30 modulo r. The blocks are themselves wings
(`prime_seat_thirty`), so the walk from 2, 3, 5 feeds itself. -/
theorem wall_walk_thirty (k f : ℤ) (n : ℕ) (hn : (n : ℤ) = 30 * k + f) (h7 : 7 ≤ n)
    (hw : n % 30 = 1 ∨ n % 30 = 7 ∨ n % 30 = 11 ∨ n % 30 = 13 ∨
          n % 30 = 17 ∨ n % 30 = 19 ∨ n % 30 = 23 ∨ n % 30 = 29) :
    n.Prime ↔ ∀ r : ℕ, r.Prime → Nat.Coprime r 30 → r * r ≤ n →
      ∀ m : ℤ, (r : ℤ) ∣ 30 * m - 1 → ¬ (r : ℤ) ∣ k + f * m := by
  have := wall_walk_width 30 k f n (by exact_mod_cast hn) (seat_thirty_coprime n hw) (by omega)
  exact_mod_cast this

/-! ## The count in wall coordinates -/

/-- The seat test of `WallFormula.wall_formula`, as a predicate on n: n >= 5 is a seat 6k + f whose wall k
is closed by no block 6j + g with (6j + g)^2 <= n. -/
def passes (n : ℕ) : Prop := 5 ≤ n ∧ ∃ k f : ℤ, (f = 1 ∨ f = -1) ∧ (n : ℤ) = 6 * k + f ∧
  ∀ j g : ℤ, 1 ≤ j → (g = 1 ∨ g = -1) → (6 * j + g) * (6 * j + g) ≤ n → ¬ (6 * j + g) ∣ k - f * g * j

/-- A number is prime exactly when it is 2, 3 or a seat that passes. -/
theorem prime_iff_passes (n : ℕ) : n.Prime ↔ n = 2 ∨ n = 3 ∨ passes n := by
  constructor
  · intro hp
    have h4 : n ≠ 4 := by rintro rfl; norm_num at hp
    have h2 := hp.two_le
    rcases (show n = 2 ∨ n = 3 ∨ 5 ≤ n by omega) with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · right; right
      obtain ⟨k, f, hf, hn⟩ := WallWalk.wall_walk_seat n hp h
      exact ⟨h, k, f, hf, hn, (WallFormula.wall_formula k f hf n hn h).1 hp⟩
  · rintro (rfl | rfl | ⟨h5, k, f, hf, hn, ht⟩)
    · norm_num
    · norm_num
    · exact (WallFormula.wall_formula k f hf n hn h5).2 ht

open Classical in
/-- THE COUNT IN WALL COORDINATES: for N >= 3 the number of primes up to N is 2 (the two mirrors) plus the
number of n <= N that pass the seat test. -/
theorem prime_count_walls (N : ℕ) (hN : 3 ≤ N) :
    Nat.primeCounting N = 2 + ((Finset.range (N + 1)).filter passes).card := by
  have h0 : Nat.primeCounting N = ((Finset.range (N + 1)).filter Nat.Prime).card := by
    rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  rw [h0]
  have h1 : (Finset.range (N + 1)).filter Nat.Prime =
      (Finset.range (N + 1)).filter (fun n => n = 2 ∨ n = 3) ∪ (Finset.range (N + 1)).filter passes := by
    rw [← Finset.filter_or]
    exact Finset.filter_congr (fun n _ => by rw [prime_iff_passes]; tauto)
  have h2 : (Finset.range (N + 1)).filter (fun n => n = 2 ∨ n = 3) = {2, 3} := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
    omega
  have h3 : Disjoint ((Finset.range (N + 1)).filter (fun n => n = 2 ∨ n = 3))
      ((Finset.range (N + 1)).filter passes) := by
    rw [Finset.disjoint_filter]
    rintro n _ (rfl | rfl) ⟨h5, -⟩ <;> omega
  rw [h1, Finset.card_union_of_disjoint h3, h2, Finset.card_pair (by norm_num)]

/-! ## One hand-off for every block -/

/-- ONE HAND-OFF FOR EVERY BLOCK: for primes p < q = p + 2h with centre m = p + h, and any prime block r
other than p and q, the centre is neither h nor -h modulo r (the two mirror seats of the half gap). -/
theorem hand_off_every_block (p q h r : ℕ) (hp : p.Prime) (hq : q.Prime) (hh : q = p + 2 * h)
    (hr : r.Prime) (hrp : r ≠ p) (hrq : r ≠ q) :
    ¬ (((p + h : ℕ) : ℤ) ≡ h [ZMOD r]) ∧ ¬ (((p + h : ℕ) : ℤ) ≡ -(h : ℤ) [ZMOD r]) := by
  constructor
  · intro e
    have d := e.symm.dvd
    have d' : (r : ℤ) ∣ (p : ℤ) := by
      have : ((p + h : ℕ) : ℤ) - (h : ℤ) = (p : ℤ) := by push_cast; ring
      rw [this] at d; exact d
    rcases (Nat.dvd_prime hp).1 (Int.natCast_dvd_natCast.1 d') with h1 | h1
    · exact hr.one_lt.ne' h1
    · exact hrp h1
  · intro e
    have d := e.symm.dvd
    have d' : (r : ℤ) ∣ (q : ℤ) := by
      have : ((p + h : ℕ) : ℤ) - -(h : ℤ) = (q : ℤ) := by rw [hh]; push_cast; ring
      rw [this] at d; exact d
    rcases (Nat.dvd_prime hq).1 (Int.natCast_dvd_natCast.1 d') with h1 | h1
    · exact hr.one_lt.ne' h1
    · exact hrq h1

/-- At r = 2 the block hand-off is the 2-hand-off: the centre is even exactly when the half gap is odd. -/
theorem two_hand_off_of_block (m h : ℕ) :
    (¬ ((m : ℤ) ≡ h [ZMOD 2]) ∧ ¬ ((m : ℤ) ≡ -(h : ℤ) [ZMOD 2])) ↔ (m % 2 = 0 ↔ ¬ h % 2 = 0) := by
  simp only [Int.ModEq]; omega

/-- At r = 3 the block hand-off is the 3-hand-off: exactly one of centre and half gap is on the 3-mirror. -/
theorem three_hand_off_of_block (m h : ℕ) :
    (¬ ((m : ℤ) ≡ h [ZMOD 3]) ∧ ¬ ((m : ℤ) ≡ -(h : ℤ) [ZMOD 3])) ↔ (m % 3 = 0 ↔ ¬ h % 3 = 0) := by
  simp only [Int.ModEq]; omega

/-- `PrimeHandOff.hand_off_primes` recovered from the block hand-off at r = 2 and r = 3. -/
theorem hand_off_primes' (p q h : ℕ) (hp : p.Prime) (hq : q.Prime) (h3 : 3 < p) (hh : q = p + 2 * h) :
    (((p + h) % 2 = 0) ↔ ¬ (h % 2 = 0)) ∧ (((p + h) % 3 = 0) ↔ ¬ (h % 3 = 0)) := by
  have e2 := hand_off_every_block p q h 2 hp hq hh Nat.prime_two (by omega) (by omega)
  have e3 := hand_off_every_block p q h 3 hp hq hh Nat.prime_three (by omega) (by omega)
  push_cast at e2 e3
  exact ⟨(two_hand_off_of_block (p + h) h).1 e2, (three_hand_off_of_block (p + h) h).1 e3⟩

/-! ## The hop and the hand-off are one -/

/-- THE HOP READS THE CENTRE: with the walls crossed w and the step s of `PrimeHandOff.hop_primes`,
w is even exactly when the centre p + h is odd, and s = 0 exactly when the centre is off the 3-mirror. -/
theorem hop_reads_centre (p q h : ℕ) (hp : p.Prime) (hq : q.Prime) (h3 : 3 < p) (hh : q = p + 2 * h)
    (w s : ℤ) (hw : ((q : ℤ) % 4 = (p : ℤ) % 4) ↔ w % 2 = 0) (hs : ((q : ℤ) % 3 = (p : ℤ) % 3) ↔ s = 0) :
    (w % 2 = 0 ↔ (p + h) % 2 = 1) ∧ (s = 0 ↔ (p + h) % 3 ≠ 0) := by
  obtain ⟨o2, o3⟩ := PrimeHandOff.hand_off_primes p q h hp hq h3 hh
  obtain ⟨s2, s3⟩ := PrimeHandOff.side_and_facing_primes p q h hp hq h3 hh
  constructor
  · rw [← hw]; omega
  · rw [← hs]; omega

/-- The hop of `PrimeHandOff.hop_primes` together with its reading on the centre, in one statement. -/
theorem hop_and_hand_off (p q h : ℕ) (hp : p.Prime) (hq : q.Prime) (h3 : 3 < p) (hpq : p < q)
    (hh : q = p + 2 * h) :
    ∃ w s : ℤ, (s = -1 ∨ s = 0 ∨ s = 1) ∧ (h : ℤ) = 3 * w + 2 * s ∧
      (w % 2 = 0 ↔ (p + h) % 2 = 1) ∧ (s = 0 ↔ (p + h) % 3 ≠ 0) := by
  obtain ⟨w, s, hs, hhalf, -, hw4, hs3⟩ := PrimeHandOff.hop_primes p q hp hq h3 hpq
  refine ⟨w, s, hs, ?_, hop_reads_centre p q h hp hq h3 hh w s hw4 hs3⟩
  rw [← hhalf]; omega

/-! ## Same wall means twins -/

/-- Two primes past 3 beside the same wall k = (n + 1) / 6 are the twin pair 6k - 1, 6k + 1. -/
theorem same_wall_twin (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (h3 : 3 < p) (hpq : p < q)
    (hw : (p + 1) / 6 = (q + 1) / 6) : q = p + 2 ∧ p % 6 = 5 ∧ q % 6 = 1 := by
  have h6p := TwoZero.stacked_six p hp (PrimeHandOff.five_le p hp h3)
  have h6q := TwoZero.stacked_six q hq (by omega)
  omega

end FableImprovements

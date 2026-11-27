import Mathlib
import MirrorNumbersAll.Upgrades
import MirrorNumbersAll.FableImprovements
import MirrorNumbersAll.TwoZero

/-!
# Claims B: rows 76 to 142 of the claim audit (tUrUq's paper v5.8, 11-27-2026)

Checked, measured and definition rows of the paper made exact, row by row:
* row 77  `arrow_runs`, `arrow_examples`, `arrow_shorthand`: nesting k -> k<1> = 2k + 1 from 1 runs 2^(n+1) - 1.
* row 78  `first_false_prime`, `false_prime_seat`, `false_prime_25`, `false_prime_49`, `false_prime_121`:
          with the mirrors below a prime block q laid, the first false prime is q * q.
* row 80  `longest_strand_chain`: the strand 16651 -> 33301 -> 66601 -> 133201 -> 266401 -> 532801.
* row 83  `strand`, `strand_start`, `strand_step`, `strand_missing`, `strand_examples`, `wing_examples`.
* row 85  `open_wings_count`, `even_open_wings_count`: the open wings to N are the odd primes to 2N + 1,
          the even open wings the primes 4j + 1.
* row 88  `wing_shared`, `gap_sides`.
* row 89  `walker_names`: the walker names q in every gap of consecutive primes 3 <= p < q.
* row 94  `place_product`, `half_unit`, `half_product_hom`.
* row 99  `fifty_five`.  row 102 `twenty_two_three`.
* row 115 `offset_eleven_line`, `offset_22_pairs`, `offset_66_pairs`, `offset_33_pairs`.
* row 128 `near_zero_iff`: within half a turn of W every open seat is 1 or a prime exactly when W/2 is
          below the next block squared; `near_zero_6`, `near_zero_30`, `near_zero_210`, `frays_2310`.
* walls of 210: `seat_210_count` (48 wings), `wall_walk_210`; any width: `prime_count_width`.
No sorry, no admit, no native_decide.
-/

namespace ClaimsB

/-! ## Row 77: arrows -/

/-- The arrow nesting k -> k<1> = k, 1, k read as w, c, w: 2k + 1. -/
def arrowNest (k : ℕ) : ℕ := 2 * k + 1

/-- Nesting from 1 runs 1, 3, 7, 15, 31, ...: n nestings give 2^(n+1) - 1. -/
theorem arrow_runs (n : ℕ) : arrowNest^[n] 1 = 2 ^ (n + 1) - 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, arrowNest]
    have : 1 ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
    rw [pow_succ 2 (n + 1)]
    omega

theorem arrow_examples : (List.range 5).map (fun n => arrowNest^[n] 1) = [1, 3, 7, 15, 31] := by
  decide

/-- The shorthand a<b> = a, b, a read as w, c, w: 2 = 1<0>, 3 = 1<1>, 7 = 3<1>. -/
theorem arrow_shorthand : 2 * 1 + 0 = 2 ∧ 2 * 1 + 1 = 3 ∧ 2 * 3 + 1 = 7 := by decide

/-! ## Row 78: the first false prime -/

/-- With every mirror r < q laid (q a prime block), a number past 1 that is not prime and is split by no
laid mirror is at least q * q. -/
theorem first_false_prime (q n : ℕ) (hn2 : 2 ≤ n) (hnp : ¬ n.Prime)
    (hoff : ∀ r, r.Prime → r < q → ¬ r ∣ n) : q * q ≤ n := by
  have hm : n.minFac.Prime := Nat.minFac_prime (by omega)
  have hq : q ≤ n.minFac := by
    by_contra h
    exact hoff _ hm (by omega) (Nat.minFac_dvd n)
  have hsq : n.minFac ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hnp
  rw [pow_two] at hsq
  exact le_trans (Nat.mul_le_mul hq hq) hsq

/-- ... and q * q is such a number: it is not prime and no mirror below q splits it. -/
theorem false_prime_seat (q : ℕ) (hq : q.Prime) :
    ¬ (q * q).Prime ∧ ∀ r, r.Prime → r < q → ¬ r ∣ q * q := by
  refine ⟨Nat.not_prime_mul hq.one_lt.ne' hq.one_lt.ne', fun r hr hrq hd => ?_⟩
  rcases (Nat.Prime.dvd_mul hr).1 hd with h | h <;>
    exact absurd ((Nat.prime_dvd_prime_iff_eq hr hq).1 h) (by omega)

/-- Stopping at the mirrors 2 and 3 the first false prime is 25. -/
theorem false_prime_25 (n : ℕ) (hn2 : 2 ≤ n) (hnp : ¬ n.Prime) (h2 : ¬ 2 ∣ n) (h3 : ¬ 3 ∣ n) :
    25 ≤ n :=
  first_false_prime 5 n hn2 hnp (fun r hr hr5 => by
    interval_cases r <;> first | exact h2 | exact h3 | (exfalso; norm_num at hr))

/-- Adding the mirror 5 moves it to 49. -/
theorem false_prime_49 (n : ℕ) (hn2 : 2 ≤ n) (hnp : ¬ n.Prime) (h2 : ¬ 2 ∣ n) (h3 : ¬ 3 ∣ n)
    (h5 : ¬ 5 ∣ n) : 49 ≤ n :=
  first_false_prime 7 n hn2 hnp (fun r hr hr7 => by
    interval_cases r <;> first | exact h2 | exact h3 | exact h5 | (exfalso; norm_num at hr))

/-- Adding the mirror 7 moves it to 121. -/
theorem false_prime_121 (n : ℕ) (hn2 : 2 ≤ n) (hnp : ¬ n.Prime) (h2 : ¬ 2 ∣ n) (h3 : ¬ 3 ∣ n)
    (h5 : ¬ 5 ∣ n) (h7 : ¬ 7 ∣ n) : 121 ≤ n :=
  first_false_prime 11 n hn2 hnp (fun r hr hr11 => by
    interval_cases r <;> first | exact h2 | exact h3 | exact h5 | exact h7 | (exfalso; norm_num at hr))

/-! ## Row 80: the strand of operators -/

/-- The strand 16651 -> 33301 -> 66601 -> 133201 -> 266401 -> 532801: each step is q -> 2q - 1, every
member is prime, the strand cannot step in below 16651 (its centre 8326 is even) and its next step
1065601 is past 10^6. That no longer strand lies below 10^6 is the exact computation of row 80. -/
theorem longest_strand_chain :
    Nat.Prime 16651 ∧ Nat.Prime 33301 ∧ Nat.Prime 66601 ∧ Nat.Prime 133201 ∧ Nat.Prime 266401 ∧
    Nat.Prime 532801 ∧ 2 * 16651 - 1 = 33301 ∧ 2 * 33301 - 1 = 66601 ∧ 2 * 66601 - 1 = 133201 ∧
    2 * 133201 - 1 = 266401 ∧ 2 * 266401 - 1 = 532801 ∧ ¬ Nat.Prime ((16651 + 1) / 2) ∧
    10 ^ 6 < 2 * 532801 - 1 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-! ## Row 83: wings and strands -/

/-- p = |w: the odd primes 3, 5, 7, 11, 13, 17, 19 by their wings 1, 2, 3, 5, 6, 8, 9. -/
theorem wing_examples : [1, 2, 3, 5, 6, 8, 9].map (fun w => 2 * w + 1) = [3, 5, 7, 11, 13, 17, 19] := by
  decide

/-- The strand of an odd block m: the wings a m + (m - 1)/2, a >= 1. -/
def strand (m a : ℕ) : ℕ := a * m + (m - 1) / 2

theorem strand_start (m : ℕ) : strand m 1 = m + (m - 1) / 2 := by simp [strand]

theorem strand_step (m a : ℕ) : strand m (a + 1) = strand m a + m := by simp [strand]; ring

/-- Every wing on a strand of an odd block m >= 3 is missing (`Upgrades.Missing`). -/
theorem strand_missing (m a : ℕ) (ha : 1 ≤ a) (hm : 3 ≤ m) (ho : m % 2 = 1) :
    Upgrades.Missing (strand m a) := ⟨a, m, ha, hm, ho, rfl⟩

/-- The strands of 3, 5, 7: 4, 7, 10, 13; 7, 12, 17; 10, 17, 24. -/
theorem strand_examples :
    (List.range 4).map (fun a => strand 3 (a + 1)) = [4, 7, 10, 13] ∧
    (List.range 3).map (fun a => strand 5 (a + 1)) = [7, 12, 17] ∧
    (List.range 3).map (fun a => strand 7 (a + 1)) = [10, 17, 24] := by decide

/-! ## Row 85: open wings counted by primes -/

section OpenWings
/-- Missing wings, decided classically (used only to form the finite sets below). -/
noncomputable local instance : DecidablePred Upgrades.Missing := Classical.decPred _

/-- The seats 2w + 1 of the open wings w in [1, N] (with any extra condition on w) are exactly the
primes in [3, 2N + 1] (with that condition on p / 2). -/
theorem open_wings_image (N : ℕ) (Q : ℕ → Prop) [DecidablePred Q] :
    ((Finset.Icc 1 N).filter (fun w => ¬ Upgrades.Missing w ∧ Q w)).image (fun w => 2 * w + 1) =
      (Finset.Icc 3 (2 * N + 1)).filter (fun p => p.Prime ∧ Q (p / 2)) := by
  ext p
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨w, ⟨⟨h1, h2⟩, ho, hq⟩, rfl⟩
    refine ⟨⟨by omega, by omega⟩, (Upgrades.open_iff_prime w h1).1 ho, ?_⟩
    have : (2 * w + 1) / 2 = w := by omega
    rw [this]; exact hq
  · rintro ⟨⟨h1, h2⟩, hp, hq⟩
    have hodd : p % 2 = 1 := TwoZero.odd_prime_reads_one p hp (by omega)
    refine ⟨p / 2, ⟨⟨by omega, by omega⟩, (Upgrades.open_iff_prime _ (by omega)).2 ?_, hq⟩, by omega⟩
    have : 2 * (p / 2) + 1 = p := by omega
    rw [this]; exact hp

theorem open_wings_card (N : ℕ) (Q : ℕ → Prop) [DecidablePred Q] :
    ((Finset.Icc 1 N).filter (fun w => ¬ Upgrades.Missing w ∧ Q w)).card =
      ((Finset.Icc 3 (2 * N + 1)).filter (fun p => p.Prime ∧ Q (p / 2))).card := by
  rw [← open_wings_image, Finset.card_image_of_injective]
  intro a b h; simp only at h; omega

/-- ROW 85, EVERY N: the open wings up to N are as many as the odd primes up to 2N + 1. -/
theorem open_wings_count (N : ℕ) :
    ((Finset.Icc 1 N).filter (fun w => ¬ Upgrades.Missing w)).card =
      ((Finset.Icc 3 (2 * N + 1)).filter Nat.Prime).card := by
  have := open_wings_card N (fun _ => True)
  simpa using this

/-- ... the even open wings are as many as the primes 4j + 1 up to 2N + 1, the odd ones as the primes 4j + 3. -/
theorem even_open_wings_count (N : ℕ) :
    ((Finset.Icc 1 N).filter (fun w => ¬ Upgrades.Missing w ∧ w % 2 = 0)).card =
      ((Finset.Icc 3 (2 * N + 1)).filter (fun p => p.Prime ∧ p % 4 = 1)).card ∧
    ((Finset.Icc 1 N).filter (fun w => ¬ Upgrades.Missing w ∧ w % 2 = 1)).card =
      ((Finset.Icc 3 (2 * N + 1)).filter (fun p => p.Prime ∧ p % 4 = 3)).card := by
  constructor
  · rw [open_wings_card N (fun w => w % 2 = 0)]
    congr 1
    apply Finset.filter_congr
    intro p hp
    simp only [Finset.mem_Icc] at hp
    constructor
    · rintro ⟨h, h2⟩
      exact ⟨h, by have := TwoZero.odd_prime_reads_one p h (by omega); omega⟩
    · rintro ⟨h, h2⟩; exact ⟨h, by omega⟩
  · rw [open_wings_card N (fun w => w % 2 = 1)]
    congr 1
    apply Finset.filter_congr
    intro p hp
    simp only [Finset.mem_Icc] at hp
    constructor
    · rintro ⟨h, h2⟩
      exact ⟨h, by have := TwoZero.odd_prime_reads_one p h (by omega); omega⟩
    · rintro ⟨h, h2⟩; exact ⟨h, by omega⟩

end OpenWings

/-! ## Row 88: the two sides of a gap -/

/-- 2k and 2k + 1 share the wing k. -/
theorem wing_shared (k : ℕ) : (2 * k) / 2 = k ∧ (2 * k + 1) / 2 = k := by omega

/-- For odd p < q the next prime q finishes the wing pair q - 1, q whose even half sits inside the gap,
while p closes the pair p - 1, p outside it. -/
theorem gap_sides (p q : ℕ) (hp : p % 2 = 1) (hq : q % 2 = 1) (hpq : p < q) :
    p < q - 1 ∧ q - 1 < q ∧ (q - 1) / 2 = q / 2 ∧ p - 1 < p ∧ (p - 1) / 2 = p / 2 := by omega

/-! ## Row 89: the walker names q -/

/-- ROW 89, EVERY GAP: for consecutive primes 3 <= p < q, the walker standing at x and reading the seat
2x - p meets no open seat for p < x < (p + q)/2 and meets q at the centre x = (p + q)/2. The open seat is
read as an open wing (`Upgrades.Missing`, `Upgrades.open_iff_prime`). -/
theorem walker_names (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (h3 : 3 ≤ p) (hpq : p < q)
    (hnext : ∀ n, p < n → n < q → ¬ n.Prime) :
    2 * ((p + q) / 2) - p = q ∧ ¬ Upgrades.Missing (q / 2) ∧
    ∀ x, p < x → x < (p + q) / 2 → Upgrades.Missing ((2 * x - p) / 2) := by
  have hpo := TwoZero.odd_prime_reads_one p hp (by omega)
  have hqo := TwoZero.odd_prime_reads_one q hq (by omega)
  refine ⟨by omega, ?_, ?_⟩
  · rw [Upgrades.open_iff_prime _ (by omega)]
    have : 2 * (q / 2) + 1 = q := by omega
    rw [this]; exact hq
  · intro x hx1 hx2
    rw [Upgrades.missing_iff_not_prime _ (by omega)]
    have : 2 * ((2 * x - p) / 2) + 1 = 2 * x - p := by omega
    rw [this]
    exact hnext _ (by omega) (by omega)

/-! ## Row 94: the even line and its unit -/

/-- On the even line (place k at 2k) the ordinary product of the places a and b lands on place 2ab:
the place product a (x) b = 2ab, so 1 (x) 1 = 2 (2 x 2 = 4). -/
theorem place_product (a b : ℕ) : (2 * a) * (2 * b) = 2 * (2 * a * b) ∧ (2 * 1) * (2 * 1) = 2 * 2 := by
  constructor <;> ring

/-- With 2 taken as the unit, a . b = ab / 2: 2 is its unit, 2 . 2 = 2, and doubling carries ordinary
multiplication onto it, so its primes are the doubled primes and factoring is single again. -/
theorem half_unit (x : ℕ) : (2 * x) * 2 / 2 = 2 * x ∧ 2 * 2 / 2 = 2 := by omega

theorem half_product_hom (a b : ℕ) : (2 * a) * (2 * b) / 2 = 2 * (a * b) := by
  have : (2 * a) * (2 * b) = 2 * (2 * (a * b)) := by ring
  rw [this]; omega

/-! ## Rows 99 and 102: examples -/

/-- 55 = 27, 28, 27: its halving shows the neighbours 54 = 2 3^3 and 56 = 2^3 7, which share no block with
55 = 5 x 11; centre^2 - wing^2 = 55. -/
theorem fifty_five : 27 + 28 = 55 ∧ 54 = 2 * 3 ^ 3 ∧ 56 = 2 ^ 3 * 7 ∧ Nat.Coprime 54 55 ∧
    Nat.Coprime 56 55 ∧ 55 = 5 * 11 ∧ 28 ^ 2 - 27 ^ 2 = 55 := by
  refine ⟨rfl, rfl, rfl, by norm_num, by norm_num, rfl, rfl⟩

/-- 22 = 11, 0, 11 and 23 = 11, 1, 11 are the pictures 1, 0, 1 = 2 and 1, 1, 1 = 3 with the wing 1 read as 11. -/
theorem twenty_two_three : 2 * 11 + 0 = 22 ∧ 2 * 11 + 1 = 23 ∧ 2 * 1 + 0 = 2 ∧ 2 * 1 + 1 = 3 := by decide

/-! ## Row 115: offsets of eleven -/

/-- The mirror line with offset 11: 5 <-> 6, 7 <-> 4, 3 <-> 8, 2 <-> 9, 1 <-> 10, 11 <-> 0. -/
theorem offset_eleven_line :
    [5, 7, 3, 2, 1, 11].map (fun n => 11 - n) = [6, 4, 8, 9, 10, 0] := by decide

/-- Offset 22 pairs primes with primes: 3 <-> 19, 5 <-> 17, 11 <-> 11 (p <= 11). -/
theorem offset_22_pairs :
    (List.range 12).filter (fun p => p.Prime ∧ (22 - p).Prime) = [3, 5, 11] := by decide

/-- Offset 66: six pairs, 5 <-> 61, 7 <-> 59, 13 <-> 53, 19 <-> 47, 23 <-> 43, 29 <-> 37 (p <= 33). -/
theorem offset_66_pairs :
    (List.range 34).filter (fun p => p.Prime ∧ (66 - p).Prime) = [5, 7, 13, 19, 23, 29] := by decide

/-- Offset 33 pairs a prime with an even prime 2r exactly at 7 <-> 26, 11 <-> 22, 19 <-> 14, 23 <-> 10,
29 <-> 4. -/
theorem offset_33_pairs :
    (List.range 34).filter (fun p => p.Prime ∧ (33 - p) % 2 = 0 ∧ ((33 - p) / 2).Prime) =
      [7, 11, 19, 23, 29] := by decide

/-! ## Row 128: holds while W/2 is below the next block squared -/

/-- ROW 128, EVERY WIDTH: let every prime below the prime block q divide W, and q not divide W. Within half
a turn of W every open seat (prime to W) is 1 or a prime exactly when W/2 is below q^2. -/
theorem near_zero_iff (W q : ℕ) (hq : q.Prime) (hW : ∀ r, r.Prime → r < q → r ∣ W) (hqW : ¬ q ∣ W) :
    (∀ s, 1 ≤ s → s ≤ W / 2 → Nat.Coprime s W → s = 1 ∨ s.Prime) ↔ W / 2 < q * q := by
  constructor
  · intro h
    by_contra hle
    have hc0 : Nat.Coprime q W := (Nat.Prime.coprime_iff_not_dvd hq).2 hqW
    have hc : Nat.Coprime (q * q) W := Nat.coprime_mul_iff_left.2 ⟨hc0, hc0⟩
    have h2 := hq.two_le
    rcases h (q * q) (by nlinarith) (by omega) hc with h1 | h1
    · nlinarith
    · exact (false_prime_seat q hq).1 h1
  · intro hlt s hs1 hs hc
    by_contra hne
    push Not at hne
    have h2 : 2 ≤ s := by
      rcases Nat.lt_or_ge s 2 with h | h
      · exact absurd (by omega : s = 1) hne.1
      · exact h
    have := first_false_prime q s h2 hne.2 (fun r hr hrq hd =>
      hr.one_lt.ne' (Nat.eq_one_of_dvd_one (by rw [← hc.gcd_eq_one]; exact Nat.dvd_gcd hd (hW r hr hrq))))
    omega

/-- Walls of 6: within 3 of the zero every open seat is 1 or a prime (3 < 5^2). -/
theorem near_zero_6 : ∀ s, 1 ≤ s → s ≤ 6 / 2 → Nat.Coprime s 6 → s = 1 ∨ s.Prime :=
  (near_zero_iff 6 5 (by norm_num) (fun r hr h => by
    interval_cases r <;> first | (norm_num; done) | exact absurd hr (by norm_num)) (by norm_num)).2 (by norm_num)

/-- Walls of 30: within 15 (15 < 7^2). -/
theorem near_zero_30 : ∀ s, 1 ≤ s → s ≤ 30 / 2 → Nat.Coprime s 30 → s = 1 ∨ s.Prime :=
  (near_zero_iff 30 7 (by norm_num) (fun r hr h => by
    interval_cases r <;> first | (norm_num; done) | exact absurd hr (by norm_num)) (by norm_num)).2 (by norm_num)

/-- Walls of 210: within 105 (105 < 11^2). -/
theorem near_zero_210 : ∀ s, 1 ≤ s → s ≤ 210 / 2 → Nat.Coprime s 210 → s = 1 ∨ s.Prime :=
  (near_zero_iff 210 11 (by norm_num) (fun r hr h => by
    interval_cases r <;> first | (norm_num; done) | exact absurd hr (by norm_num)) (by norm_num)).2 (by norm_num)

/-- Walls of 2310: 1155 is not below 13^2 = 169, so the half turn holds an open seat that is neither 1 nor prime. -/
theorem frays_2310 : ¬ ∀ s, 1 ≤ s → s ≤ 2310 / 2 → Nat.Coprime s 2310 → s = 1 ∨ s.Prime := by
  rw [near_zero_iff 2310 13 (by norm_num) (fun r hr h => by
    interval_cases r <;> first | (norm_num; done) | exact absurd hr (by norm_num)) (by norm_num)]
  norm_num

/-! ## Walls of 210 and the count at any width -/

/-- A wall of 210 has 48 wings: the seats below 210 prime to 210. -/
theorem seat_210_count : ((Finset.range 210).filter (fun r => Nat.Coprime r 210)).card = 48 := by
  decide

/-- THE WALK ON WALLS OF 210: a seat n = 210 k + f prime to 210 (n >= 2) is prime exactly when no prime
block r prime to 210 with r * r <= n has k = -f m (mod r), m the inverse of 210 modulo r. -/
theorem wall_walk_210 (k f : ℤ) (n : ℕ) (hn : (n : ℤ) = 210 * k + f) (hcop : Nat.Coprime n 210)
    (h2 : 2 ≤ n) :
    n.Prime ↔ ∀ r : ℕ, r.Prime → Nat.Coprime r 210 → r * r ≤ n →
      ∀ m : ℤ, (r : ℤ) ∣ 210 * m - 1 → ¬ (r : ℤ) ∣ k + f * m := by
  have := FableImprovements.wall_walk_width 210 k f n (by exact_mod_cast hn) hcop h2
  exact_mod_cast this

section CountWidth
open Classical

/-- THE COUNT AT ANY WIDTH: the primes up to N are the primes dividing W plus the seats n <= N prime to W
(n >= 2) that no prime block r prime to W with r * r <= n divides. At W = 6 this is
`FableImprovements.prime_count_walls`' 2 + passes; at W = 30 the eight wings, at W = 210 the 48. -/
theorem prime_count_width (W N : ℕ) :
    Nat.primeCounting N = ((Finset.range (N + 1)).filter (fun p => p.Prime ∧ p ∣ W)).card +
      ((Finset.range (N + 1)).filter (fun n => 2 ≤ n ∧ Nat.Coprime n W ∧
        ∀ r : ℕ, r.Prime → Nat.Coprime r W → r * r ≤ n → ¬ r ∣ n)).card := by
  have h0 : Nat.primeCounting N = ((Finset.range (N + 1)).filter Nat.Prime).card := by
    rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  rw [h0, ← Finset.card_union_of_disjoint]
  · congr 1
    rw [← Finset.filter_or]
    apply Finset.filter_congr
    intro n _
    constructor
    · intro hp
      by_cases hd : n ∣ W
      · exact Or.inl ⟨hp, hd⟩
      · have hc : Nat.Coprime n W := (Nat.Prime.coprime_iff_not_dvd hp).2 hd
        exact Or.inr ⟨hp.two_le, hc, (FableImprovements.walk_width W n hc hp.two_le).1 hp⟩
    · rintro (⟨hp, -⟩ | ⟨h2, hc, ht⟩)
      · exact hp
      · exact (FableImprovements.walk_width W n hc h2).2 ht
  · rw [Finset.disjoint_filter]
    rintro n - ⟨hp, hd⟩ ⟨-, hc, -⟩
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 hc hd

end CountWidth

end ClaimsB

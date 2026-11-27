import Mathlib
import MirrorNumbersAll.NineCubes
import MirrorNumbersAll.TwoMirrors
import MirrorNumbersAll.UnifiedCode

/-!
# Upgrades: claims checked to a range, now proven for every n (tUrUq's mirror method, 11-27-2026)

* `missing_iff_not_prime`, `open_iff_prime` (#84): a wing w >= 1 is missing (w = a m + (m-1)/2 with
  a >= 1, m odd >= 3) exactly when 2w + 1 is not prime; the open wings are the prime seats.
* `twice_prime_iff_open` (#93): 4w + 2 is twice a prime exactly when wing w is open.
* `even_wing_iff_two_squares` (#86): for a prime p = 2w + 1, w is even exactly when p is a sum of two squares.
* `cube_sum_prime_iff` (#122): a^3 + b^3 (a, b >= 1) is prime only at 1^3 + 1^3 = 2; first two sums 2 and 9.
* `square_past_self_counting_iff` (#121): a prime square p^2 is one past a self-counting number 2^a or 3 2^a exactly at p = 2, 3, 5, 7.
* `ladder_sign` (#104): the side-and-diagonal ladder of sqrt 2 keeps x^2 - 2 y^2 = -1, +1 alternating.
* `first_four_factor` (#61): 11 and 15 are the first odd numbers whose count u holds a factor 4 (20, 28).
* `B_reverse`, `B_length`, `hub_even`, `hub_odd` (#12): the halving build is a mirror of an odd number of
  triples; an even hub is the zero, an odd number inherits the hub of its middle block.
* `centre_unit_iff` (#46): the centre digit is a unit exactly for 1 and 2^m + 1 (m >= 1), every n.
* `step_position`, `one_moves`, `centre_stays` (#17): under one order digit i moves to digit 3i + 1.
* `width_closed` (#44): the zoomed width is 3^(k+2) for 3 2^k < n <= 3 2^(k+1).
No sorry, no admit, no native_decide.
-/

namespace Upgrades

/-! ## 1. Missing wings, open wings, twice a prime (#84, #93) -/

/-- Wing w is missing: copies of an odd block m >= 3 plus half of m, w = a m + (m-1)/2, a >= 1. -/
def Missing (w : ℕ) : Prop := ∃ a m, 1 ≤ a ∧ 3 ≤ m ∧ m % 2 = 1 ∧ w = a * m + (m - 1) / 2

/-- The missing wing's seat faces: 2(a m + (m-1)/2) + 1 = (2a + 1) m. -/
theorem missing_seat (a m : ℕ) (hm : m % 2 = 1) : 2 * (a * m + (m - 1) / 2) + 1 = (2 * a + 1) * m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k + 1 := ⟨m / 2, by omega⟩
  have : (2 * k + 1 - 1) / 2 = k := by omega
  rw [this]; ring

/-- A wing w >= 1 is missing exactly when its seat 2w + 1 is not prime. -/
theorem missing_iff_not_prime (w : ℕ) (hw : 1 ≤ w) : Missing w ↔ ¬ (2 * w + 1).Prime := by
  constructor
  · rintro ⟨a, m, ha, hm3, hm, rfl⟩ hp
    rw [missing_seat a m hm] at hp
    rcases hp.eq_one_or_self_of_dvd m (Dvd.intro_left _ rfl) with h | h
    · omega
    · have : 1 * m < (2 * a + 1) * m := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      omega
  · intro hp
    have h2 : 2 ≤ 2 * w + 1 := by omega
    set m := (2 * w + 1).minFac with hmdef
    have hmd : m ∣ 2 * w + 1 := Nat.minFac_dvd _
    have hmp : m.Prime := Nat.minFac_prime (by omega)
    have hlt : m < 2 * w + 1 := by
      rcases (Nat.minFac_le (by omega : 0 < 2 * w + 1)).lt_or_eq with h | h
      · exact h
      · exact absurd (h ▸ hmp) hp
    obtain ⟨c, hc⟩ := hmd
    have hm2 : m ≠ 2 := by
      intro h; rw [h] at hc; omega
    have hm3 : 3 ≤ m := by have := hmp.two_le; omega
    have hmodd : m % 2 = 1 := by
      rcases hmp.eq_two_or_odd with h | h
      · exact absurd h hm2
      · exact h
    have hcodd : c % 2 = 1 := by
      rcases Nat.even_or_odd c with ⟨t, ht⟩ | ⟨t, ht⟩
      · subst ht; exfalso
        have : 2 * w + 1 = 2 * (m * t) := by rw [hc]; ring
        omega
      · omega
    have hc3 : 3 ≤ c := by
      rcases (by omega : c = 1 ∨ 3 ≤ c) with h | h
      · rw [h] at hc; omega
      · exact h
    refine ⟨c / 2, m, by omega, hm3, hmodd, ?_⟩
    have e := missing_seat (c / 2) m hmodd
    have : 2 * (c / 2) + 1 = c := by omega
    rw [this] at e
    have : 2 * w + 1 = 2 * (c / 2 * m + (m - 1) / 2) + 1 := by rw [e, hc, mul_comm]
    omega

/-- OPEN WINGS ARE PRIME SEATS (#84), every wing w >= 1. -/
theorem open_iff_prime (w : ℕ) (hw : 1 ≤ w) : ¬ Missing w ↔ (2 * w + 1).Prime := by
  rw [missing_iff_not_prime w hw, not_not]

/-- 4w + 2 IS TWICE A PRIME EXACTLY WHEN WING w IS OPEN (#93), every wing w >= 1. -/
theorem twice_prime_iff_open (w : ℕ) (hw : 1 ≤ w) :
    (∃ q, q.Prime ∧ 4 * w + 2 = 2 * q) ↔ ¬ Missing w := by
  rw [open_iff_prime w hw]
  constructor
  · rintro ⟨q, hq, h⟩
    have : q = 2 * w + 1 := by omega
    exact this ▸ hq
  · intro h; exact ⟨_, h, by ring⟩

/-! ## 2. Even open wings are the imaginary side (#86) -/

/-- The wing of an odd prime p = 2w + 1 is even exactly when p sits one past a multiple of 4. -/
theorem even_wing_iff_mod_four (w : ℕ) : w % 2 = 0 ↔ (2 * w + 1) % 4 = 1 := by omega

/-- A sum of two squares never sits 3 past a multiple of 4. -/
theorem two_squares_mod_four (a b : ℕ) : (a ^ 2 + b ^ 2) % 4 ≠ 3 := by
  have ha : a ^ 2 % 4 = 0 ∨ a ^ 2 % 4 = 1 := by
    rcases Nat.even_or_odd a with ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> ring_nf <;> omega
  have hb : b ^ 2 % 4 = 0 ∨ b ^ 2 % 4 = 1 := by
    rcases Nat.even_or_odd b with ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> ring_nf <;> omega
  omega

/-- EVEN OPEN WINGS BELONG TO SUMS OF TWO SQUARES, ODD ONES DO NOT (#86), every prime p = 2w + 1. -/
theorem even_wing_iff_two_squares (w : ℕ) (hp : (2 * w + 1).Prime) :
    w % 2 = 0 ↔ ∃ a b, a ^ 2 + b ^ 2 = 2 * w + 1 := by
  constructor
  · intro h
    have := Fact.mk hp
    exact Nat.Prime.sq_add_sq (by omega)
  · rintro ⟨a, b, h⟩
    have := two_squares_mod_four a b
    rw [h] at this
    omega

/-! ## 3. Sums of two cubes (#122) -/

/-- SUMS OF TWO CUBES ARE COMPOSITE EXCEPT 1^3 + 1^3 = 2 (#122), every a, b >= 1. -/
theorem cube_sum_prime_iff (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (a ^ 3 + b ^ 3).Prime ↔ a = 1 ∧ b = 1 := by
  constructor
  · intro hp
    by_contra hc
    rcases le_total b a with h | h
    · exact NineCubes.cube_sum_closed a b hb h (by omega) hp
    · exact NineCubes.cube_sum_closed b a ha h (by omega) (add_comm (a ^ 3) (b ^ 3) ▸ hp)
  · rintro ⟨rfl, rfl⟩; norm_num

/-- The first two sums of two cubes are 2 and 9: every other one is at least 16. -/
theorem cube_sum_first_two (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    a ^ 3 + b ^ 3 = 2 ∨ a ^ 3 + b ^ 3 = 9 ∨ 16 ≤ a ^ 3 + b ^ 3 := by
  rcases (by omega : a = 1 ∨ a = 2 ∨ 3 ≤ a) with rfl | rfl | h
  · rcases (by omega : b = 1 ∨ b = 2 ∨ 3 ≤ b) with rfl | rfl | h'
    · norm_num
    · norm_num
    · right; right; have : 27 ≤ b ^ 3 := by nlinarith [pow_le_pow_left₀ (by norm_num) h' 3]
      omega
  · rcases (by omega : b = 1 ∨ 2 ≤ b) with rfl | h'
    · norm_num
    · right; right; have : 8 ≤ b ^ 3 := by nlinarith [pow_le_pow_left₀ (by norm_num) h' 3]
      norm_num; omega
  · right; right; have : 27 ≤ a ^ 3 := by nlinarith [pow_le_pow_left₀ (by norm_num) h 3]
    omega

/-! ## 4. Prime squares one past a self-counting number (#121) -/

/-- A self-counting number: 2^a or 3 2^a (a >= 0), the numbers with u(n) = n (RatioTwoLine.fixed_iff). -/
def SelfCounting (n : ℕ) : Prop := ∃ a, n = 2 ^ a ∨ n = 3 * 2 ^ a

/-- Every divisor of a self-counting number is self-counting. -/
theorem self_counting_dvd (d n : ℕ) (hn : SelfCounting n) (hd : d ∣ n) : SelfCounting d := by
  obtain ⟨a, rfl | rfl⟩ := hn
  · obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
    exact ⟨i, Or.inl rfl⟩
  · obtain ⟨y, z, hy, hz, rfl⟩ := Nat.dvd_mul.1 hd
    obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hz
    rcases (Nat.prime_three.eq_one_or_self_of_dvd y hy) with rfl | rfl
    · exact ⟨i, Or.inl (one_mul _)⟩
    · exact ⟨i, Or.inr rfl⟩

/-- Two self-counting numbers two apart: (1, 3), (2, 4), (4, 6), (6, 8). -/
theorem self_counting_two_apart (x : ℕ) (hx : SelfCounting x) (hy : SelfCounting (x + 2)) :
    x = 1 ∨ x = 2 ∨ x = 4 ∨ x = 6 := by
  obtain ⟨i, hi⟩ := hx
  obtain ⟨j, hj⟩ := hy
  have key : ∀ i : ℕ, 2 ^ i = 1 ∨ 2 ^ i = 2 ∨ (2 ^ i) % 4 = 0 := by
    intro i
    rcases i with _ | _ | i
    · simp
    · simp
    · right; right; rw [show 2 ^ (i + 2) = 4 * 2 ^ i by ring]; simp
  have h1 := key i
  have h2 := key j
  have h3 : 0 < 2 ^ i := by positivity
  generalize 2 ^ i = A at *
  generalize 2 ^ j = B at *
  clear key
  omega

/-- THE PRIME SQUARES ONE PAST A SELF-COUNTING NUMBER ARE THOSE OF 2, 3, 5, 7 (#121), proven for every prime p. -/
theorem square_past_self_counting_iff (p : ℕ) (hp : p.Prime) :
    SelfCounting (p ^ 2 - 1) ↔ p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
  constructor
  · intro hw
    have h2 := hp.two_le
    have e : p ^ 2 - 1 = (p - 1) * (p + 1) := by
      obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
      simp only [Nat.add_sub_cancel]; ring_nf; omega
    rw [e] at hw
    have h1 := self_counting_dvd (p - 1) _ hw (Dvd.intro _ rfl)
    have h3 := self_counting_dvd (p + 1) _ hw (Dvd.intro_left _ rfl)
    have : p - 1 + 2 = p + 1 := by omega
    rw [← this] at h3
    rcases self_counting_two_apart _ h1 h3 with h | h | h | h
    · left; omega
    · right; left; omega
    · right; right; left; omega
    · right; right; right; omega
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, Or.inr rfl⟩
    · exact ⟨3, Or.inl rfl⟩
    · exact ⟨3, Or.inr rfl⟩
    · exact ⟨4, Or.inr rfl⟩

/-- 4, 9, 25, 49 sit one past the self-counting numbers 3, 2^3, 3 2^3, 3 2^4. -/
theorem square_self_counting : 2 ^ 2 = 3 * 2 ^ 0 + 1 ∧ 3 ^ 2 = 2 ^ 3 + 1 ∧ 5 ^ 2 = 3 * 2 ^ 3 + 1 ∧
    7 ^ 2 = 3 * 2 ^ 4 + 1 := by norm_num

/-! ## 5. The side-and-diagonal ladder of sqrt 2 (#104) -/

/-- The ladder: (1, 1), then (x, y) -> (x + 2y, x + y). -/
def ladder : ℕ → ℕ × ℕ
  | 0 => (1, 1)
  | k + 1 => ((ladder k).1 + 2 * (ladder k).2, (ladder k).1 + (ladder k).2)

/-- The rungs (3, 2), (7, 5), (17, 12), (41, 29). -/
theorem ladder_rungs : ladder 1 = (3, 2) ∧ ladder 2 = (7, 5) ∧ ladder 3 = (17, 12) ∧
    ladder 4 = (41, 29) := by decide

/-- EVERY RUNG: x^2 - 2 y^2 = (-1)^(k+1); 7^2 = 2 5^2 - 1 is rung 2. -/
theorem ladder_sign (k : ℕ) :
    ((ladder k).1 : ℤ) ^ 2 - 2 * ((ladder k).2 : ℤ) ^ 2 = (-1) ^ (k + 1) := by
  induction k with
  | zero => simp [ladder]
  | succ k ih =>
    rw [show ((-1 : ℤ)) ^ (k + 1 + 1) = (-1) ^ (k + 1) * (-1) by ring, ← ih]
    simp only [ladder]; push_cast; ring

theorem seven_five : 7 ^ 2 = 2 * 5 ^ 2 - 1 := by norm_num

/-! ## 6. 11 and 15, the first odd counts with a factor 4 (#61) -/

/-- Odd n below 15 with 4 | u n: only 11; u 11 = 4 5, u 15 = 4 7 (one factor 4 each). -/
theorem first_four_factor :
    (∀ n < 15, n % 2 = 1 → (4 ∣ TwoMirrors.u n ↔ n = 11)) ∧
    TwoMirrors.u 11 = 4 * 5 ∧ TwoMirrors.u 15 = 4 * 7 := by
  refine ⟨fun n hn ho => ?_, by simp [TwoMirrors.u], by simp [TwoMirrors.u]⟩
  interval_cases n <;> simp_all [TwoMirrors.u]

/-! ## 7. The halving build: a mirror with one hub (#12), the centre digit (#46) -/

/-- The halving build as digits: B(1), B(2), B(3) = 010, 101, 111; B(2k) = B(k), 000, B(k);
B(2k+1) = B(k), B(k+1), B(k). (B 0 is the zero word.) -/
def B : ℕ → List ℕ
  | 0 => [0, 0, 0]
  | 1 => [0, 1, 0]
  | 2 => [1, 0, 1]
  | 3 => [1, 1, 1]
  | n + 4 =>
    if (n + 4) % 2 = 0 then B ((n + 4) / 2) ++ [0, 0, 0] ++ B ((n + 4) / 2)
    else B ((n + 4) / 2) ++ B ((n + 4) / 2 + 1) ++ B ((n + 4) / 2)
  decreasing_by all_goals omega

theorem B_even (k : ℕ) (hk : 2 ≤ k) : B (2 * k) = B k ++ [0, 0, 0] ++ B k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  rw [show 2 * (m + 2) = 2 * m + 4 by ring, B]
  simp [show (2 * m + 4) / 2 = m + 2 by omega]

theorem B_odd (k : ℕ) (hk : 2 ≤ k) : B (2 * k + 1) = B k ++ B (k + 1) ++ B k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  rw [show 2 * (m + 2) + 1 = (2 * m + 1) + 4 by ring, B]
  simp [show ¬ (2 * m + 1 + 4) % 2 = 0 by omega, show (2 * m + 1 + 4) / 2 = m + 2 by omega]

/-- Split n >= 4 as 2k or 2k + 1 with k >= 2. -/
theorem split_four (n : ℕ) (h : 4 ≤ n) :
    (∃ k, 2 ≤ k ∧ n = 2 * k) ∨ (∃ k, 2 ≤ k ∧ n = 2 * k + 1) := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · left; exact ⟨k, by omega, by omega⟩
  · right; exact ⟨k, by omega, hk⟩

/-- Every build reads the same from either wing. -/
theorem B_reverse (n : ℕ) : (B n).reverse = B n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 4 with h | h
    · interval_cases n <;> simp [B]
    · rcases split_four n h with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
      · rw [B_even k hk]; simp [ih k (by omega)]
      · rw [B_odd k hk]; simp [ih k (by omega), ih (k + 1) (by omega)]

/-- Every build is an odd number of triples: length = 3 T with T odd. -/
theorem B_length (n : ℕ) : (B n).length % 6 = 3 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 4 with h | h
    · interval_cases n <;> simp [B]
    · rcases split_four n h with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
      · rw [B_even k hk]; have := ih k (by omega); simp; omega
      · rw [B_odd k hk]; have := ih k (by omega); have := ih (k + 1) (by omega); simp; omega

/-- The hub: the single centre triple of the build. -/
def hub (n : ℕ) : List ℕ := ((B n).drop (((B n).length - 3) / 2)).take 3

/-- An even number's hub is the zero between its two halves. -/
theorem hub_even (k : ℕ) (hk : 2 ≤ k) : hub (2 * k) = [0, 0, 0] := by
  unfold hub
  rw [B_even k hk]
  have e : ((B k ++ [0, 0, 0] ++ B k).length - 3) / 2 = (B k).length := by simp; omega
  rw [e, List.append_assoc, List.drop_left]
  rfl

/-- Dropping past a left piece. -/
theorem drop_past (a m : List ℕ) (x : ℕ) : (a ++ m).drop (a.length + x) = m.drop x := by
  induction a with
  | nil => simp
  | cons y a ih => simp only [List.cons_append, List.length_cons, Nat.add_right_comm, List.drop_succ_cons, ih]

/-- An odd number inherits the hub of its middle block. -/
theorem hub_odd (k : ℕ) (hk : 2 ≤ k) : hub (2 * k + 1) = hub (k + 1) := by
  unfold hub
  rw [B_odd k hk]
  have hl := B_length (k + 1)
  have e : ((B k ++ B (k + 1) ++ B k).length - 3) / 2 = (B k).length + ((B (k + 1)).length - 3) / 2 := by
    simp only [List.length_append]; omega
  rw [e, List.append_assoc, drop_past, List.drop_append_of_le_length (by omega),
    List.take_append_of_le_length (by simp only [List.length_drop]; omega)]

/-- The centre digit of the build. -/
def centreDigit (n : ℕ) : ℕ := (B n).getD ((B n).length / 2) 0

/-- The centre digit is the middle of the hub. -/
theorem centreDigit_hub (n : ℕ) : centreDigit n = (hub n).getD 1 0 := by
  have hl := B_length n
  unfold centreDigit hub
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop]
  simp only [show 1 < 3 from by norm_num, ite_true]
  congr 2; omega

/-- THE CENTRE DIGIT IS A UNIT EXACTLY FOR 1 AND 2^m + 1, m >= 1 (#46), every n. -/
theorem centre_unit_iff (n : ℕ) : centreDigit n = 1 ↔ TwoMirrors.P n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 4 with h | h
    · interval_cases n
      · simp [centreDigit, B, TwoMirrors.P]
      · simp [centreDigit, B, TwoMirrors.P]
      · simp [centreDigit, B, TwoMirrors.P]
      · simp [centreDigit, B, TwoMirrors.P]; exact ⟨1, le_rfl, rfl⟩
    · rcases split_four n h with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
      · rw [centreDigit_hub, hub_even k hk]
        simp only [TwoMirrors.P]
        constructor
        · intro h; simp at h
        · rintro (h | ⟨a, ha, h⟩)
          · omega
          · exfalso
            obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
            rw [pow_succ] at h; omega
      · rw [centreDigit_hub, hub_odd k hk, ← centreDigit_hub, ih (k + 1) (by omega)]
        simp only [TwoMirrors.P]
        constructor
        · rintro (h | ⟨a, ha, h⟩)
          · omega
          · right; exact ⟨a + 1, by omega, by rw [pow_succ]; omega⟩
        · rintro (h | ⟨a, ha, h⟩)
          · omega
          · right
            obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
            rw [pow_succ] at h
            refine ⟨b, ?_, by omega⟩
            rcases Nat.eq_zero_or_pos b with rfl | hb
            · simp at h; omega
            · exact hb

/-! ## 8. Orders: a one at digit i moves to digit 3i + 1 (#17) -/

/-- Under one order (UnifiedCode.step) digit i lands on digit 3i + 1, and 3i, 3i + 2 are zeros. -/
theorem step_position (l : List ℕ) (i : ℕ) :
    (UnifiedCode.step l)[3 * i + 1]? = l[i]?.map (fun d => if d = 0 then 0 else 1) ∧
    (UnifiedCode.step l)[3 * i]? = l[i]?.map (fun _ => 0) ∧
    (UnifiedCode.step l)[3 * i + 2]? = l[i]?.map (fun _ => 0) := by
  induction l generalizing i with
  | nil => simp [UnifiedCode.step]
  | cons d l ih =>
    have hs : UnifiedCode.step (d :: l) =
        (if d = 0 then [0, 0, 0] else [0, 1, 0]) ++ UnifiedCode.step l := by
      simp [UnifiedCode.step]
    rw [hs]
    rcases i with _ | i
    · split_ifs <;> simp_all
    · have hlen : (if d = 0 then [0, 0, 0] else [0, 1, 0]).length = 3 := by split_ifs <;> rfl
      obtain ⟨h1, h2, h3⟩ := ih i
      refine ⟨?_, ?_, ?_⟩ <;>
      · rw [List.getElem?_append_right (by omega), hlen]
        simp only [List.getElem?_cons_succ]
        first
          | (rw [show 3 * (i + 1) + 1 - 3 = 3 * i + 1 by omega]; exact h1)
          | (rw [show 3 * (i + 1) - 3 = 3 * i by omega]; exact h2)
          | (rw [show 3 * (i + 1) + 2 - 3 = 3 * i + 2 by omega]; exact h3)

/-- On digit strings (0 and 1) the one at digit i is the one at digit 3i + 1. -/
theorem one_moves (l : List ℕ) (h : ∀ x ∈ l, x ≤ 1) (i : ℕ) :
    (UnifiedCode.step l)[3 * i + 1]? = l[i]? := by
  rw [(step_position l i).1]
  rcases hi : l[i]? with _ | x
  · rfl
  · have := h x (List.mem_of_getElem? hi)
    simp only [Option.map_some]
    congr 1; split_ifs <;> omega

/-- The centre stays the centre: on an odd-length digit string the centre digit is kept. -/
theorem centre_stays (l : List ℕ) (h : ∀ x ∈ l, x ≤ 1) (ho : l.length % 2 = 1) :
    (UnifiedCode.step l)[(UnifiedCode.step l).length / 2]? = l[l.length / 2]? := by
  rw [UnifiedCode.step_length, show 3 * l.length / 2 = 3 * (l.length / 2) + 1 by omega]
  exact one_moves l h _

/-! ## 9. The width steps up exactly after 3 2^k (#44) -/

/-- Width of the zoomed build: all blocks of one level are zoomed to the widest, so the width of
n >= 4 is 3 times the larger width of its blocks n/2 and (n+1)/2; the words 0..3 are 3 wide. -/
def W : ℕ → ℕ
  | 0 => 3
  | 1 => 3
  | 2 => 3
  | 3 => 3
  | n + 4 => 3 * max (W ((n + 4) / 2)) (W ((n + 5) / 2))
  decreasing_by all_goals omega

theorem W_step (n : ℕ) (h : 4 ≤ n) : W n = 3 * max (W (n / 2)) (W ((n + 1) / 2)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [W]

theorem W_bound (k : ℕ) : ∀ n, n ≤ 3 * 2 ^ k → W n ≤ 3 ^ (k + 1) ∧ (3 * 2 ^ k < 2 * n → W n = 3 ^ (k + 1)) := by
  induction k with
  | zero =>
    intro n hn
    simp at hn
    interval_cases n <;> simp [W]
  | succ k ih =>
    intro n hn
    have hp : 3 ^ (k + 1) ≤ 3 ^ (k + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have e2 : 3 * 2 ^ (k + 1) = 2 * (3 * 2 ^ k) := by ring
    have e3 : 3 ^ (k + 1 + 1) = 3 * 3 ^ (k + 1) := by ring
    rcases le_or_gt n (3 * 2 ^ k) with h | h
    · exact ⟨le_trans (ih n h).1 hp, fun h' => by omega⟩
    · have h3 : 3 ≤ 3 * 2 ^ k := by have := Nat.one_le_two_pow (n := k); omega
      rw [W_step n (by omega)]
      have a1 := (ih (n / 2) (by omega)).1
      have a2 := (ih ((n + 1) / 2) (by omega)).2 (by omega)
      rw [a2, max_eq_right a1, e3]
      exact ⟨le_rfl, fun _ => rfl⟩

/-- THE WIDTH STEPS UP EXACTLY AFTER 3 2^k (#44): for 3 2^k < n <= 3 2^(k+1) the width is 3^(k+2);
the words 1..3 are 3 wide. So 4-6: 9, 7-12: 27, 13-24: 81, 25-48: 243. -/
theorem width_closed (k n : ℕ) (h1 : 3 * 2 ^ k < n) (h2 : n ≤ 3 * 2 ^ (k + 1)) : W n = 3 ^ (k + 2) :=
  (W_bound (k + 1) n h2).2 (by rw [pow_succ]; omega)

theorem width_words (n : ℕ) (h : n ≤ 3) : W n = 3 := by interval_cases n <;> simp [W]

end Upgrades

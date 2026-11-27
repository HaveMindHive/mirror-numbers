import Mathlib
import MirrorNumbersAll.RuleHierarchy

/-!
# PySR finds (tUrUq's mirror numbers, 11-27-2026)

Exact laws found by PySR on exact data from his scripts, each matched on every training point and on a
held-out range, then proven here for every value. Log: `pysr-finds_v1.0_11-27-2026/pysr-finds-log_v1.0_11-27-2026.txt`.

* Row 109 (block r above the hand-off): over one full turn of the 6r-run, the first seat off 2 and 3 is an
  r-seat from exactly 2 of the 2(r-1) off classes, so the share is 1/(r-1) (every prime r >= 5); the stacked
  share over the full turn of 6*5*7 and 6*5*7*11 is 1/6 and 1/10 of what 5 (and 7) leave.
* Row 49 (ladder ends): the ladder of n >= 4 ends in 2|3 on [2^m, 3*2^(m-1)) and in 1|2 on [3*2^(m-1), 2^(m+1));
  its length is log2(n/3) + 1 (new statement, PySR).
* Row 92 (even-line primes): prime in the evens alone iff n = 2 mod 4 and n != 2; their count up to X is
  (X+2)/4 - 1 for X >= 2.
* Row 95 (depth): for every odd p the shallow side 2p -+ 2 has depth 2 and the deep side has depth
  1 + halvings of p -+ 1, deep on the left iff p = 1 mod 4.
* Row 71 (marks): the mark notation of the turn build of 3^k has 2*3^k - k - 2 symbols (new statement, PySR).

No sorry, no admit, no native_decide.
-/

namespace PySRFinds

open RuleHierarchy

/-! ## Row 109: block r takes 1/(r-1) over a full turn -/

theorem coprime_six_iff (c : ℕ) : Nat.Coprime c 6 ↔ c % 2 = 1 ∧ c % 3 ≠ 0 := by
  have h6 : (6 : ℕ) = 2 * 3 := rfl
  rw [h6, Nat.coprime_mul_iff_right, Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two,
    Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three, Nat.dvd_iff_mod_eq_zero,
    Nat.dvd_iff_mod_eq_zero]
  omega

theorem coprime_six_r_iff (r c : ℕ) (hr : r.Prime) :
    Nat.Coprime c (6 * r) ↔ c % 2 = 1 ∧ c % 3 ≠ 0 ∧ ¬ r ∣ c := by
  rw [Nat.coprime_mul_iff_right, coprime_six_iff, Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hr]
  tauto

/-- A number t with 0 < t < 2r is a multiple of r exactly when t = r. -/
theorem mod_zero_small (r t : ℕ) (h0 : 0 < t) (h1 : t < 2 * r) : t % r = 0 ↔ t = r := by
  constructor
  · intro h
    obtain ⟨m, hm⟩ := Nat.dvd_of_mod_eq_zero h
    rcases m with _ | _ | m
    · omega
    · omega
    · nlinarith
  · rintro rfl; exact Nat.mod_self t

/-- The off classes mod 6r number 2(r-1). -/
theorem off_classes (r : ℕ) (hr : r.Prime) (h5 : 5 ≤ r) :
    ((Finset.range (6 * r)).filter (fun c => Nat.Coprime c (6 * r))).card = 2 * (r - 1) := by
  have : ((Finset.range (6 * r)).filter (fun c => Nat.Coprime c (6 * r))) =
      (Finset.range (6 * r)).filter (Nat.Coprime (6 * r)) := by
    apply Finset.filter_congr; intro c _; exact Nat.coprime_comm
  rw [this, ← Nat.totient_eq_card_coprime, Nat.totient_mul, Nat.totient_prime hr]
  · rfl
  · rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hr]
    intro h
    rcases (Nat.Prime.dvd_mul hr).mp (show r ∣ 2 * 3 from h) with h' | h' <;>
      · have := Nat.le_of_dvd (by norm_num) h'; omega

/-- A residue t strictly between the walls 0 and r is not a multiple of r, past any number of whole r. -/
theorem not_dvd_off (r q t : ℕ) (h0 : 0 < t) (h1 : t < r) : ¬ r ∣ r * q + t := by
  rw [Nat.dvd_iff_mod_eq_zero, Nat.mul_add_mod, Nat.mod_eq_of_lt h1]; omega

/-- Row 109, one full turn of the 6r-run: the hand-off's first seat is an r-seat from exactly two off classes. -/
theorem above_classes (r : ℕ) (hr : r.Prime) (h5 : 5 ≤ r) :
    ((Finset.range (6 * r)).filter (fun c => Nat.Coprime c (6 * r) ∧ handOff c % r = 0)).card = 2 := by
  have hr2 : r % 2 = 1 := by rcases hr.eq_two_or_odd with h | h <;> omega
  have hr3 : r % 3 ≠ 0 := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).mp (Nat.dvd_of_mod_eq_zero h); omega
  -- the hand-off seat from c, written past whole r
  have seat : ∀ c, c < 6 * r → ¬ r ∣ c → c % 2 = 1 → c % 3 ≠ 0 → handOff c % r = 0 →
      ∃ q, q < 6 ∧ ((c % 6 = 1 ∧ c + 4 = r * (q + 1)) ∨ (c % 6 = 5 ∧ c + 2 = r * (q + 1))) := by
    intro c hc hnd h2 h3 hh
    have hq : c / r < 6 := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by linarith)
    have hcq := (Nat.div_add_mod c r).symm
    have hs := Nat.mod_lt c (by omega : 0 < r)
    have hs0 : c % r ≠ 0 := fun h => hnd (Nat.dvd_of_mod_eq_zero h)
    refine ⟨c / r, hq, ?_⟩
    unfold handOff at hh
    split_ifs at hh with h6
    · have e : c + 4 = r * (c / r) + (c % r + 4) := by omega
      rw [e, Nat.mul_add_mod, mod_zero_small r _ (by omega) (by omega)] at hh
      left; constructor
      · exact h6
      · rw [e, hh]; ring
    · have e : c + 2 = r * (c / r) + (c % r + 2) := by omega
      rw [e, Nat.mul_add_mod, mod_zero_small r _ (by omega) (by omega)] at hh
      right; constructor
      · omega
      · rw [e, hh]; ring
  have hcase : r % 6 = 1 ∨ r % 6 = 5 := by omega
  rcases hcase with h6 | h6
  · have : (Finset.range (6 * r)).filter (fun c => Nat.Coprime c (6 * r) ∧ handOff c % r = 0) =
        {r - 2, 5 * r - 4} := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_range, coprime_six_r_iff r c hr, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro ⟨hc, ⟨h2, h3, hnd⟩, hh⟩
        obtain ⟨q, hq, hq'⟩ := seat c hc hnd h2 h3 hh
        interval_cases q <;> omega
      · rintro (rfl | rfl)
        · refine ⟨by omega, ⟨by omega, by omega, ?_⟩, ?_⟩
          · have := not_dvd_off r 0 (r - 2) (by omega) (by omega); simpa using this
          · unfold handOff; rw [if_neg (by omega)]
            rw [show r - 2 + 2 = r by omega, Nat.mod_self]
        · refine ⟨by omega, ⟨by omega, by omega, ?_⟩, ?_⟩
          · have := not_dvd_off r 4 (r - 4) (by omega) (by omega)
            rwa [show r * 4 + (r - 4) = 5 * r - 4 by omega] at this
          · unfold handOff; rw [if_pos (by omega)]
            rw [show 5 * r - 4 + 4 = r * 5 by omega, Nat.mul_mod_right]
    rw [this, Finset.card_pair (by omega)]
  · have : (Finset.range (6 * r)).filter (fun c => Nat.Coprime c (6 * r) ∧ handOff c % r = 0) =
        {5 * r - 2, r - 4} := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_range, coprime_six_r_iff r c hr, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro ⟨hc, ⟨h2, h3, hnd⟩, hh⟩
        obtain ⟨q, hq, hq'⟩ := seat c hc hnd h2 h3 hh
        interval_cases q <;> omega
      · rintro (rfl | rfl)
        · refine ⟨by omega, ⟨by omega, by omega, ?_⟩, ?_⟩
          · have := not_dvd_off r 4 (r - 2) (by omega) (by omega)
            rwa [show r * 4 + (r - 2) = 5 * r - 2 by omega] at this
          · unfold handOff; rw [if_neg (by omega)]
            rw [show 5 * r - 2 + 2 = r * 5 by omega, Nat.mul_mod_right]
        · refine ⟨by omega, ⟨by omega, by omega, ?_⟩, ?_⟩
          · have := not_dvd_off r 0 (r - 4) (by omega) (by omega); simpa using this
          · unfold handOff; rw [if_pos (by omega)]
            rw [show r - 4 + 4 = r by omega, Nat.mod_self]
    rw [this, Finset.card_pair (by omega)]

/-- Row 109 as a share: over one full turn of the 6r-run the r rule sits above the hand-off on
exactly 1/(r-1) of the off classes (2 of 2(r-1)), for every prime r >= 5. -/
theorem above_share (r : ℕ) (hr : r.Prime) (h5 : 5 ≤ r) :
    (((Finset.range (6 * r)).filter (fun c => Nat.Coprime c (6 * r) ∧ handOff c % r = 0)).card : ℚ) /
      ((Finset.range (6 * r)).filter (fun c => Nat.Coprime c (6 * r))).card = 1 / (r - 1) := by
  rw [above_classes r hr h5, off_classes r hr h5]
  have : (1 : ℚ) ≤ r := by exact_mod_cast (by omega : 1 ≤ r)
  rw [Nat.cast_mul, Nat.cast_sub (by omega)]
  have hne : (r : ℚ) - 1 ≠ 0 := by
    have : (5 : ℚ) ≤ r := by exact_mod_cast h5
    linarith
  push_cast
  field_simp

/-- Row 109 stacked, full turn of 6*5*7 = 210: of the 36 off classes whose first seat is not a 5-seat,
the 7 rule takes 6, that is 1/6 = 1/(7-1). -/
theorem stack_seven :
    ((Finset.range 210).filter (fun c => Nat.Coprime c 210 ∧ handOff c % 5 ≠ 0)).card = 36 ∧
    ((Finset.range 210).filter (fun c => Nat.Coprime c 210 ∧ handOff c % 5 ≠ 0 ∧ handOff c % 7 = 0)).card = 6 := by
  decide +kernel

/-- Row 109 stacked, full turn of 6*5*7*11 = 2310: of the 300 off classes whose first seat is on
neither 5 nor 7, the 11 rule takes 30, that is 1/10 = 1/(11-1). -/
theorem stack_eleven :
    ((Finset.range 2310).filter (fun c => Nat.Coprime c 2310 ∧ handOff c % 5 ≠ 0 ∧ handOff c % 7 ≠ 0)).card = 300 ∧
    ((Finset.range 2310).filter (fun c => Nat.Coprime c 2310 ∧ handOff c % 5 ≠ 0 ∧ handOff c % 7 ≠ 0 ∧
      handOff c % 11 = 0)).card = 30 := by
  decide +kernel

/-! ## Row 49: where the ladder ends, and its length -/

/-- His ladder from the top pair k|k+1: halve k until the pair is made of words (k + 1 <= 3). -/
def ladderFrom (k : ℕ) : List (ℕ × ℕ) :=
  if k ≤ 2 then [(k, k + 1)] else (k, k + 1) :: ladderFrom (k / 2)
termination_by k
decreasing_by omega

/-- The ladder of n (ladder-shorthand script): pairs from n / 2 | n / 2 + 1 down. -/
def ladder (n : ℕ) : List (ℕ × ℕ) := ladderFrom (n / 2)

theorem ladderFrom_ne_nil (k : ℕ) : ladderFrom k ≠ [] := by
  rw [ladderFrom]; split_ifs <;> simp

theorem ladderFrom_big (k : ℕ) (hk : 3 ≤ k) : ladderFrom k = (k, k + 1) :: ladderFrom (k / 2) := by
  rw [ladderFrom, if_neg (by omega)]

theorem getLast_big (k : ℕ) (hk : 3 ≤ k) : (ladderFrom k).getLast? = (ladderFrom (k / 2)).getLast? := by
  rw [ladderFrom_big k hk]
  obtain ⟨y, l, hl⟩ := List.exists_cons_of_ne_nil (ladderFrom_ne_nil (k / 2))
  rw [hl, List.getLast?_cons_cons]

theorem ladderFrom_ends (m : ℕ) : ∀ k,
    (2 ^ (m + 1) ≤ k → k < 3 * 2 ^ m → (ladderFrom k).getLast? = some (2, 3)) ∧
    (3 * 2 ^ m ≤ k → k < 2 ^ (m + 2) → (ladderFrom k).getLast? = some (1, 2)) := by
  induction m with
  | zero =>
    intro k; constructor
    · intro h1 h2
      obtain rfl : k = 2 := by simp at h1 h2; omega
      rw [ladderFrom, if_pos (by omega)]; rfl
    · intro h1 h2
      obtain rfl : k = 3 := by simp at h1 h2; omega
      rw [getLast_big 3 (by omega), ladderFrom, if_pos (by omega)]; rfl
  | succ m ih =>
    intro k
    have p1 : 2 ^ (m + 1 + 1) = 2 * 2 ^ (m + 1) := by ring
    have p2 : 2 ^ (m + 1 + 2) = 2 * 2 ^ (m + 2) := by ring
    have p3 : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
    have p4 : 2 ^ (m + 2) = 4 * 2 ^ m := by ring
    have hpos : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    constructor
    · intro h1 h2
      rw [getLast_big k (by omega)]
      exact (ih (k / 2)).1 (by omega) (by omega)
    · intro h1 h2
      rw [getLast_big k (by omega)]
      exact (ih (k / 2)).2 (by omega) (by omega)

/-- Row 49, first range: for n from 2^M up to 3 2^(M-1) (M >= 2) the ladder ends in 2|3. -/
theorem ladder_ends_two_three (m n : ℕ) (h1 : 2 ^ (m + 2) ≤ n) (h2 : n < 3 * 2 ^ (m + 1)) :
    (ladder n).getLast? = some (2, 3) := by
  have p1 : 2 ^ (m + 2) = 2 * 2 ^ (m + 1) := by ring
  have p3 : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
  exact (ladderFrom_ends m (n / 2)).1 (by omega) (by omega)

/-- Row 49, second range: for n from 3 2^(M-1) up to 2^(M+1) (M >= 2) the ladder ends in 1|2. -/
theorem ladder_ends_one_two (m n : ℕ) (h1 : 3 * 2 ^ (m + 1) ≤ n) (h2 : n < 2 ^ (m + 3)) :
    (ladder n).getLast? = some (1, 2) := by
  have p1 : 2 ^ (m + 3) = 2 * 2 ^ (m + 2) := by ring
  have p3 : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
  exact (ladderFrom_ends m (n / 2)).2 (by omega) (by omega)

/-- Row 49, length (new statement, PySR floor(log2 n - 0.5868...) snapped to log2(n/3) + 1):
the ladder of every n >= 2 has log2(n / 3) + 1 pairs. -/
theorem ladder_length (n : ℕ) (hn : 2 ≤ n) : (ladder n).length = Nat.log 2 (n / 3) + 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hs : n ≤ 5
    · rw [ladder, ladderFrom, if_pos (by omega), Nat.log_of_lt (by omega)]; rfl
    · rw [ladder, ladderFrom_big (n / 2) (by omega), List.length_cons]
      have := ih (n / 2) (by omega) (by omega)
      rw [ladder] at this
      rw [this, show n / 2 / 3 = n / 3 / 2 by omega, Nat.log_div_base]
      have : 0 < Nat.log 2 (n / 3) := Nat.log_pos (by norm_num) (by omega)
      omega

/-! ## Row 92: primes inside the evens, a fixed quarter -/

/-- Prime inside the evens alone (even-primes script): even, not 2 (the 1 of the evens), and not a
product of an even a >= 2 below n with an even cofactor. -/
def evenWorldPrime (n : ℕ) : Prop :=
  n % 2 = 0 ∧ n ≠ 2 ∧ ¬ ∃ a ∈ Finset.range n, 2 ≤ a ∧ a % 2 = 0 ∧ n % a = 0 ∧ (n / a) % 2 = 0

instance : DecidablePred evenWorldPrime := fun n => by unfold evenWorldPrime; infer_instance

/-- The even-line primes are exactly the odd places 6, 10, 14, ... : n = 2 mod 4, n != 2. -/
theorem evenWorldPrime_iff (n : ℕ) (hn : 0 < n) : evenWorldPrime n ↔ n % 4 = 2 ∧ n ≠ 2 := by
  constructor
  · rintro ⟨h2, hne, hno⟩
    refine ⟨?_, hne⟩
    by_contra h4
    exact hno ⟨2, Finset.mem_range.mpr (by omega), le_refl 2, rfl, by omega, by omega⟩
  · rintro ⟨h4, hne⟩
    refine ⟨by omega, hne, ?_⟩
    rintro ⟨a, _, _, hae, hdiv, hqe⟩
    obtain ⟨x, hx⟩ : 2 ∣ a := Nat.dvd_of_mod_eq_zero hae
    obtain ⟨y, hy⟩ : 2 ∣ n / a := Nat.dvd_of_mod_eq_zero hqe
    have hn' : n = a * (n / a) := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hdiv)).symm
    have : n = 4 * (x * y) := by rw [hn', hy, hx]; ring
    omega

/-- Row 92: up to X >= 2 the even-line primes number (X+2)/4 - 1 (PySR floor(0.25 X - 0.37) snapped). -/
theorem even_world_count (X : ℕ) (hX : 2 ≤ X) :
    ((Finset.Icc 1 X).filter evenWorldPrime).card = (X + 2) / 4 - 1 := by
  induction X, hX using Nat.le_induction with
  | base => decide
  | succ X hX ih =>
    rw [← Finset.insert_Icc_right_eq_Icc_add_one (by omega), Finset.filter_insert]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (by simp), ih]
      rw [evenWorldPrime_iff _ (by omega)] at h
      omega
    · rw [ih]
      rw [evenWorldPrime_iff _ (by omega)] at h
      omega

/-! ## Row 95: depth of the deep side -/

/-- p = 1 mod 4 (p >= 5): the right side 2p+2 is shallow (depth 2), the left side 2p-2 is deep,
depth = 1 + halvings of p - 1, at least 3. -/
theorem depth_one_mod_four (p : ℕ) (hp : p % 4 = 1) (h5 : 5 ≤ p) :
    padicValNat 2 (2 * p + 2) = 2 ∧ padicValNat 2 (2 * p - 2) = padicValNat 2 (p - 1) + 1 ∧
      3 ≤ padicValNat 2 (2 * p - 2) := by
  have hA : 2 * p + 2 = 2 ^ 2 * ((p + 1) / 2) := by omega
  have hodd : ¬ 2 ∣ (p + 1) / 2 := by omega
  have hB : 2 * p - 2 = 2 * (p - 1) := by omega
  have hv : padicValNat 2 (2 * p - 2) = padicValNat 2 (p - 1) + 1 := by
    rw [hB, padicValNat.mul (by norm_num) (by omega), padicValNat.self (by norm_num)]; ring
  refine ⟨?_, hv, ?_⟩
  · rw [hA, padicValNat.mul (by norm_num) (by omega), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hodd]
  · have : 2 ≤ padicValNat 2 (p - 1) :=
      (padicValNat_dvd_iff_le (by omega)).mp (by
        obtain ⟨k, hk⟩ : ∃ k, p - 1 = 4 * k := ⟨(p - 1) / 4, by omega⟩
        rw [hk]; exact Dvd.intro k rfl)
    omega

/-- p = 3 mod 4: the left side 2p-2 is shallow (depth 2), the right side 2p+2 is deep,
depth = 1 + halvings of p + 1, at least 3. -/
theorem depth_three_mod_four (p : ℕ) (hp : p % 4 = 3) :
    padicValNat 2 (2 * p - 2) = 2 ∧ padicValNat 2 (2 * p + 2) = padicValNat 2 (p + 1) + 1 ∧
      3 ≤ padicValNat 2 (2 * p + 2) := by
  have hA : 2 * p - 2 = 2 ^ 2 * ((p - 1) / 2) := by omega
  have hodd : ¬ 2 ∣ (p - 1) / 2 := by omega
  have hB : 2 * p + 2 = 2 * (p + 1) := by omega
  have hv : padicValNat 2 (2 * p + 2) = padicValNat 2 (p + 1) + 1 := by
    rw [hB, padicValNat.mul (by norm_num) (by omega), padicValNat.self (by norm_num)]; ring
  refine ⟨?_, hv, ?_⟩
  · rw [hA, padicValNat.mul (by norm_num) (by omega), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hodd]
  · have : 2 ≤ padicValNat 2 (p + 1) :=
      (padicValNat_dvd_iff_le (by omega)).mp (by
        obtain ⟨k, hk⟩ : ∃ k, p + 1 = 4 * k := ⟨(p + 1) / 4, by omega⟩
        rw [hk]; exact Dvd.intro k rfl)
    omega

/-! ## Row 71: symbol count of the turn mark notation on 3^k -/

/-- Notation A (two-mirrors script) of the turn build of 3^(h+1): the word 111 for 3, and each level
X|,Y|,Z| with h+1 commas after the first two marks; the three copies of 3^h are equal (3^(h+1) = 3 * 3^h + 0). -/
def markT : ℕ → List Char
  | 0 => ['1', '1', '1']
  | h + 1 =>
    markT h ++ ['|'] ++ List.replicate (h + 1) ',' ++ markT h ++ ['|'] ++ List.replicate (h + 1) ',' ++
      markT h ++ ['|']

/-- Row 71 length law (new statement, PySR (2.998^k - 1.024)/0.498 - k snapped to 2 3^k - k - 2):
notation A of the turn build of 3^k has 2 3^k - k - 2 symbols (k = h + 1 >= 1). -/
theorem markT_length (h : ℕ) : (markT h).length + (h + 1) + 2 = 2 * 3 ^ (h + 1) := by
  induction h with
  | zero => rfl
  | succ h ih =>
    simp only [markT, List.length_append, List.length_replicate, List.length_cons, List.length_nil]
    rw [pow_succ]; omega

theorem markT_27 : (markT 2).length = 49 := by
  have := markT_length 2; norm_num at this; omega

end PySRFinds

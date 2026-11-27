import Mathlib

/-!
# Unit counting laws (tUrUq, 11-24-2026)

1. Even-period law (2 and 5 through 10) and its odd-period converse.
2. Mirror remainders (mod 9 and mod 11 of a digit list and its reverse).
3. Carry level law (top 2-adic level in (x, y] is Nat.log 2 (x ^^^ y), hit once).
4. Triaxial counting (binary palindromes, one per weight, only at L = 1, 3).
-/

namespace UnitCountingLaws

/-! ## 1. Even-period law -/

/-- In any commutative monoid, the order of `a * b` divides `lcm (orderOf a) (orderOf b)`. -/
theorem orderOf_mul_dvd_lcm' {M : Type*} [CommMonoid M] (a b : M) :
    orderOf (a * b) ∣ Nat.lcm (orderOf a) (orderOf b) := by
  apply orderOf_dvd_of_pow_eq_one
  rw [mul_pow, orderOf_dvd_iff_pow_eq_one.mp (Nat.dvd_lcm_left _ _),
    orderOf_dvd_iff_pow_eq_one.mp (Nat.dvd_lcm_right _ _), one_mul]

/-- General form: if `a` and `b` both have odd order, so does `a * b`. -/
theorem odd_orderOf_mul {M : Type*} [CommMonoid M] (a b : M)
    (ha : Odd (orderOf a)) (hb : Odd (orderOf b)) : Odd (orderOf (a * b)) := by
  have hl : Odd (Nat.lcm (orderOf a) (orderOf b)) :=
    Nat.odd_iff.mpr (by
      have := Nat.lcm_dvd_mul (orderOf a) (orderOf b)
      have hm : Odd (orderOf a * orderOf b) := ha.mul hb
      exact Nat.odd_iff.mp (Odd.of_dvd_nat hm this))
  exact Odd.of_dvd_nat hl (orderOf_mul_dvd_lcm' a b)

/-- EVEN-PERIOD LAW. For a prime `p` not dividing 10: if 2 and 5 both have odd order
mod `p`, then 10 has odd order. (Contrapositive: an even decimal period means 2 and 5
are never both odd-order.) -/
theorem even_period_law (p : ℕ) [Fact p.Prime] (_hp : ¬ p ∣ 10)
    (h2 : Odd (orderOf (2 : ZMod p))) (h5 : Odd (orderOf (5 : ZMod p))) :
    Odd (orderOf (10 : ZMod p)) := by
  have : (10 : ZMod p) = 2 * 5 := by norm_num
  rw [this]
  exact odd_orderOf_mul _ _ h2 h5

/-- Contrapositive wording: even decimal period → not both odd. -/
theorem even_period_never_both_odd (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ 10)
    (h10 : Even (orderOf (10 : ZMod p))) :
    ¬ (Odd (orderOf (2 : ZMod p)) ∧ Odd (orderOf (5 : ZMod p))) := by
  rintro ⟨h2, h5⟩
  exact (Nat.not_even_iff_odd.mpr (even_period_law p hp h2 h5)) h10

/-- Key step: if `a*b` has order `k`, then `orderOf b ∣ k * orderOf a`. -/
theorem orderOf_dvd_mul_of_mul {M : Type*} [CommMonoid M] (a b : M) :
    orderOf b ∣ orderOf (a * b) * orderOf a := by
  apply orderOf_dvd_of_pow_eq_one
  have h1 : (a * b) ^ (orderOf (a * b) * orderOf a) = 1 := by
    rw [pow_mul, pow_orderOf_eq_one, one_pow]
  have h2 : a ^ (orderOf (a * b) * orderOf a) = 1 := by
    rw [mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
  rw [mul_pow, h2, one_mul] at h1
  exact h1

/-- General form of the converse: if `a*b` has odd order and `a`, `b` have finite
(nonzero) order, then `v₂(ord a) = v₂(ord b)`. -/
theorem padicValNat_two_orderOf_eq {M : Type*} [CommMonoid M] (a b : M)
    (ha : orderOf a ≠ 0) (hb : orderOf b ≠ 0) (hab : Odd (orderOf (a * b))) :
    padicValNat 2 (orderOf a) = padicValNat 2 (orderOf b) := by
  have hk : orderOf (a * b) ≠ 0 := by
    rintro h; rw [h] at hab; exact (Nat.not_odd_zero) hab
  have hv : padicValNat 2 (orderOf (a * b)) = 0 :=
    padicValNat.eq_zero_of_not_dvd (by
      intro h; exact (Nat.not_even_iff_odd.mpr hab) (even_iff_two_dvd.mpr h))
  have key : ∀ x y : M, orderOf x ≠ 0 → orderOf y ≠ 0 → orderOf (x * y) ≠ 0 →
      padicValNat 2 (orderOf (x * y)) = 0 →
      padicValNat 2 (orderOf y) ≤ padicValNat 2 (orderOf x) := by
    intro x y hx hy hxy hv
    have hd := orderOf_dvd_mul_of_mul x y
    have := (padicValNat_dvd_iff_le (p := 2) (mul_ne_zero hxy hx)).mp
      (dvd_trans (pow_padicValNat_dvd (p := 2)) hd)
    rwa [padicValNat.mul hxy hx, hv, zero_add] at this
  apply le_antisymm
  · have := key b a hb ha (by rwa [mul_comm]) (by rwa [mul_comm])
    exact this
  · exact key a b ha hb hk hv

/-- ODD-PERIOD LAW (converse direction). For a prime `p ∤ 10`, if 10 has odd order
mod `p`, then the 2-adic valuations of the orders of 2 and 5 are equal. -/
theorem odd_period_law (p : ℕ) [hp : Fact p.Prime] (h : ¬ p ∣ 10)
    (h10 : Odd (orderOf (10 : ZMod p))) :
    padicValNat 2 (orderOf (2 : ZMod p)) = padicValNat 2 (orderOf (5 : ZMod p)) := by
  have hne : ∀ n : ℕ, n ∣ 10 → ((n : ℕ) : ZMod p) ≠ 0 := by
    intro n hn h0
    rw [ZMod.natCast_eq_zero_iff] at h0
    exact h (dvd_trans h0 hn)
  have hpos : ∀ x : ZMod p, x ≠ 0 → orderOf x ≠ 0 := by
    intro x hx h0
    have := orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hx)
    rw [h0, zero_dvd_iff] at this
    have := hp.out.two_le
    omega
  have h2 : (2 : ZMod p) ≠ 0 := by exact_mod_cast hne 2 (by norm_num)
  have h5 : (5 : ZMod p) ≠ 0 := by exact_mod_cast hne 5 (by norm_num)
  have e : (10 : ZMod p) = 2 * 5 := by norm_num
  rw [e] at h10
  exact padicValNat_two_orderOf_eq _ _ (hpos _ h2) (hpos _ h5) h10

/-! ## 2. Mirror remainders -/

theorem mirror_mod_nine (ds : List ℕ) :
    Nat.ofDigits 10 ds % 9 = Nat.ofDigits 10 ds.reverse % 9 := by
  rw [Nat.ofDigits_mod, Nat.ofDigits_mod 10 9 ds.reverse]
  norm_num [Nat.ofDigits_one, List.sum_reverse]

theorem ofDigits_ten_modEq_eleven (ds : List ℕ) :
    ((Nat.ofDigits 10 ds : ℕ) : ℤ) ≡ (ds.map (fun n : ℕ => (n : ℤ))).alternatingSum [ZMOD 11] := by
  have h1 : ((Nat.ofDigits 10 ds : ℕ) : ℤ) = Nat.ofDigits (10 : ℤ) ds := by
    rw [Nat.coe_ofDigits]; rfl
  rw [h1, ← Nat.ofDigits_neg_one]
  have h2 := Nat.ofDigits_zmodeq (-1 : ℤ) 11 ds
  norm_num at h2
  exact h2.symm

theorem mirror_mod_eleven (ds : List ℕ) :
    ((Nat.ofDigits 10 ds : ℕ) : ℤ) ≡
      (-1) ^ (ds.length + 1) * ((Nat.ofDigits 10 ds.reverse : ℕ) : ℤ) [ZMOD 11] := by
  have hn := ofDigits_ten_modEq_eleven ds
  have hr := ofDigits_ten_modEq_eleven ds.reverse
  rw [List.map_reverse, List.alternatingSum_reverse, List.length_map, zsmul_eq_mul, Int.cast_id] at hr
  have hr' := hr.mul_left ((-1 : ℤ) ^ (ds.length + 1))
  have hsq : ((-1 : ℤ) ^ (ds.length + 1)) * ((-1 : ℤ) ^ (ds.length + 1)) = 1 := by
    rw [← mul_pow]; norm_num
  rw [← mul_assoc, hsq, one_mul] at hr'
  exact hn.trans hr'.symm

/-- Odd length: n ≡ r (mod 11). -/
theorem mirror_mod_eleven_odd (ds : List ℕ) (h : Odd ds.length) :
    ((Nat.ofDigits 10 ds : ℕ) : ℤ) ≡ ((Nat.ofDigits 10 ds.reverse : ℕ) : ℤ) [ZMOD 11] := by
  have := mirror_mod_eleven ds
  rwa [(Nat.even_add_one.mpr (Nat.not_even_iff_odd.mpr h)).neg_one_pow, one_mul] at this

/-- Even length: n ≡ -r (mod 11). -/
theorem mirror_mod_eleven_even (ds : List ℕ) (h : Even ds.length) :
    ((Nat.ofDigits 10 ds : ℕ) : ℤ) ≡ -((Nat.ofDigits 10 ds.reverse : ℕ) : ℤ) [ZMOD 11] := by
  have := mirror_mod_eleven ds
  rwa [(Nat.odd_add_one.mpr (Nat.not_odd_iff_even.mpr h)).neg_one_pow, neg_one_mul] at this

/-! ## 3. Carry level law -/

/-- With `k = Nat.log 2 (x ^^^ y)` and `x ≠ y`: `x`, `y` agree above bit `k`
and differ at level `k`. -/
theorem xor_log_split (x y : ℕ) (hxy : x ≠ y) :
    x / 2 ^ (Nat.log 2 (x ^^^ y) + 1) = y / 2 ^ (Nat.log 2 (x ^^^ y) + 1) ∧
    x / 2 ^ Nat.log 2 (x ^^^ y) ≠ y / 2 ^ Nat.log 2 (x ^^^ y) := by
  set k := Nat.log 2 (x ^^^ y) with hk
  have hlt : x ^^^ y < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hne : x ^^^ y ≠ 0 := by
    intro h0
    apply hxy
    apply Nat.eq_of_testBit_eq
    intro i
    have := Nat.testBit_xor x y i
    rw [h0, Nat.zero_testBit] at this
    cases hx : x.testBit i <;> cases hy : y.testBit i <;> simp_all
  have hge : 2 ^ k ≤ x ^^^ y := Nat.pow_log_le_self 2 hne
  constructor
  · rw [← Nat.shiftRight_eq_div_pow, ← Nat.shiftRight_eq_div_pow]
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_shiftRight, Nat.testBit_shiftRight]
    have h := Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt
      (Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right (k + 1) i)))
    rw [Nat.testBit_xor] at h
    cases hx : x.testBit (k + 1 + i) <;> cases hy : y.testBit (k + 1 + i) <;> simp_all
  · intro heq
    rw [← Nat.shiftRight_eq_div_pow, ← Nat.shiftRight_eq_div_pow] at heq
    have : x ^^^ y < 2 ^ k := by
      apply Nat.lt_pow_two_of_testBit
      intro i hi
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
      have := congrArg (fun t => Nat.testBit t j) heq
      simp only [Nat.testBit_shiftRight] at this
      rw [Nat.testBit_xor, this]; simp
    omega

/-- CARRY LEVEL LAW. For `x < y`, every integer in `(x, y]` has 2-adic valuation at most
`Nat.log 2 (x ^^^ y)`, and exactly one integer in `(x, y]` attains it. -/
theorem carry_level_law (x y : ℕ) (hxy : x < y) :
    (∀ z, x < z → z ≤ y → padicValNat 2 z ≤ Nat.log 2 (x ^^^ y)) ∧
    ∃! m, x < m ∧ m ≤ y ∧ padicValNat 2 m = Nat.log 2 (x ^^^ y) := by
  obtain ⟨hup, hlow⟩ := xor_log_split x y hxy.ne
  set k := Nat.log 2 (x ^^^ y)
  set d := 2 ^ k with hd
  have hdpos : 0 < d := by positivity
  have h2d : 2 ^ (k + 1) = d * 2 := by rw [pow_succ]
  rw [h2d, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul] at hup
  have hxd : x / d < y / d := lt_of_le_of_ne (Nat.div_le_div_right hxy.le) hlow
  have hyd : y / d = x / d + 1 := by omega
  -- multiples of d in (x, y] are exactly y / d * d
  have hmul : ∀ c, x < d * c → d * c ≤ y → c = y / d := by
    intro c h1 h2
    have a1 : c ≤ y / d := (Nat.le_div_iff_mul_le hdpos).mpr (by linarith)
    have a2 : x / d < c := (Nat.div_lt_iff_lt_mul hdpos).mpr (by linarith)
    omega
  have hle : ∀ z, x < z → z ≤ y → padicValNat 2 z ≤ k := by
    intro z h1 h2
    by_contra hc
    push Not at hc
    have hz : z ≠ 0 := by omega
    have hdvd : 2 ^ (k + 1) ∣ z := (padicValNat_dvd_iff_le hz).mpr hc
    obtain ⟨c, rfl⟩ := hdvd
    rw [h2d, mul_assoc] at h1 h2
    have := hmul _ h1 h2
    have hev : y / d = 2 * c := by omega
    omega
  refine ⟨hle, y / d * d, ⟨?_, Nat.div_mul_le_self y d, ?_⟩, ?_⟩
  · have := Nat.lt_div_mul_add hdpos (a := x)
    nlinarith
  · apply le_antisymm
    · exact hle _ (by have := Nat.lt_div_mul_add hdpos (a := x); nlinarith)
        (Nat.div_mul_le_self y d)
    · have hm0 : y / d * d ≠ 0 := by
        have : 0 < y / d := by rw [hyd]; exact Nat.succ_pos _
        positivity
      exact (padicValNat_dvd_iff_le hm0).mp (Dvd.intro_left _ rfl)
  · rintro z ⟨h1, h2, h3⟩
    have hz : z ≠ 0 := by omega
    obtain ⟨c, rfl⟩ := (padicValNat_dvd_iff_le hz).mpr h3.ge
    rw [hmul c h1 h2, mul_comm]

/-! ## 4. Triaxial counting -/

/-- All binary words of length `L`. -/
def allWords : ℕ → List (List Bool)
  | 0 => [[]]
  | L + 1 => (allWords L).flatMap (fun w => [false :: w, true :: w])

theorem mem_allWords (L : ℕ) (w : List Bool) : w ∈ allWords L ↔ w.length = L := by
  induction L generalizing w with
  | zero => cases w <;> simp [allWords]
  | succ L ih =>
    cases w with
    | nil => simp [allWords]
    | cons b w => cases b <;> simp [allWords, ih]

theorem nodup_allWords (L : ℕ) : (allWords L).Nodup := by
  induction L with
  | zero => simp [allWords]
  | succ L ih =>
    rw [allWords, List.nodup_flatMap]
    refine ⟨fun w _ => by simp, ?_⟩
    refine List.Pairwise.imp_of_mem ?_ ih
    intro a b _ _ hab
    simp [List.disjoint_left]
    intro h
    exact hab h

/-- Number of binary palindromes of length `L` with exactly `w` ones. -/
def palCount (L w : ℕ) : ℕ :=
  ((allWords L).filter (fun x => x.reverse == x && x.count true == w)).length

/-- `L` is triaxial: exactly one palindrome of each weight `0..L`. -/
def isTriaxial (L : ℕ) : Bool := (List.range (L + 1)).all (fun w => palCount L w == 1)

theorem isTriaxial_iff (L : ℕ) : isTriaxial L = true ↔ ∀ w ≤ L, palCount L w = 1 := by
  simp [isTriaxial]

/-- TRIAXIAL COUNTING, finite check: among L = 1..8, only L = 1 and L = 3 are triaxial. -/
theorem triaxial_one_to_eight : (List.range' 1 8).filter isTriaxial = [1, 3] := by
  decide +kernel

theorem triaxial_one : ∀ w ≤ 1, palCount 1 w = 1 := (isTriaxial_iff 1).mp (by decide +kernel)
theorem triaxial_three : ∀ w ≤ 3, palCount 3 w = 1 := (isTriaxial_iff 3).mp (by decide +kernel)

theorem not_triaxial_two_to_eight (L : ℕ) (h2 : 2 ≤ L) (h8 : L ≤ 8) (h3 : L ≠ 3) :
    ¬ ∀ w ≤ L, palCount L w = 1 := by
  rw [← isTriaxial_iff]
  interval_cases L <;> first | decide +kernel | exact absurd rfl h3

/-- General: for every `L ≥ 4` there are at least two palindromes of weight 2
(`1 0…0 1` and `0 1 0…0 1 0`), so `L` is not triaxial. -/
theorem two_le_palCount_two (L : ℕ) (h : 4 ≤ L) : 2 ≤ palCount L 2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' h
  set w1 : List Bool := true :: (List.replicate (m + 2) false ++ [true])
  set w2 : List Bool := false :: true :: (List.replicate m false ++ [true, false])
  have hsub : [w1, w2] ⊆
      (allWords (m + 4)).filter (fun x => x.reverse == x && x.count true == 2) := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rw [List.mem_filter, mem_allWords]
    rcases hx with rfl | rfl
    · simp [w1, List.count_replicate]
    · simp [w2, List.count_replicate]
  have hnd : [w1, w2].Nodup := by simp [w1, w2]
  have := (List.subperm_of_subset hnd hsub).length_le
  simpa [palCount] using this

theorem not_triaxial_of_four_le (L : ℕ) (h : 4 ≤ L) : ¬ ∀ w ≤ L, palCount L w = 1 := by
  intro hall
  have := two_le_palCount_two L h
  rw [hall 2 (by omega)] at this
  omega

/-- FULL CLASSIFICATION: exactly one palindrome of each weight `0..L` holds only for
`L = 0` (the empty word, trivially), `L = 1` and `L = 3`. -/
theorem triaxial_iff (L : ℕ) : (∀ w ≤ L, palCount L w = 1) ↔ L = 0 ∨ L = 1 ∨ L = 3 := by
  constructor
  · intro hall
    by_contra hc
    by_cases h4 : 4 ≤ L
    · exact not_triaxial_of_four_le L h4 hall
    · have : L = 2 := by omega
      subst this
      exact absurd (hall 1 (by norm_num)) (by decide +kernel)
  · rintro (rfl | rfl | rfl)
    · exact (isTriaxial_iff 0).mp (by decide +kernel)
    · exact triaxial_one
    · exact triaxial_three

end UnitCountingLaws

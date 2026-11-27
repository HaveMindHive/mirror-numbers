import Main
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import TauCeti.NumberTheory.LSeries.SmoothedSum.ZeroFreeRegion
import TauCeti.NumberTheory.LSeries.RiemannZeta.LogDeriv.RightOfCurve
import TauCeti.NumberTheory.Chebyshev.PsiSubTheta
import TauCeti.NumberTheory.Chebyshev.ThetaTransfer

/-!
# The walls meet the proved Riemann hypothesis (11-27-2026)

One file, one environment, every step kernel-checked.

* Turaq Rayn-McLean's wall count `prime_count_walls`, ported from `MirrorNumbersAll`:
  for `N ≥ 3`, `π(N) = 2 + #{n ≤ N that pass the wall test}`.
* `riemannHypothesis` (from `Main`, the locally built community proof).
* A consequence of RH, proved here from it: `ζ′/ζ = O(log t)` on `Re s ≥ 3/4`
  (`logDeriv_bound_of_RH`), then through Tau Ceti's Ingham transfer theorem
  `|ψ(x) - x| ≤ C x^(1-δ)` for some `δ > 0` (`psi_sub_le_rpow_of_RH`), the same for `θ`, and
  `|π(x) - Li(x)| ≤ C x^(1-δ)` (`primeCounting_sub_logIntegral_le_rpow_of_RH`).
* `walls_meet_rh`: the wall count is within `C N^(1-δ)` of `Li(N)`.

The exponent `δ` is positive but not the `1/2` of the classical RH bound `O(√x log² x)`:
the transfer theorem available in Tau Ceti loses a constant factor in the exponent.
-/

open Complex

namespace WallsMeetRH

theorem wing_identity (k kr f fr : ℤ) (hfr : fr * fr = 1) :
    6 * k + f = 6 * (k - f * fr * kr) + f * fr * (6 * kr + fr) := by
  linear_combination (-f) * hfr

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

theorem prime_seat (q : ℕ) (hq : q.Prime) (h5 : 5 ≤ q) : q % 6 = 1 ∨ q % 6 = 5 := by
  by_contra h
  have h23 : 2 ∣ q ∨ 3 ∣ q := by omega
  rcases h23 with h2 | h3
  · have := (Nat.Prime.eq_one_or_self_of_dvd hq 2 h2); omega
  · have := (Nat.Prime.eq_one_or_self_of_dvd hq 3 h3); omega

theorem wall_walk_seat (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
    ∃ k f : ℤ, (f = 1 ∨ f = -1) ∧ (p : ℤ) = 6 * k + f := by
  rcases prime_seat p hp h5 with h | h
  · exact ⟨(p : ℤ) / 6, 1, Or.inl rfl, by omega⟩
  · exact ⟨(p : ℤ) / 6 + 1, -1, Or.inr rfl, by omega⟩

theorem seat_coprime (j g : ℤ) (hg : g = 1 ∨ g = -1) : IsCoprime (6 * j + g) 6 := by
  rcases hg with rfl | rfl
  · exact ⟨1, -j, by ring⟩
  · exact ⟨-1, j, by ring⟩

/-- His wall formula: a seat `n = 6k + f` (`f = ±1`, `n ≥ 5`) is prime exactly when no block
`6j + g` (`j ≥ 1`, `g = ±1`) with `(6j + g)^2 ≤ n` divides `k - f g j`. -/
theorem wall_formula (k f : ℤ) (hf : f = 1 ∨ f = -1) (n : ℕ) (hn : (n : ℤ) = 6 * k + f)
    (h5 : 5 ≤ n) :
    n.Prime ↔ ∀ j g : ℤ, 1 ≤ j → (g = 1 ∨ g = -1) → (6 * j + g) * (6 * j + g) ≤ n →
      ¬ (6 * j + g) ∣ k - f * g * j := by
  constructor
  · intro hp j g hj hg hsq hd
    have hgg : g * g = 1 := by rcases hg with rfl | rfl <;> norm_num
    have h1 : (6 * j + g) ∣ (n : ℤ) := by
      rw [hn]; exact (wing_closed k j f g hgg (seat_coprime j g hg)).2 hd
    have hpos : 5 ≤ 6 * j + g := by rcases hg with rfl | rfl <;> omega
    obtain ⟨t, ht⟩ : ∃ t : ℕ, (t : ℤ) = 6 * j + g :=
      ⟨(6 * j + g).toNat, Int.toNat_of_nonneg (by omega)⟩
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
    have hm2 : m ≠ 2 := by intro h; rw [h] at hmd; omega
    have hm3 : m ≠ 3 := by intro h; rw [h] at hmd; omega
    have hm5 : 5 ≤ m := by
      have := hmp.two_le
      rcases (show m = 2 ∨ m = 3 ∨ m = 4 ∨ 5 ≤ m by omega) with h | h | h | h
      · exact absurd h hm2
      · exact absurd h hm3
      · rw [h] at hmp; exact absurd hmp (by decide)
      · exact h
    have hseat := prime_seat m hmp hm5
    set j : ℤ := ((m : ℤ) + 1) / 6 with hj
    set g : ℤ := (m : ℤ) - 6 * j with hgdef
    have hg : g = 1 ∨ g = -1 := by rcases hseat with h | h <;> omega
    have hgg : g * g = 1 := by rcases hg with h | h <;> rw [h] <;> norm_num
    have hme : (m : ℤ) = 6 * j + g := by omega
    have hj1 : 1 ≤ j := by omega
    have hdz : (6 * j + g) ∣ 6 * k + f := by
      rw [← hme, ← hn]; exact Int.natCast_dvd_natCast.2 hmd
    have hd := (wing_closed k j f g hgg (seat_coprime j g hg)).1 hdz
    refine hall j g hj1 hg ?_ hd
    rw [← hme]; exact_mod_cast (by nlinarith : m * m ≤ n)

/-- The wall test: `n ≥ 5` is a seat `6k + f` whose wall `k` is closed by no block `6j + g`
with `(6j + g)^2 ≤ n`. -/
def passes (n : ℕ) : Prop := 5 ≤ n ∧ ∃ k f : ℤ, (f = 1 ∨ f = -1) ∧ (n : ℤ) = 6 * k + f ∧
  ∀ j g : ℤ, 1 ≤ j → (g = 1 ∨ g = -1) → (6 * j + g) * (6 * j + g) ≤ n →
    ¬ (6 * j + g) ∣ k - f * g * j

theorem prime_iff_passes (n : ℕ) : n.Prime ↔ n = 2 ∨ n = 3 ∨ passes n := by
  constructor
  · intro hp
    have h2 := hp.two_le
    rcases (show n = 2 ∨ n = 3 ∨ n = 4 ∨ 5 ≤ n by omega) with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · subst h; norm_num at hp
    · right; right
      obtain ⟨k, f, hf, hn⟩ := wall_walk_seat n hp h
      exact ⟨h, k, f, hf, hn, (wall_formula k f hf n hn h).1 hp⟩
  · rintro (rfl | rfl | ⟨h5, k, f, hf, hn, ht⟩)
    · norm_num
    · norm_num
    · exact (wall_formula k f hf n hn h5).2 ht

open Classical in
/-- His wall count: for `N ≥ 3`, the number of primes up to `N` is `2` (the two mirrors)
plus the number of `n ≤ N` that pass the wall test. -/
theorem prime_count_walls (N : ℕ) (hN : 3 ≤ N) :
    Nat.primeCounting N = 2 + ((Finset.range (N + 1)).filter passes).card := by
  have h0 : Nat.primeCounting N = ((Finset.range (N + 1)).filter Nat.Prime).card := by
    rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  rw [h0]
  have h1 : (Finset.range (N + 1)).filter Nat.Prime =
      (Finset.range (N + 1)).filter (fun n => n = 2 ∨ n = 3) ∪
        (Finset.range (N + 1)).filter passes := by
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


/-- From the proved `riemannHypothesis`: `ζ(s) ≠ 0` for `Re s > 1/2`. -/
theorem riemannZeta_ne_zero_of_half_lt {s : ℂ} (hs : 1 / 2 < s.re) : riemannZeta s ≠ 0 := by
  intro h0
  rcases eq_or_ne s 1 with rfl | hs1
  · exact riemannZeta_one_ne_zero h0
  have htriv : ¬ ∃ n : ℕ, s = -2 * (n + 1) := by
    rintro ⟨n, rfl⟩
    have : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
    rw [this] at hs
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  have := riemannHypothesis s h0 htriv hs1
  linarith

/-! Copies of two private lemmas of Tau Ceti's `RightOfCurve.lean` (Apache 2.0). -/

private lemma norm_logDeriv_add_one_div_le_of_le_re' {CN : ℝ}
    (hNear : ∀ {η : ℝ}, 0 < η → η ≤ 1 → -(logDeriv riemannZeta (1 + η)).re ≤ η⁻¹ + CN)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) {w : ℂ} (hw : 1 + η ≤ w.re) :
    ‖deriv riemannZeta w / riemannZeta w + 1 / (w - 1)‖ ≤ 2 * η⁻¹ + CN := by
  have h1 : ‖deriv riemannZeta w / riemannZeta w‖ ≤ η⁻¹ + CN := by
    rw [← logDeriv_apply]
    have hcmp : ‖logDeriv riemannZeta w‖ ≤ -(logDeriv riemannZeta ((1 + η : ℝ) : ℂ)).re := by
      simpa [DirichletCharacter.LFunction_modOne_eq] using
        (1 : DirichletCharacter ℂ 1).norm_logDeriv_LFunction_le_of_le_re (by linarith) hw
    refine hcmp.trans ?_
    have := hNear hη hη1
    push_cast
    linarith
  have h2 : ‖1 / (w - 1)‖ ≤ η⁻¹ := by
    rw [norm_div, norm_one, one_div]
    refine inv_anti₀ hη ?_
    have := re_le_norm (w - 1)
    rw [sub_re, one_re] at this
    linarith
  linarith [norm_add_le (deriv riemannZeta w / riemannZeta w) (1 / (w - 1))]

private lemma norm_one_div_sub_sub_one_div_sub_le' {s s₁ ρ : ℂ} {a η : ℝ} (ha : 0 < a)
    (hη : 0 < η) (hs₁re : s₁.re = 1 + η) (hs₁im : s₁.im = s.im) (hs : 1 - a ≤ s.re)
    (hs' : s.re < 1 + η) (hρ : ρ.re ≤ 1 - 2 * a) :
    ‖1 / (s - ρ) - 1 / (s₁ - ρ)‖ ≤ (2 + η / a) * (1 / (s₁ - ρ)).re := by
  set u := s - ρ
  set v := s₁ - ρ
  have hure : a ≤ u.re := by simp only [u, sub_re]; linarith
  have hvre : η + 2 * a ≤ v.re := by simp only [v, sub_re]; linarith
  have hu : a ≤ ‖u‖ := hure.trans (re_le_norm u)
  have hu0 : u ≠ 0 := norm_pos_iff.mp (ha.trans_le hu)
  have hv0 : v ≠ 0 := fun h ↦ by simp [h] at hvre; linarith
  have hvu : v - u = ((1 + η - s.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [u, v, hs₁re, hs₁im]
  have hd : ‖v - u‖ = 1 + η - s.re := by
    rw [hvu, norm_real, Real.norm_of_nonneg (by linarith)]
  have hvle : ‖v‖ ≤ ‖u‖ + (1 + η - s.re) := by
    have := norm_add_le u (v - u)
    rwa [add_sub_cancel, hd] at this
  have hkey : (1 + η - s.re) * ‖v‖ ≤ (2 + η / a) * v.re * ‖u‖ := by
    have h1 : 1 + η - s.re ≤ v.re := by linarith
    have h2 : ‖v‖ ≤ (2 + η / a) * ‖u‖ := by
      have : η + a ≤ (1 + η / a) * ‖u‖ := by
        have : (1 + η / a) * a = η + a := by field_simp; ring
        nlinarith [div_pos hη ha]
      nlinarith
    calc (1 + η - s.re) * ‖v‖ ≤ v.re * ((2 + η / a) * ‖u‖) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by linarith)
      _ = _ := by ring
  have hre : (1 / v).re = v.re / ‖v‖ ^ 2 := by
    rw [one_div, inv_re, normSq_eq_norm_sq]
  rw [hre, one_div, one_div, inv_sub_inv hu0 hv0, norm_div, norm_mul, hd, mul_div_assoc']
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc (1 + η - s.re) * ‖v‖ ^ 2 = ((1 + η - s.re) * ‖v‖) * ‖v‖ := by ring
    _ ≤ ((2 + η / a) * v.re * ‖u‖) * ‖v‖ := by gcongr
    _ = _ := by ring

/-- **Under the proved RH, `ζ′/ζ` is `O(log t)` on `Re s ≥ 3/4`.** Every window zero has real
part `1/2`, so the window comparison of `RightOfCurve.lean` runs with the fixed gap `1/4` and
`s₁ = 2 + i Im s`. -/
theorem logDeriv_bound_of_RH : ∃ C : ℝ, ∀ s : ℂ, s ≠ 1 → 3 / 4 ≤ s.re →
    ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1)‖ ≤ C * Real.log (|s.im| + 2) := by
  classical
  obtain ⟨Cw, hCw⟩ := TauCeti.riemannZeta_logDeriv_window
  obtain ⟨CN, hCN, hNear⟩ := TauCeti.exists_neg_re_logDeriv_riemannZeta_one_add_le
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  refine ⟨|Cw| + 7 * (2 * (2 + CN) + |Cw|), fun s hs1 hs ↦ ?_⟩
  set t := s.im with ht
  set L := Real.log (|t| + 2)
  have hL : 1 / 2 ≤ L := hlog2.trans (Real.log_two_le_log_add_two (abs_nonneg t))
  have hK : 2 + CN ≤ 2 * (2 + CN) * L := by nlinarith
  rcases le_or_gt 2 s.re with h2 | h2
  · have h := norm_logDeriv_add_one_div_le_of_le_re' hNear one_pos le_rfl
      (show 1 + 1 ≤ s.re by linarith)
    rw [inv_one] at h
    nlinarith [abs_nonneg Cw]
  set s₁ : ℂ := ((1 + 1 : ℝ) : ℂ) + t * I
  have hs₁re : s₁.re = 1 + 1 := by simp [s₁]
  have hs₁im : s₁.im = t := by simp [s₁]
  have hs₁1 : s₁ ≠ 1 := fun h ↦ by rw [h, one_re] at hs₁re; linarith
  have hζ₁ : riemannZeta s₁ ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by linarith)
  set W := {z ∈ TauCeti.riemannZetaZerosClosedBall (2 + t * I) 4 |
    0 < z.re ∧ z.re < 1 ∧ |z.im - t| ≤ 1 ∧ riemannZeta z = 0}
  set m : ℂ → ℕ := fun z ↦ (analyticOrderAt riemannZeta z).toNat
  have hw := hCw s (by linarith) h2.le hs1 (riemannZeta_ne_zero_of_half_lt (by linarith))
  have hw₁ := hCw s₁ (by linarith) (by linarith) hs₁1 hζ₁
  rw [← ht, TauCeti.finsum_window_eq_sum_riemannZetaZerosClosedBall t
    fun z ↦ (m z : ℂ) / (s - z)] at hw
  rw [hs₁im, TauCeti.finsum_window_eq_sum_riemannZetaZerosClosedBall t
    fun z ↦ (m z : ℂ) / (s₁ - z)] at hw₁
  set H := deriv riemannZeta s / riemannZeta s + 1 / (s - 1)
  set H₁ := deriv riemannZeta s₁ / riemannZeta s₁ + 1 / (s₁ - 1)
  set S₀ := ∑ z ∈ W, (m z : ℂ) / (s - z)
  set S₁ := ∑ z ∈ W, (m z : ℂ) / (s₁ - z)
  have hCwL : Cw * L ≤ |Cw| * L := mul_le_mul_of_nonneg_right (le_abs_self Cw) (by linarith)
  have hH₁ : ‖H₁‖ ≤ 2 + CN := by
    have := norm_logDeriv_add_one_div_le_of_le_re' hNear one_pos le_rfl hs₁re.ge
    rw [inv_one] at this
    linarith
  have hS₁ : ‖S₁‖ ≤ 2 + CN + |Cw| * L := by linarith [norm_le_norm_add_norm_sub H₁ S₁]
  -- by RH every window zero has real part `1/2`
  have hzero : ∀ z ∈ W, z.re ≤ 1 - 2 * (1 / 4) := by
    intro z hz
    obtain ⟨-, -, -, -, hzζ⟩ := Finset.mem_filter.mp hz
    by_contra hlt
    exact riemannZeta_ne_zero_of_half_lt (by linarith) hzζ
  have hS : ‖S₀ - S₁‖ ≤ 6 * ‖S₁‖ := by
    rw [← Finset.sum_sub_distrib]
    calc _ ≤ ∑ z ∈ W, ‖(m z : ℂ) / (s - z) - (m z : ℂ) / (s₁ - z)‖ := norm_sum_le _ _
      _ ≤ ∑ z ∈ W, 6 * ((m z : ℂ) / (s₁ - z)).re := by
        refine Finset.sum_le_sum fun z hz ↦ ?_
        have hpt := norm_one_div_sub_sub_one_div_sub_le' (a := 1 / 4) (by norm_num) one_pos
          hs₁re hs₁im (by linarith) (by linarith) (hzero z hz)
        rw [show (2 : ℝ) + 1 / (1 / 4) = 6 by norm_num] at hpt
        rw [div_eq_mul_one_div (m z : ℂ), div_eq_mul_one_div (m z : ℂ), ← mul_sub, norm_mul,
          norm_natCast, ← ofReal_natCast, re_ofReal_mul]
        calc _ ≤ (m z : ℝ) * (6 * (1 / (s₁ - z)).re) :=
              mul_le_mul_of_nonneg_left hpt (Nat.cast_nonneg _)
          _ = _ := by ring
      _ = 6 * (∑ z ∈ W, (m z : ℂ) / (s₁ - z)).re := by rw [← Finset.mul_sum, re_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (re_le_norm _) (by norm_num)
  calc ‖H‖ ≤ ‖H - S₀‖ + ‖S₀ - S₁‖ + ‖S₁‖ := by
        simpa using norm_add₃_le (a := H - S₀) (b := S₀ - S₁) (c := S₁)
    _ ≤ |Cw| * L + 7 * (2 + CN + |Cw| * L) := by linarith
    _ ≤ _ := by nlinarith [abs_nonneg Cw]

open scoped Chebyshev in
/-- **A power saving for `ψ` from the proved RH.** There are `δ > 0` and `C` with
`|ψ(x) - x| ≤ C x^(1 - δ)` for every `x ≥ 3`. Ingham's transfer theorem (Tau Ceti) with the
constant zero-free width `1/4`, which the proved RH supplies. -/
theorem psi_sub_le_rpow_of_RH : ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 3 ≤ x →
    |ψ x - x| ≤ C * x ^ (1 - δ) := by
  obtain ⟨C, hC⟩ := logDeriv_bound_of_RH
  set U : Set ℂ := {s | 5 / 8 < s.re}
  have hζU {s : ℂ} (hs : s ∈ U) : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_half_lt (by simp only [U, Set.mem_ofPred_eq] at hs; linarith)
  set G : ℂ → ℂ := fun s ↦ -logDeriv (DirichletCharacter.LFunctionTrivChar₁ 1) s
  have hGU : DifferentiableOn ℂ G U := fun s hs ↦ by
    have hd := DirichletCharacter.differentiable_LFunctionTrivChar₁ 1
    exact ((((hd.analyticAt s).deriv).differentiableAt.div (hd s)
      (DirichletCharacter.LFunctionTrivChar₁_one_ne_zero (hζU hs))).neg).differentiableWithinAt
  have hGeq {s : ℂ} (hs1 : s ≠ 1) (hs : s ∈ U) :
      G s = -(deriv riemannZeta s / riemannZeta s + 1 / (s - 1)) := by
    simp only [G]
    rw [one_div, ← logDeriv_apply, TauCeti.logDeriv_riemannZeta_add_inv_sub_one hs1 (hζU hs)]
  set η : ℝ → ℝ := fun _ ↦ 1 / 4
  have hRU : {s : ℂ | 1 - η (|s.im| + 3) ≤ s.re} ⊆ U := fun s hs ↦ by
    simp only [η, Set.mem_ofPred_eq, U] at hs ⊢; linarith
  have ha (n : ℕ) (hn : 1 ≤ n) : ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ ≤
      1 * Real.log (n + 1) := by
    rw [Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, one_mul]
    exact ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_log (by exact_mod_cast hn) (by linarith))
  have hLG (s : ℂ) (hs : 1 < s.re) :
      LSeries (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) s = G s + 1 / (s - 1) := by
    have hs1 : s ≠ 1 := fun h ↦ by simp [h] at hs
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs,
      hGeq hs1 (show (5 : ℝ) / 8 < s.re by linarith)]
    ring
  have hl3 : 1 ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]; linarith [Real.exp_one_lt_d9]
  set C₀ := max (max C 0) (‖G 1‖ / Real.log 3)
  have hGb (s : ℂ) (hs : 1 - η (|s.im| + 3) ≤ s.re) :
      ‖G s‖ ≤ C₀ * Real.log (|s.im| + 3) ^ (1 : ℝ) := by
    rw [Real.rpow_one]
    have hlog3 : Real.log 3 ≤ Real.log (|s.im| + 3) :=
      Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im])
    rcases eq_or_ne s 1 with rfl | hs1
    · have hC₀ : 0 ≤ C₀ := le_trans (le_max_right C 0) (le_max_left _ _)
      calc ‖G 1‖ = ‖G 1‖ / Real.log 3 * Real.log 3 := by field_simp
        _ ≤ C₀ * Real.log (|(1 : ℂ).im| + 3) :=
          mul_le_mul (le_max_right _ _) hlog3 (by linarith) hC₀
    · simp only [η] at hs
      rw [hGeq hs1 (hRU (by simpa [η] using hs)), norm_neg]
      refine (hC s hs1 (by linarith)).trans ?_
      have h2 : Real.log (|s.im| + 2) ≤ Real.log (|s.im| + 3) :=
        Real.log_le_log (by positivity) (by linarith)
      calc C * Real.log (|s.im| + 2) ≤ max C 0 * Real.log (|s.im| + 2) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _)
              (Real.log_nonneg (by linarith [abs_nonneg s.im]))
        _ ≤ C₀ * Real.log (|s.im| + 3) :=
            mul_le_mul (le_max_left _ _) h2
              (Real.log_nonneg (by linarith [abs_nonneg s.im]))
              (le_trans (le_max_right _ _) (le_max_left _ _))
  obtain ⟨c, hc, C', hC'⟩ := TauCeti.LSeries.norm_sum_sub_mul_le_of_zeroFreeRegion
    (η := η) continuousOn_const (fun _ _ _ _ _ ↦ le_rfl) (a₀ := 1 / 4) (A := 0) (by norm_num)
    (fun t _ ↦ by simp [η]) ha (U := U) hRU hGU (r := 1)
    (by simpa using hLG) (B' := 1) hGb
  refine ⟨c / 4, by positivity, max C' 0, le_max_right _ _, fun x hx ↦ ?_⟩
  have hx0 : 0 < x := by linarith
  have hsum : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) - 1 * x =
      ((ψ x - x : ℝ) : ℂ) := by
    rw [Chebyshev.psi, ← Finset.Icc_add_one_left_eq_Ioc]
    push_cast
    ring
  have hω : 1 / 4 * Real.log x ≤ TauCeti.inghamExponent η x :=
    TauCeti.le_inghamExponent fun t ht ↦ by
      simp only [η]; linarith [Real.log_nonneg (show (1 : ℝ) ≤ t by linarith)]
  have h := hC' x hx
  rw [hsum, Complex.norm_real, Real.norm_eq_abs] at h
  have hpow : x * Real.exp (-c * TauCeti.inghamExponent η x) ≤ x ^ (1 - c / 4) := by
    rw [Real.rpow_sub hx0, Real.rpow_one, div_eq_mul_inv, ← Real.rpow_neg hx0.le,
      Real.rpow_def_of_pos hx0]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hx0.le
    nlinarith [mul_le_mul_of_nonneg_left hω hc.le]
  calc |ψ x - x| ≤ max C' 0 * x * Real.exp (-c * TauCeti.inghamExponent η x) :=
        h.trans (by gcongr; exact le_max_left _ _)
    _ ≤ max C' 0 * x ^ (1 - c / 4) := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hpow (le_max_right _ _)

open scoped Chebyshev in
/-- The same power saving for `θ`, with `δ ≤ 1/2`. -/
theorem theta_sub_le_rpow_of_RH : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ ∃ K : ℝ, 0 ≤ K ∧
    ∀ x : ℝ, 3 ≤ x → |θ x - x| ≤ K * x ^ (1 - δ) := by
  obtain ⟨δ, hδ, C, hC0, hC⟩ := psi_sub_le_rpow_of_RH
  set d := min δ (1 / 2)
  have hd : 0 < d := lt_min hδ (by norm_num)
  have hd2 : d ≤ 1 / 2 := min_le_right _ _
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine ⟨d, hd, hd2, C + Real.log 4 * (1 + 6 / Real.log 2), by positivity, fun x hx ↦ ?_⟩
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have h := Chebyshev.abs_theta_sub_le_abs_psi_sub_add (c := Real.log 4)
    (fun y hy ↦ Chebyshev.theta_le_log4_mul_x hy.le) hx0.le
  have hX : x ^ (1 - δ) ≤ x ^ (1 - d) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith [min_le_left δ (1 / 2)])
  have hhalf : x ^ (1 / 2 : ℝ) ≤ x ^ (1 - d) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hsq : √x ≤ x ^ (1 - d) := by rw [Real.sqrt_eq_rpow]; exact hhalf
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hlog6 : Real.log x ≤ 6 * x ^ (1 / 6 : ℝ) := by
    have := Real.log_le_rpow_div hx0.le (show (0 : ℝ) < 1 / 6 by norm_num)
    linarith [show x ^ (1 / 6 : ℝ) / (1 / 6) = 6 * x ^ (1 / 6 : ℝ) by ring]
  have hmax : max (Real.log x / Real.log 2 - 2) 0 ≤ 6 / Real.log 2 * x ^ (1 / 6 : ℝ) := by
    refine max_le ?_ (by positivity)
    calc Real.log x / Real.log 2 - 2 ≤ Real.log x / Real.log 2 := by linarith
      _ ≤ 6 * x ^ (1 / 6 : ℝ) / Real.log 2 := by gcongr
      _ = _ := by ring
  have hthird : max (Real.log x / Real.log 2 - 2) 0 * x ^ ((1 : ℝ) / 3) ≤
      6 / Real.log 2 * x ^ (1 - d) := by
    calc _ ≤ 6 / Real.log 2 * x ^ (1 / 6 : ℝ) * x ^ ((1 : ℝ) / 3) := by gcongr
      _ = 6 / Real.log 2 * x ^ (1 / 2 : ℝ) := by
          rw [mul_assoc, ← Real.rpow_add hx0]; norm_num
      _ ≤ _ := by gcongr
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  calc |θ x - x| ≤ C * x ^ (1 - d) + Real.log 4 * (x ^ (1 - d) + 6 / Real.log 2 * x ^ (1 - d)) := by
        have := hC x hx
        have := mul_le_mul_of_nonneg_left hX hC0
        have := mul_le_mul_of_nonneg_left (add_le_add hsq hthird) hl4
        linarith
    _ = _ := by ring

open scoped Chebyshev in
/-- **The prime count sits within `O(x^(1-δ))` of `Li x`, from the proved RH.** -/
theorem primeCounting_sub_logIntegral_le_rpow_of_RH : ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ,
    ∀ x : ℝ, 3 ≤ x → |(Nat.primeCounting ⌊x⌋₊ : ℝ) - TauCeti.Real.logIntegral x| ≤
      C * x ^ (1 - δ) := by
  obtain ⟨d, hd, hd2, K, hK0, hK⟩ := theta_sub_le_rpow_of_RH
  set D1 := |(Nat.primeCounting ⌊(3 : ℝ)⌋₊ : ℝ) - TauCeti.Real.logIntegral 3|
  set ε : ℝ → ℝ := fun t ↦ K * t ^ (-d)
  set D3 := 3 * ε 3 / Real.log 3
  have hl3 : 1 ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]; linarith [Real.exp_one_lt_d9]
  have hD3 : 0 ≤ D3 := by simp only [D3, ε]; positivity
  refine ⟨d, hd, D1 + K + D3 + 2 * K, fun x hx ↦ ?_⟩
  have hx0 : 0 < x := by linarith
  have hX1 : 1 ≤ x ^ (1 - d) := Real.one_le_rpow (by linarith) (by linarith)
  have hX0 : 0 ≤ x ^ (1 - d) := by positivity
  have hεt (t : ℝ) (ht : 0 < t) : t * ε t = K * t ^ (1 - d) := by
    simp only [ε]
    rw [sub_eq_add_neg, Real.rpow_add ht, Real.rpow_one]; ring
  have hint : IntervalIntegrable ε MeasureTheory.volume 3 x :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul K
  have hmain := Chebyshev.abs_primeCounting_sub_logIntegral_le (ε := ε) (x₀ := 3) (x := x)
    (by norm_num) hx hint (fun t ht ↦ by
      rw [hεt t (by linarith [ht.1])]; exact hK t ht.1)
  -- the four terms
  have hlx : 1 ≤ Real.log x := hl3.trans (Real.log_le_log (by norm_num) hx)
  have h2 : x * ε x / Real.log x ≤ K * x ^ (1 - d) := by
    rw [hεt x hx0]
    exact div_le_self (by positivity) hlx
  have hcont : ContinuousOn (fun t ↦ ε t / Real.log t ^ 2) (Set.uIcc 3 x) := by
    rw [Set.uIcc_of_le hx]
    refine ContinuousOn.div (continuousOn_const.mul (ContinuousOn.rpow_const continuousOn_id
      fun t ht ↦ Or.inl (ne_of_gt (show (0 : ℝ) < t by linarith [ht.1]))))
      ((Real.continuousOn_log.mono fun t ht ↦ by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [ht.1]).pow 2)
      fun t ht ↦ by
        have : 1 ≤ Real.log t := hl3.trans (Real.log_le_log (by norm_num) ht.1)
        exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le one_pos this))
  have h4 : ∫ t in (3 : ℝ)..x, ε t / Real.log t ^ 2 ≤ 2 * K * x ^ (1 - d) := by
    calc ∫ t in (3 : ℝ)..x, ε t / Real.log t ^ 2 ≤ ∫ t in (3 : ℝ)..x, ε t :=
          intervalIntegral.integral_mono_on hx (hcont.intervalIntegrable) hint fun t ht ↦ by
            have : 1 ≤ Real.log t := hl3.trans (Real.log_le_log (by norm_num) ht.1)
            have : 0 ≤ ε t := by simp only [ε]; have := ht.1; positivity
            exact div_le_self this (by nlinarith)
      _ = K * ((x ^ (1 - d) - 3 ^ (1 - d)) / (1 - d)) := by
          simp only [ε]
          rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith)),
            show -d + 1 = 1 - d by ring]
      _ ≤ 2 * K * x ^ (1 - d) := by
          have h3 : (0 : ℝ) ≤ 3 ^ (1 - d) := by positivity
          have hq : (x ^ (1 - d) - 3 ^ (1 - d)) / (1 - d) ≤ 2 * x ^ (1 - d) := by
            rw [div_le_iff₀ (by linarith)]; nlinarith
          nlinarith [mul_le_mul_of_nonneg_left hq hK0]
  have hD1 : 0 ≤ D1 := abs_nonneg _
  change _ ≤ D1 + _ + D3 + _ at hmain
  nlinarith [mul_le_mul_of_nonneg_left hX1 hD1, mul_le_mul_of_nonneg_left hX1 hD3]


open Classical in
/-- **The walls meet RH.** There are `δ > 0` and `C` such that for every `N ≥ 3` the wall count
`2 + #{n ≤ N that pass the wall test}` differs from `Li(N)` by at most `C N^(1-δ)`. Proved from
`riemannHypothesis` (through `primeCounting_sub_logIntegral_le_rpow_of_RH`) and his
`prime_count_walls`. -/
theorem walls_meet_rh : ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ N : ℕ, 3 ≤ N →
    |((2 + ((Finset.range (N + 1)).filter passes).card : ℕ) : ℝ) -
      TauCeti.Real.logIntegral N| ≤ C * (N : ℝ) ^ (1 - δ) := by
  obtain ⟨δ, hδ, C, hC⟩ := primeCounting_sub_logIntegral_le_rpow_of_RH
  refine ⟨δ, hδ, C, fun N hN ↦ ?_⟩
  have h := hC N (by exact_mod_cast hN)
  rwa [Nat.floor_natCast, prime_count_walls N hN] at h

/-! ## The named steps of `SeatFacingRH.lean` (11-22-2026), re-read against the proved RH -/

noncomputable def liTwo : ℝ :=
  Real.eulerMascheroniConstant + Real.log (Real.log 2) +
    ∑' k : ℕ, Real.log 2 ^ (k + 1) / ((k + 1) * (k + 1).factorial)

noncomputable def li (x : ℝ) : ℝ := liTwo + ∫ t in (2 : ℝ)..x, 1 / Real.log t

def PiLiBigO : Prop :=
  ∃ C : ℝ, ∀ x : ℝ, 2657 ≤ x →
    |(Nat.primeCounting ⌊x⌋₊ : ℝ) - li x| ≤ C * √x * Real.log x ^ 2

def RHOfPiLiBigO : Prop := PiLiBigO → RiemannHypothesis

/-- The named step `RHOfPiLiBigO` now holds, because its conclusion is a theorem. This is not
von Koch's argument; it is the proved RH. -/
theorem rhOfPiLiBigO_holds : RHOfPiLiBigO := fun _ ↦ riemannHypothesis

end WallsMeetRH

#print axioms riemannHypothesis
#print axioms WallsMeetRH.prime_count_walls
#print axioms WallsMeetRH.psi_sub_le_rpow_of_RH
#print axioms WallsMeetRH.primeCounting_sub_logIntegral_le_rpow_of_RH
#print axioms WallsMeetRH.walls_meet_rh
#print axioms WallsMeetRH.rhOfPiLiBigO_holds

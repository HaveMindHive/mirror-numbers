import Main
import TauCeti.NumberTheory.LSeries.SmoothedSum.ZeroFreeRegion
import TauCeti.NumberTheory.LSeries.DirichletEulerLog
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Bounds
import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogDeriv.Basic
import TauCeti.Analysis.Complex.LocalLogDeriv
import TauCeti.Analysis.Complex.JensenFormula
import TauCeti.Analysis.Complex.AbsMax
import TauCeti.Analysis.Meromorphic.Divisor
import TauCeti.NumberTheory.Chebyshev.PsiSubTheta
import TauCeti.NumberTheory.Chebyshev.ThetaTransfer
import WallsMeetRHSharp

/-!
# The wing families meet the proved GRH (11-27-2026)

Turaq Rayn-McLean's walls of six seat every prime `p ≥ 5` at `p = 6k + f` with the facing
`f = ±1`: the two wing families `6k - 1` (`f = -1`) and `6k + 1` (`f = +1`). This file proves,
in the environment of the community condensed proof of the Riemann hypothesis by Alpöge with
Claude (which proves the generalized Riemann hypothesis for every Dirichlet L-function:
`LFunction_ne_zero_of_half_lt_re`, `LFunction_eq_zero_re` in `Main`), that each wing family
carries half the primes to square-root accuracy. It imports the Sharp file
(`WallsMeetRHSharp_v1.0_11-27-2026.lean`, compiled as the module `WallsMeetRHSharp` by
`check-wings_v1.0_11-27-2026.sh`) for the zeta route `|π(x) - Li(x)| ≤ C √x log² x`.

* `logDeriv_LFunction_le_of_GRH_gap`: for a nonprincipal `χ` mod `N`,
  `‖L′/L(s, χ)‖ ≤ (C / a) log(|Im s| + 2)` on `1/2 + a ≤ Re s ≤ 2`, uniformly in the gap
  `a ∈ (0, 1]`. Landau's local lemma on the discs of radii `8/5 < 19/10` about `2 + i Im s`,
  the zeros of the small disc on `Re = 1/2` by GRH, their number `O(log(|Im s| + 2))` by Jensen.
  No window lemma is needed for `L(s, χ)`: the discs stay in `Re > 1/10`, where Tau Ceti's level
  bound `‖L(s, χ)‖ ≤ N ‖s‖ / Re s` holds.
* `psi_chi_le_of_gap`: `‖∑_{n ≤ x} χ(n) Λ(n)‖ ≤ D x^(1/2 + a) log² x / a` for `0 < a ≤ 1/4`,
  `x ≥ 3` (Tau Ceti's smoothed Perron contour with no main term, since `L(s, χ)` has no pole).
* `psi_chi_le_of_GRH`: `O(√x log³ x)` (gap `a = 1 / log x`), `psi_chi_le_rpow_of_GRH`:
  `O(x^(1/2 + δ))` for every `δ > 0`; `psi_chi6_le_of_GRH` at the wing character.
* `chi6`: the wing character mod 6 (`chi6_apply`: `+1` on `6k + 1`, `-1` on `6k - 1`, `0` on
  multiples of `2` or `3`), its real weight `w6`, the twisted sums `psi6`, `theta6`, `primeSum6`.
* `primeSum6_le`: `|∑_{p ≤ x} w₆(p)| ≤ C √x log² x` for `x ≥ 3` (Abel summation from
  `theta6_le`).
* `wingCount f x`: the primes `p ≤ x` seated at `p = 6k + f`.
  `wing_lead_le`: `|#(6k - 1 family) - #(6k + 1 family)| ≤ C √x log² x`.
  `wing_count_sub_half_li`: `|#(6k + f family) - Li(x)/2| ≤ C √x log² x` for `f = ±1`.
  `wing_families_meet_grh`: the three bounds with one constant.

Every step is kernel-checked (`#print axioms`: `propext`, `Classical.choice`, `Quot.sound`).
Tau Ceti is Apache-2.0, copyright The Tau Ceti contributors; `nonneg_of_norm_mellin_smoothCutoff_le`
is a copy of a private lemma of its `ZeroFreeRegion.lean`, and
`primeSum6_eq_theta6_div_log_add_integral` follows the proof of Mathlib's
`Chebyshev.primeCounting_eq_theta_div_log_add_integral` (Apache-2.0, Mathlib contributors).
-/

open Complex Metric Set

namespace WingFamiliesGRH

/-! ## GRH for one nonprincipal character, as used -/

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

/-- From the proved GRH: `L(s, χ) ≠ 0` for `Re s > 1/2` when `χ` is nonprincipal. -/
theorem LFunction_ne_zero_of_half_lt (hχ : χ ≠ 1) {s : ℂ} (hs : 1 / 2 < s.re) :
    DirichletCharacter.LFunction χ s ≠ 0 :=
  LFunction_ne_zero_of_half_lt_re N χ s hs (Or.inl hχ)

/-- From the proved GRH: a zero of `L(s, χ)` with `0 < Re ρ < 1` has `Re ρ = 1/2`. -/
theorem re_eq_half_of_LFunction_eq_zero {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hρ : DirichletCharacter.LFunction χ ρ = 0) : ρ.re = 1 / 2 :=
  LFunction_eq_zero_re N χ ρ h0 h1 hρ

/-! ## `L′/L` right of the critical line, with the gap explicit -/

/-- The distance from `s` to the point `2 + i Im s` is `|Re s - 2|`. -/
theorem norm_sub_two_add_im_mul_I (s : ℂ) : ‖s - (2 + s.im * I)‖ = |s.re - 2| := by
  have : s - (2 + s.im * I) = ((s.re - 2 : ℝ) : ℂ) := by apply Complex.ext <;> simp
  rw [this, Complex.norm_real, Real.norm_eq_abs]

/-- **Under the proved GRH, `L′/L(s, χ)` is `O(log(|Im s| + 2) / a)` on `1/2 + a ≤ Re s ≤ 2`**
for a nonprincipal `χ`, with one constant for every gap `a ∈ (0, 1]`. Landau's local lemma
(`AnalyticOnNhd.norm_logDeriv_sub_finsum_divisor_le`) on the discs of radii `8/5 < 19/10` about
`s₀ = 2 + i Im s`, where `‖L(w, χ)‖ ≤ 20 N (|Im s| + 2)` (Tau Ceti's level bound, `Re w ≥ 1/10`)
and `‖L(s₀, χ)‖ ≥ exp(-ζ(2))`, leaves the sum over the zeros of the small disc, each on
`Re = 1/2` by GRH and so at distance at least `a` from `s`; they number `O(log(|Im s| + 2))`
by Jensen's bound (`AnalyticOnNhd.sum_divisor_le_log_div_log`). -/
theorem logDeriv_LFunction_le_of_GRH_gap (hχ : χ ≠ 1) : ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 0 < a → a ≤ 1 →
    ∀ s : ℂ, 1 / 2 + a ≤ s.re → s.re ≤ 2 →
    ‖logDeriv (DirichletCharacter.LFunction χ) s‖ ≤ C / a * Real.log (|s.im| + 2) := by
  classical
  set F := DirichletCharacter.LFunction χ
  set c₀ : ℝ := Real.exp (-(riemannZeta ((2 : ℝ) : ℂ)).re) with hc₀def
  have hc₀ : 0 < c₀ := Real.exp_pos _
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlr : 0 < Real.log ((19 / 10 : ℝ) / (8 / 5)) := Real.log_pos (by norm_num)
  set Cm : ℝ := |Real.log (20 * N / c₀)| / Real.log 2 + 1
  have hCm : 0 ≤ Cm := by positivity
  set A : ℝ := 4 * (8 / 5 + 3 / 2) / (8 / 5 - 3 / 2) ^ 2 +
    8 / 5 / (((19 / 10) ^ 2 - 8 / 5 * (3 / 2)) * Real.log ((19 / 10 : ℝ) / (8 / 5)))
  have hA : 0 ≤ A := by positivity
  refine ⟨A * Cm + Cm / Real.log ((19 / 10 : ℝ) / (8 / 5)), by positivity,
    fun a ha ha1 s hs hs2 ↦ ?_⟩
  set t := s.im
  set L₂ := Real.log (|t| + 2)
  have hL₂ : Real.log 2 ≤ L₂ := Real.log_le_log two_pos (by linarith [abs_nonneg t])
  have hL₂0 : 0 ≤ L₂ := hl2.le.trans hL₂
  set s₀ : ℂ := 2 + t * I with hs₀def
  have hs₀re : s₀.re = 2 := by simp [s₀]
  have hs₀im : s₀.im = t := by simp [s₀]
  have hss₀ : ‖s - s₀‖ ≤ 3 / 2 := by
    rw [hs₀def, norm_sub_two_add_im_mul_I, abs_le]; constructor <;> linarith
  have hF : AnalyticOnNhd ℂ F (closedBall s₀ (19 / 10)) :=
    ((DirichletCharacter.differentiable_LFunction hχ).differentiableOn.analyticOnNhd
      isOpen_univ).mono (subset_univ _)
  have hFs₀ : F s₀ ≠ 0 := LFunction_ne_zero_of_half_lt hχ (by rw [hs₀re]; norm_num)
  have hFs : F s ≠ 0 := LFunction_ne_zero_of_half_lt hχ (by linarith)
  -- the centre lower bound and the sphere upper bound
  have hcentre : c₀ ≤ ‖F s₀‖ := by
    have := χ.exp_neg_re_riemannZeta_le_norm_LFunction (s := s₀) (by rw [hs₀re]; norm_num)
    rwa [hs₀re] at this
  have hs₀norm : ‖s₀‖ ≤ |t| + 2 := by
    calc ‖s₀‖ ≤ ‖(2 : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
      _ = |t| + 2 := by simp [Complex.norm_real, Real.norm_eq_abs]; ring
  set M : ℝ := 20 * N * (|t| + 2) / c₀
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have hM : ∀ w ∈ sphere s₀ (19 / 10), ‖F w‖ ≤ M * ‖F s₀‖ := fun w hw ↦ by
    rw [mem_sphere, dist_eq_norm] at hw
    have hre : |w.re - 2| ≤ 19 / 10 := by
      have := abs_re_le_norm (w - s₀); rw [hw, sub_re, hs₀re] at this; exact this
    have hwre : 1 / 10 ≤ w.re := by linarith [(abs_le.1 hre).1]
    have hwn : ‖w‖ ≤ 2 * (|t| + 2) := by
      calc ‖w‖ = ‖(w - s₀) + s₀‖ := by rw [sub_add_cancel]
        _ ≤ ‖w - s₀‖ + ‖s₀‖ := norm_add_le _ _
        _ ≤ 19 / 10 + (|t| + 2) := by rw [hw]; linarith
        _ ≤ 2 * (|t| + 2) := by linarith [abs_nonneg t]
    calc ‖F w‖ ≤ N * ‖w‖ / w.re := χ.norm_LFunction_le_level_mul_norm_div_re hχ (by linarith)
      _ ≤ N * (2 * (|t| + 2)) / (1 / 10) := by gcongr
      _ = 20 * N * (|t| + 2) := by ring
      _ = M * c₀ := by simp only [M]; field_simp
      _ ≤ M * ‖F s₀‖ := by gcongr
  have hM1 : 1 ≤ M :=
    (hF.differentiableOn.diffContOnCl_ball Subset.rfl).one_le_of_forall_mem_sphere_norm_le_mul
      (by norm_num) hFs₀ hM
  have hlogM : Real.log M ≤ Cm * L₂ := by
    have hM' : M = 20 * N / c₀ * (|t| + 2) := by simp only [M]; ring
    have hpos : 0 < 20 * N / c₀ := by positivity
    rw [hM', Real.log_mul hpos.ne' (by positivity)]
    have h1 : Real.log (20 * N / c₀) ≤ |Real.log (20 * N / c₀)| / Real.log 2 * L₂ := by
      calc Real.log (20 * N / c₀) ≤ |Real.log (20 * N / c₀)| := le_abs_self _
        _ = |Real.log (20 * N / c₀)| / Real.log 2 * Real.log 2 := by field_simp
        _ ≤ |Real.log (20 * N / c₀)| / Real.log 2 * L₂ := by gcongr
    simp only [Cm]; nlinarith
  have hlogM0 : 0 ≤ Real.log M := Real.log_nonneg hM1
  -- Landau's local lemma on the discs of radii `8/5 < 19/10`
  have hd : ‖s - s₀‖ < 8 / 5 := by linarith
  have hlocal := hF.norm_logDeriv_sub_finsum_divisor_le (by norm_num : (8 / 5 : ℝ) < 19 / 10) hM hd hFs
  have hcoef : 4 * (8 / 5 + ‖s - s₀‖) / (8 / 5 - ‖s - s₀‖) ^ 2 +
      8 / 5 / (((19 / 10) ^ 2 - 8 / 5 * ‖s - s₀‖) * Real.log ((19 / 10 : ℝ) / (8 / 5))) ≤ A := by
    simp only [A]
    gcongr
  have hloc : ‖logDeriv F s -
      ∑ᶠ ρ, (MeromorphicOn.divisor F (closedBall s₀ (8 / 5)) ρ : ℂ) / (s - ρ)‖ ≤ A * Cm * L₂ := by
    calc _ ≤ _ := hlocal
      _ ≤ A * Real.log M := mul_le_mul_of_nonneg_right hcoef hlogM0
      _ ≤ A * (Cm * L₂) := by gcongr
      _ = A * Cm * L₂ := by ring
  -- the zeros of the small disc: on `Re = 1/2`, at distance `≥ a` from `s`, `O(L₂)` in number
  set D := MeromorphicOn.divisor F (closedBall s₀ (8 / 5))
  have hDfin : D.support.Finite :=
    MeromorphicOn.divisor_support_finite_of_subset hF.meromorphicOn (isCompact_closedBall _ _)
      (closedBall_subset_closedBall (by norm_num))
  set S := hDfin.toFinset
  have hDval (ρ : ℂ) (hρ : ρ ∈ S) : D ρ = (analyticOrderNatAt F ρ : ℤ) ∧
      ‖ρ - s₀‖ ≤ 8 / 5 ∧ F ρ = 0 := by
    have hsup : D ρ ≠ 0 := by simpa [S, Function.mem_support] using hρ
    have hmem : ρ ∈ closedBall s₀ (8 / 5) := D.supportWithinDomain hsup
    have hρa : AnalyticAt ℂ F ρ := hF ρ (closedBall_subset_closedBall (by norm_num) hmem)
    refine ⟨(hF.meromorphicOn.mono_set (closedBall_subset_closedBall (by norm_num))).divisor_eq_analyticOrderNatAt hρa hmem, ?_, ?_⟩
    · rwa [mem_closedBall, dist_eq_norm] at hmem
    · by_contra hne; exact hsup (hρa.divisor_apply_eq_zero hne)
  have hsep (ρ : ℂ) (hρ : ρ ∈ S) : a ≤ ‖s - ρ‖ := by
    obtain ⟨-, hdist, hzero⟩ := hDval ρ hρ
    have hre : |ρ.re - 2| ≤ 8 / 5 := by
      have := abs_re_le_norm (ρ - s₀); rw [sub_re, hs₀re] at this; linarith
    have h0 : 0 < ρ.re := by linarith [(abs_le.1 hre).1]
    have h1 : ρ.re < 1 := by
      by_contra h
      exact χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ) (not_lt.1 h) hzero
    have hhalf := re_eq_half_of_LFunction_eq_zero h0 h1 hzero
    calc a ≤ (s - ρ).re := by rw [sub_re, hhalf]; linarith
      _ ≤ ‖s - ρ‖ := re_le_norm _
  have hsum_eq : ∑ᶠ ρ, (D ρ : ℂ) / (s - ρ) = ∑ ρ ∈ S, (D ρ : ℂ) / (s - ρ) :=
    finsum_eq_sum_of_support_subset _ fun ρ hρ ↦ by
      rw [Finset.mem_coe, Set.Finite.mem_toFinset, Function.mem_support]
      intro h; apply hρ; simp [h]
  have hcount_eq : ∑ᶠ ρ, D ρ = ∑ ρ ∈ S, D ρ :=
    finsum_eq_sum_of_support_subset _ fun ρ hρ ↦ by
      rwa [Finset.mem_coe, Set.Finite.mem_toFinset]
  have hcount := hF.sum_divisor_le_log_div_log (by norm_num : (0 : ℝ) < 8 / 5) (by norm_num) hFs₀ hM
  rw [hcount_eq] at hcount
  have hW : ‖∑ ρ ∈ S, (D ρ : ℂ) / (s - ρ)‖ ≤ Cm * L₂ / (Real.log ((19 / 10 : ℝ) / (8 / 5)) * a) := by
    calc ‖∑ ρ ∈ S, (D ρ : ℂ) / (s - ρ)‖ ≤ ∑ ρ ∈ S, ((D ρ : ℤ) : ℝ) / a := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ hρ ↦ ?_)
          obtain ⟨hval, -, -⟩ := hDval ρ hρ
          have hnn : (0 : ℝ) ≤ ((D ρ : ℤ) : ℝ) := by rw [hval]; positivity
          rw [norm_div, show ((D ρ : ℤ) : ℂ) = (((D ρ : ℤ) : ℝ) : ℂ) by norm_cast,
            Complex.norm_real, Real.norm_of_nonneg hnn]
          exact div_le_div_of_nonneg_left hnn ha (hsep ρ hρ)
      _ = ((∑ ρ ∈ S, D ρ : ℤ) : ℝ) / a := by rw [Int.cast_sum, Finset.sum_div]
      _ ≤ Real.log M / Real.log ((19 / 10 : ℝ) / (8 / 5)) / a := by gcongr
      _ ≤ Cm * L₂ / Real.log ((19 / 10 : ℝ) / (8 / 5)) / a := by gcongr
      _ = Cm * L₂ / (Real.log ((19 / 10 : ℝ) / (8 / 5)) * a) := by rw [div_div]
  rw [hsum_eq] at hloc
  have htri : ‖logDeriv F s‖ ≤ ‖logDeriv F s - ∑ ρ ∈ S, (D ρ : ℂ) / (s - ρ)‖ +
      ‖∑ ρ ∈ S, (D ρ : ℂ) / (s - ρ)‖ := by
    have := norm_add_le (logDeriv F s - ∑ ρ ∈ S, (D ρ : ℂ) / (s - ρ)) (∑ ρ ∈ S, (D ρ : ℂ) / (s - ρ))
    rwa [sub_add_cancel] at this
  have h1 : A * Cm * L₂ ≤ A * Cm * L₂ / a :=
    le_div_self (by positivity) ha ha1
  have h2 : Cm * L₂ / (Real.log ((19 / 10 : ℝ) / (8 / 5)) * a) =
      Cm / Real.log ((19 / 10 : ℝ) / (8 / 5)) / a * L₂ := by
    field_simp
  calc ‖logDeriv F s‖ ≤ A * Cm * L₂ + Cm * L₂ / (Real.log ((19 / 10 : ℝ) / (8 / 5)) * a) := by
        linarith
    _ ≤ A * Cm * L₂ / a + Cm / Real.log ((19 / 10 : ℝ) / (8 / 5)) / a * L₂ := by
        rw [← h2]; linarith
    _ = (A * Cm + Cm / Real.log ((19 / 10 : ℝ) / (8 / 5))) / a * L₂ := by ring

/-! ## The explicit-formula contour for `∑ χ(n) Λ(n)` at `η = 1/2 - a`, `T = x`, `ε = x^(-1/2)` -/

/-- Copy of a private lemma of Tau Ceti's `ZeroFreeRegion.lean` (Apache 2.0): the Mellin bound at
`ε = 1`, `s = 1` forces `C ≥ 0`. -/
theorem nonneg_of_norm_mellin_smoothCutoff_le {ν : ℝ → ℝ} {C : ℝ}
    (hC : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 2 →
      ‖mellin (fun x ↦ (TauCeti.smoothCutoff ν ε x : ℂ)) s‖ ≤ C / (‖s‖ * (1 + ε * ‖s‖))) :
    0 ≤ C := by
  have h := hC 1 one_pos le_rfl 1 (by norm_num) (by norm_num)
  rw [norm_one, one_mul, mul_one] at h
  exact (div_nonneg_iff.1 ((norm_nonneg _).trans h)).elim (·.1) fun h' ↦ absurd h'.2 (by norm_num)

open scoped Real in
/-- The arithmetic of the contour terms at `η = 1/2 - a`, `T = x = s²`, `ε = 1/s`, no main term:
`A = log(x + 2) ≤ 2L`, `P = log(1 + x/(1/2 + a)) ≤ 2L`, `L = log x ≥ 1`, `s ≤ y = x^(1/2 + a)`,
`K = Cg A / a ≤ 2 Cg L / a`. -/
private lemma wing_terms_le {C Cg a x s y L A P : ℝ} (hC : 0 ≤ C) (hCg : 0 ≤ Cg) (ha : 0 < a)
    (ha4 : a ≤ 1 / 4) (hs : 1 ≤ s) (hx : x = s ^ 2) (hL : 1 ≤ L) (hA : 0 ≤ A) (hA2 : A ≤ 2 * L)
    (hP : 0 ≤ P) (hP2 : P ≤ 2 * L) (hy : s ≤ y) :
    1 / (2 * π) * (2 * (8 * 1 * L ^ 2 * C * (Real.exp 1 * x)) / (s⁻¹ * x) +
        4 * (Cg * A / a * C * y) * P +
        2 * ((L⁻¹ + (1 / 2 - a)) * (Cg * A / a * C) * (Real.exp 1 * x) / (s⁻¹ * x ^ 2))) +
      3 * 1 * (2 * s⁻¹ * x + 1) * L ≤
    (16 * Real.exp 1 * C + (16 + 6 * Real.exp 1) * Cg * C + 9) * y * L ^ 2 / a := by
  subst hx
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  generalize Real.exp 1 = e at *
  have hs0 : 0 < s := by linarith
  have hη : 0 < 1 / 2 - a := by linarith
  have hy1 : 1 ≤ y := hs.trans hy
  have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL
  have hyQ : y ≤ y * L ^ 2 / a := by
    rw [le_div_iff₀ ha]; nlinarith
  have hsQ : s ≤ y * L ^ 2 / a := hy.trans hyQ
  have hLQ : L / a ≤ y * L ^ 2 / a := by
    apply div_le_div_of_nonneg_right _ ha.le; nlinarith
  have hsLQ : s * L ≤ y * L ^ 2 / a := by
    rw [le_div_iff₀ ha]
    have h1 : s * a ≤ y := by nlinarith
    have h2 : s * a * L ≤ y * L := mul_le_mul_of_nonneg_right h1 (by linarith)
    have h3 : y * L ≤ y * L ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
    linarith
  have hQ0 : 0 ≤ y * L ^ 2 / a := by positivity
  have hK : Cg * A / a ≤ 2 * Cg * L / a := div_le_div_of_nonneg_right (by nlinarith) ha.le
  have hK0 : 0 ≤ Cg * A / a := by positivity
  generalize Cg * A / a = K at *
  have hK' : 0 ≤ 2 * Cg * L / a := by positivity
  have t1 : 2 * (8 * 1 * L ^ 2 * C * (e * s ^ 2)) / (s⁻¹ * s ^ 2) ≤ 16 * e * C * (y * L ^ 2 / a) := by
    rw [show 2 * (8 * 1 * L ^ 2 * C * (e * s ^ 2)) / (s⁻¹ * s ^ 2) = 16 * e * C * (s * L ^ 2) by
      field_simp; ring]
    gcongr
    rw [le_div_iff₀ ha]
    nlinarith [mul_le_mul_of_nonneg_right hy (sq_nonneg L),
      mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ y) (sq_nonneg L)) (by linarith : (0:ℝ) ≤ 1 - a)]
  have t2 : 4 * (K * C * y) * P ≤ 16 * Cg * C * (y * L ^ 2 / a) := by
    calc 4 * (K * C * y) * P ≤ 4 * (2 * Cg * L / a * C * y) * (2 * L) := by gcongr
      _ = _ := by ring
  have t3 : 2 * ((L⁻¹ + (1 / 2 - a)) * (K * C) * (e * s ^ 2) / (s⁻¹ * (s ^ 2) ^ 2)) ≤
      6 * e * Cg * C * (y * L ^ 2 / a) := by
    have hLi : L⁻¹ + (1 / 2 - a) ≤ 3 / 2 := by
      have := inv_le_one_of_one_le₀ hL; linarith
    have hsi : s⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hs
    have hLi0 : 0 ≤ L⁻¹ + (1 / 2 - a) := by positivity
    calc 2 * ((L⁻¹ + (1 / 2 - a)) * (K * C) * (e * s ^ 2) / (s⁻¹ * (s ^ 2) ^ 2))
        = 2 * (L⁻¹ + (1 / 2 - a)) * K * C * e * s⁻¹ := by field_simp
      _ ≤ 2 * (3 / 2) * (2 * Cg * L / a) * C * e * 1 := by gcongr
      _ = 6 * e * Cg * C * (L / a) := by ring
      _ ≤ _ := by gcongr
  have t4 : 3 * 1 * (2 * s⁻¹ * s ^ 2 + 1) * L ≤ 9 * (y * L ^ 2 / a) := by
    rw [show 2 * s⁻¹ * s ^ 2 = 2 * s by field_simp]
    nlinarith
  have hπ : 1 / (2 * π) ≤ 1 := by rw [div_le_one (by positivity)]; linarith [Real.two_le_pi]
  have hπ0 : 0 ≤ 1 / (2 * π) := by positivity
  have hsum0 : 0 ≤ 2 * (8 * 1 * L ^ 2 * C * (e * s ^ 2)) / (s⁻¹ * s ^ 2) + 4 * (K * C * y) * P +
      2 * ((L⁻¹ + (1 / 2 - a)) * (K * C) * (e * s ^ 2) / (s⁻¹ * (s ^ 2) ^ 2)) := by
    have : 0 ≤ L⁻¹ + (1 / 2 - a) := by positivity
    positivity
  have hmul := mul_le_of_le_one_left hsum0 hπ
  have hD : (16 * e * C + (16 + 6 * e) * Cg * C + 9) * y * L ^ 2 / a =
      16 * e * C * (y * L ^ 2 / a) + 16 * Cg * C * (y * L ^ 2 / a) +
        6 * e * Cg * C * (y * L ^ 2 / a) + 9 * (y * L ^ 2 / a) := by ring
  rw [hD]
  linarith

open scoped LSeries.notation ArithmeticFunction.vonMangoldt in
/-- **The explicit formula for `∑ χ(n) Λ(n)` under the proved GRH, with the gap `a` free.** For a
nonprincipal `χ` there is a constant `D` such that for every `0 < a ≤ 1/4` and every `x ≥ 3`,
`‖∑_{n ≤ x} χ(n) Λ(n)‖ ≤ D x^(1/2 + a) log² x / a`.

Tau Ceti's smoothed Perron contour (`norm_tsum_mul_smoothCutoff_sub_residue_le_of_norm_le_mul_log`)
for `a(n) = χ(n) Λ(n)`, whose L-series is `-L′/L(s, χ)`, regular on `Re s > 1/2` with no pole
(`r = 0`), on the rectangle `[1/2 + a, 1 + 1/log x] × [-x, x]`, cutoff scale `ε = x^(-1/2)`; the
left edge is bounded through `logDeriv_LFunction_le_of_GRH_gap`; the sharp/smooth comparison
costs `3 (2 √x + 1) log x`. -/
theorem psi_chi_le_of_gap (hχ : χ ≠ 1) : ∃ D : ℝ, 0 ≤ D ∧ ∀ a : ℝ, 0 < a → a ≤ 1 / 4 →
    ∀ x : ℝ, 3 ≤ x → ‖∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, χ n * (Λ n : ℂ)‖ ≤
      D * x ^ (1 / 2 + a) * Real.log x ^ 2 / a := by
  obtain ⟨Cg, hCg0, hCg⟩ := logDeriv_LFunction_le_of_GRH_gap hχ
  -- the bump and the uniform Mellin bound on the strip `1/2 ≤ Re s ≤ 2`
  obtain ⟨ν, hνd, hν0, hνs, hνm, -⟩ := TauCeti.exists_smooth_symmetric_bump one_lt_two
  have hνs' : Function.support ν ∩ Set.Ioi 0 ⊆ Set.Icc (1 / 2) 2 := fun y hy ↦ by
    simpa only [one_div] using hνs hy.1
  have hν0' : ∀ y > 0, 0 ≤ ν y := fun y _ ↦ hν0 y
  have hν1 : ContDiffOn ℝ 1 ν (Set.Ioi 0) := (hνd.of_le (by exact_mod_cast le_top)).contDiffOn
  obtain ⟨C, hC⟩ := TauCeti.exists_norm_mellin_smoothCutoff_le (k := 1) hν1 hνs'
    (σ₁ := 1 / 2) (σ₂ := 2) (by norm_num)
  simp only [pow_one] at hC
  have hC0 : 0 ≤ C := nonneg_of_norm_mellin_smoothCutoff_le hC
  -- the L-series of `χ Λ` is `G = -L′/L`, regular on `Re s > 1/2`
  set F := DirichletCharacter.LFunction χ
  set U : Set ℂ := {s | 1 / 2 < s.re}
  have hFU {s : ℂ} (hs : s ∈ U) : F s ≠ 0 := LFunction_ne_zero_of_half_lt hχ (by simpa [U] using hs)
  set G : ℂ → ℂ := fun s ↦ -logDeriv F s
  have hd : Differentiable ℂ F := DirichletCharacter.differentiable_LFunction hχ
  have hGU : DifferentiableOn ℂ G U := fun s hs ↦
    ((((hd.analyticAt s).deriv).differentiableAt.div (hd s) (hFU hs)).neg).differentiableWithinAt
  set a : ℕ → ℂ := ↗χ * ↗Λ
  have ha (n : ℕ) (hn : 1 ≤ n) : ‖a n‖ ≤ 1 * Real.log (n + 1) := by
    simp only [a, Pi.mul_apply, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, one_mul]
    calc ‖χ (n : ZMod N)‖ * Λ n ≤ 1 * Λ n :=
          mul_le_mul_of_nonneg_right (χ.norm_le_one _) ArithmeticFunction.vonMangoldt_nonneg
      _ ≤ Real.log (n + 1) := by
          rw [one_mul]
          exact ArithmeticFunction.vonMangoldt_le_log.trans
            (Real.log_le_log (by exact_mod_cast hn) (by linarith))
  have hLG (s : ℂ) (hs : 1 < s.re) : LSeries a s = G s + 0 / (s - 1) := by
    simp only [G, a, zero_div, add_zero]
    rw [χ.logDeriv_LFunction_eq_neg_LSeries hs, neg_neg]
  refine ⟨16 * Real.exp 1 * C + (16 + 6 * Real.exp 1) * Cg * C + 9, by positivity,
    fun g hg0 hg4 x hx ↦ ?_⟩
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hs1 : 1 ≤ √x := Real.one_le_sqrt.2 hx1
  have hs0 : 0 < √x := by linarith
  have hxs : x = (√x) ^ 2 := (Real.sq_sqrt hx0.le).symm
  have hε : 0 < (√x)⁻¹ := by positivity
  have hε1 : (√x)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hs1
  have hL1 : 1 ≤ Real.log x :=
    (Real.le_log_iff_exp_le hx0).2 (by linarith [Real.exp_one_lt_d9])
  have hLinv : (Real.log x)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hL1
  have hLinv0 : 0 < (Real.log x)⁻¹ := inv_pos.2 (by linarith)
  have hη : 0 < 1 / 2 - g := by linarith
  have hη1 : 1 / 2 - g < 1 := by linarith
  have hηT : 1 / 2 - g ≤ x := by linarith
  have h1η : 1 - (1 / 2 - g) = 1 / 2 + g := by ring
  -- the rectangle lies in `U`
  have hrect : Set.Icc (1 - (1 / 2 - g)) (1 + (Real.log x)⁻¹) ×ℂ Set.Icc (-x) x ⊆ U :=
    fun z hz ↦ by
      have := (mem_reProdIm.1 hz).1.1
      simp only [U, Set.mem_ofPred_eq]; linarith
  have hlogx2 : 1 ≤ Real.log (x + 2) :=
    (Real.le_log_iff_exp_le (by linarith)).2 (by linarith [Real.exp_one_lt_d9])
  -- `G` is bounded by `Cg log(x + 2) / a` on the rectangle
  have hGb : ∀ z ∈ Set.Icc (1 - (1 / 2 - g)) (1 + (Real.log x)⁻¹) ×ℂ Set.Icc (-x) x,
      ‖G z‖ ≤ Cg * Real.log (x + 2) / g := fun z hz ↦ by
    obtain ⟨⟨hre1, hre2⟩, him⟩ := mem_reProdIm.1 hz
    simp only [G, norm_neg]
    refine (hCg g hg0 (by linarith) z (by linarith) (by linarith)).trans ?_
    have hzim : |z.im| ≤ x := abs_le.2 ⟨him.1, him.2⟩
    have hlog : Real.log (|z.im| + 2) ≤ Real.log (x + 2) :=
      Real.log_le_log (by positivity) (by linarith)
    calc Cg / g * Real.log (|z.im| + 2) ≤ Cg / g * Real.log (x + 2) := by gcongr
      _ = Cg * Real.log (x + 2) / g := by ring
  -- the contour estimate and the sharp/smooth comparison
  have hcont := TauCeti.LSeries.norm_tsum_mul_smoothCutoff_sub_residue_le_of_norm_le_mul_log
    (a := a) ha hν1 hνs' hε (by linarith) hη hη1 hηT (G := G) (r := 0)
    (hGU.continuousOn.mono hrect)
    (hGU.mono fun z hz ↦ hrect ⟨Set.Ioo_subset_Icc_self hz.1, Set.Ioo_subset_Icc_self hz.2⟩) hGb
    (fun z hz ↦ hLG z (by rw [hz]; linarith))
    (fun z hz1 hz2 ↦ hC (√x)⁻¹ hε hε1 z (by linarith) (by linarith))
  have hsm := TauCeti.norm_sum_sub_tsum_mul_smoothCutoff_le ha hν0' hνs' hνm hε hε1
    (X := x) (by linarith)
  simp only [norm_zero, zero_div, add_zero, zero_mul, sub_zero, h1η] at hcont
  set S := ∑' n : ℕ, a n * TauCeti.smoothCutoff ν (√x)⁻¹ (n / x)
  have hdec : ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, χ n * (Λ n : ℂ) = (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, a n - S) + S := by
    rw [sub_add_cancel]; rfl
  -- the logarithms on the left edge
  have hlogsq : Real.log (x ^ 2) = 2 * Real.log x := by rw [Real.log_pow]; norm_num
  have hlogA : Real.log (x + 2) ≤ 2 * Real.log x := by
    rw [← hlogsq]; exact Real.log_le_log (by positivity) (by nlinarith)
  have hlogP : Real.log (1 + x / (1 / 2 + g)) ≤ 2 * Real.log x := by
    rw [← hlogsq]
    refine Real.log_le_log (by positivity) ?_
    have : x / (1 / 2 + g) ≤ 2 * x := by rw [div_le_iff₀ (by linarith)]; nlinarith
    nlinarith
  have hlogP0 : 0 ≤ Real.log (1 + x / (1 / 2 + g)) := Real.log_nonneg (by
    have : 0 ≤ x / (1 / 2 + g) := by positivity
    linarith)
  have hy : √x ≤ x ^ (1 / 2 + g) := by
    rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have harith := wing_terms_le hC0 hCg0 hg0 hg4 hs1 hxs hL1 (Real.log_nonneg (by linarith))
    hlogA hlogP0 hlogP hy
  rw [hdec]
  calc ‖(∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, a n - S) + S‖ ≤ ‖∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, a n - S‖ + ‖S‖ :=
        norm_add_le _ _
    _ ≤ _ := by linarith

/-! ## The sharp forms: `√x log³ x` (gap `a = 1 / log x`) and `x^(1/2 + δ)` -/

/-- For `x ≥ 55`, `log x ≥ 4` (as `e⁴ < 55`). -/
theorem four_le_log_of_le (x : ℝ) (hx : 55 ≤ x) : 4 ≤ Real.log x := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have h := Real.exp_one_lt_d9
  have h0 := Real.exp_pos 1
  calc Real.exp 4 = Real.exp 1 ^ 4 := by rw [Real.exp_one_pow]; norm_num
    _ ≤ 2.7182818286 ^ 4 := by gcongr
    _ ≤ 55 := by norm_num
    _ ≤ x := hx

open scoped ArithmeticFunction.vonMangoldt in
/-- `‖∑_{n ≤ x} χ(n) Λ(n)‖ ≤ D e √x log³ x` for `x ≥ 55`: the gap `a = 1 / log x`. -/
theorem psi_chi_le_sqrt_log_cube (hχ : χ ≠ 1) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 55 ≤ x →
    ‖∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, χ n * (Λ n : ℂ)‖ ≤ C * √x * Real.log x ^ 3 := by
  obtain ⟨D, hD0, hD⟩ := psi_chi_le_of_gap hχ
  refine ⟨D * Real.exp 1, by positivity, fun x hx ↦ ?_⟩
  have hx0 : 0 < x := by linarith
  have hL4 := four_le_log_of_le x hx
  have hL0 : 0 < Real.log x := by linarith
  have ha0 : 0 < (Real.log x)⁻¹ := inv_pos.2 hL0
  have ha4 : (Real.log x)⁻¹ ≤ 1 / 4 := by
    rw [inv_eq_one_div, div_le_div_iff₀ hL0 (by norm_num)]; linarith
  refine (hD _ ha0 ha4 x (by linarith)).trans ?_
  have hpow : x ^ (1 / 2 + (Real.log x)⁻¹) ≤ √x * Real.exp 1 := by
    rw [Real.rpow_add hx0, Real.sqrt_eq_rpow]
    exact mul_le_mul_of_nonneg_left Real.rpow_inv_log_le_exp_one (by positivity)
  calc D * x ^ (1 / 2 + (Real.log x)⁻¹) * Real.log x ^ 2 / (Real.log x)⁻¹
      = D * x ^ (1 / 2 + (Real.log x)⁻¹) * Real.log x ^ 3 := by field_simp
    _ ≤ D * (√x * Real.exp 1) * Real.log x ^ 3 := by gcongr
    _ = D * Real.exp 1 * √x * Real.log x ^ 3 := by ring

open scoped ArithmeticFunction.vonMangoldt in
/-- **`∑_{n ≤ x} χ(n) Λ(n) = O(√x log³ x)` for every nonprincipal `χ`, from the proved GRH.** -/
theorem psi_chi_le_of_GRH (hχ : χ ≠ 1) : ∃ C x₀ : ℝ, ∀ x ≥ x₀,
    ‖∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, χ n * (Λ n : ℂ)‖ ≤ C * √x * Real.log x ^ 3 := by
  obtain ⟨C, -, hC⟩ := psi_chi_le_sqrt_log_cube hχ
  exact ⟨C, 55, fun x hx ↦ hC x hx⟩

open scoped ArithmeticFunction.vonMangoldt in
/-- **`∑_{n ≤ x} χ(n) Λ(n) = O(x^(1/2 + δ))` for every `δ > 0`, from the proved GRH.** The gap
`a = min(δ/2, 1/4)` and `log² x ≤ 16 x^(δ/2) / δ²`. -/
theorem psi_chi_le_rpow_of_GRH (hχ : χ ≠ 1) (δ : ℝ) (hδ : 0 < δ) : ∃ C x₀ : ℝ, ∀ x ≥ x₀,
    ‖∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, χ n * (Λ n : ℂ)‖ ≤ C * x ^ (1 / 2 + δ) := by
  obtain ⟨D, hD0, hD⟩ := psi_chi_le_of_gap hχ
  have ha0 : 0 < min (δ / 2) (1 / 4) := lt_min (by positivity) (by norm_num)
  have ha4 : min (δ / 2) (1 / 4) ≤ 1 / 4 := min_le_right _ _
  have haδ : min (δ / 2) (1 / 4) ≤ δ / 2 := min_le_left _ _
  refine ⟨D / ((δ / 4) ^ 2 * min (δ / 2) (1 / 4)), 3, fun x hx ↦ ?_⟩
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  refine (hD _ ha0 ha4 x hx).trans ?_
  have hL : Real.log x ≤ x ^ (δ / 4) / (δ / 4) := Real.log_le_rpow_div hx0.le (by positivity)
  have hL2 : Real.log x ^ 2 ≤ x ^ (δ / 2) / (δ / 4) ^ 2 := by
    calc Real.log x ^ 2 ≤ (x ^ (δ / 4) / (δ / 4)) ^ 2 :=
          pow_le_pow_left₀ (Real.log_nonneg hx1) hL 2
      _ = x ^ (δ / 2) / (δ / 4) ^ 2 := by
        rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
        congr 2; push_cast; ring
  have hxa : x ^ (1 / 2 + min (δ / 2) (1 / 4)) ≤ x ^ (1 / 2 + δ / 2) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hsplit : x ^ (1 / 2 + δ) = x ^ (1 / 2 + δ / 2) * x ^ (δ / 2) := by
    rw [← Real.rpow_add hx0]; congr 1; ring
  rw [hsplit]
  calc D * x ^ (1 / 2 + min (δ / 2) (1 / 4)) * Real.log x ^ 2 / min (δ / 2) (1 / 4)
      ≤ D * x ^ (1 / 2 + δ / 2) * (x ^ (δ / 2) / (δ / 4) ^ 2) / min (δ / 2) (1 / 4) := by gcongr
    _ = D / ((δ / 4) ^ 2 * min (δ / 2) (1 / 4)) * (x ^ (1 / 2 + δ / 2) * x ^ (δ / 2)) := by
        field_simp

/-! ## The wing character mod 6: `+1` on `6k + 1`, `-1` on `6k - 1`, `0` on multiples of 2 or 3 -/

/-- The unit part of the wing character: `+1` at the unit `1`, `-1` at the unit `5` of `ZMod 6`. -/
def chi6Hom : (ZMod 6)ˣ →* ℤˣ where
  toFun u := if (u : ZMod 6) = 1 then 1 else -1
  map_one' := by decide
  map_mul' := by decide

/-- The wing character mod 6 (the quadratic character mod 3 lifted to level 6). -/
noncomputable def chi6 : DirichletCharacter ℂ 6 :=
  (MulChar.ofUnitHom chi6Hom).ringHomComp (Int.castRingHom ℂ)

/-- The real weight of the wing character: `+1` on `6k + 1`, `-1` on `6k - 1` (`≡ 5 mod 6`),
`0` otherwise. -/
def w6 (n : ℕ) : ℝ := if n % 6 = 1 then 1 else if n % 6 = 5 then -1 else 0

theorem chi6_apply (n : ℕ) : chi6 n = if n % 6 = 1 then 1 else if n % 6 = 5 then -1 else 0 := by
  rw [chi6, MulChar.ringHomComp_apply, ← ZMod.natCast_mod n 6]
  have h := Nat.mod_lt n (by norm_num : 0 < 6)
  have hnu : ∀ m : ℕ, ¬ m.Coprime 6 → MulChar.ofUnitHom chi6Hom (m : ZMod 6) = 0 := fun m hm ↦
    MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])
  have hu : ∀ m : ℕ, (hm : m.Coprime 6) → MulChar.ofUnitHom chi6Hom (m : ZMod 6) =
      ((chi6Hom (ZMod.unitOfCoprime m hm) : ℤˣ) : ℤ) := fun m hm ↦ by
    rw [← ZMod.coe_unitOfCoprime m hm, MulChar.ofUnitHom_coe]
  have hdef : ∀ u : (ZMod 6)ˣ, chi6Hom u = if (u : ZMod 6) = 1 then 1 else -1 := fun _ ↦ rfl
  interval_cases hr : n % 6
  · rw [hnu 0 (by decide)]; simp
  · rw [hu 1 (by decide), hdef, ZMod.coe_unitOfCoprime, ite_eq_left (by simp)]; simp
  · rw [hnu 2 (by decide)]; simp
  · rw [hnu 3 (by decide)]; simp
  · rw [hnu 4 (by decide)]; simp
  · rw [hu 5 (by decide), hdef, ZMod.coe_unitOfCoprime, ite_eq_right (by decide)]; simp

theorem chi6_eq_w6 (n : ℕ) : chi6 n = (w6 n : ℂ) := by
  rw [chi6_apply, w6]; split_ifs <;> simp

theorem chi6_ne_one : chi6 ≠ 1 := by
  intro h
  have h5 := chi6_apply 5
  rw [h] at h5
  have : (1 : DirichletCharacter ℂ 6) ((5 : ℕ) : ZMod 6) = 1 :=
    MulChar.one_apply ((ZMod.isUnit_iff_coprime 5 6).2 (by decide))
  rw [this] at h5
  norm_num at h5

theorem abs_w6_le_one (n : ℕ) : |w6 n| ≤ 1 := by
  rw [w6]; split_ifs <;> simp

/-- A prime `q ≥ 5` sits at `6k + 1` or `6k - 1` (copied from the Sharp file). -/
theorem prime_seat (q : ℕ) (hq : q.Prime) (h5 : 5 ≤ q) : q % 6 = 1 ∨ q % 6 = 5 := by
  by_contra h
  have h23 : 2 ∣ q ∨ 3 ∣ q := by omega
  rcases h23 with h2 | h3
  · have := (Nat.Prime.eq_one_or_self_of_dvd hq 2 h2); omega
  · have := (Nat.Prime.eq_one_or_self_of_dvd hq 3 h3); omega

/-! ## The twisted Chebyshev sums `ψ₆`, `θ₆` and the twisted prime sum -/

open scoped ArithmeticFunction.vonMangoldt Chebyshev

/-- `ψ₆(x) = ∑_{n ≤ x} w₆(n) Λ(n)`: the von Mangoldt mass of the `6k + 1` family minus that of
the `6k - 1` family. -/
noncomputable def psi6 (x : ℝ) : ℝ := ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, w6 n * Λ n

/-- `θ₆(x) = ∑_{p ≤ x prime} w₆(p) log p`. -/
noncomputable def theta6 (x : ℝ) : ℝ := ∑ p ∈ Finset.Icc 0 ⌊x⌋₊ with p.Prime, w6 p * Real.log p

/-- `∑_{p ≤ x prime} w₆(p)`: the `6k + 1` prime count minus the `6k - 1` prime count. -/
noncomputable def primeSum6 (x : ℝ) : ℝ := ∑ p ∈ Finset.Icc 0 ⌊x⌋₊ with p.Prime, w6 p

theorem psi6_eq (x : ℝ) : (psi6 x : ℂ) = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, chi6 n * (Λ n : ℂ) := by
  simp only [psi6, chi6_eq_w6]; push_cast; rfl

/-- **`ψ₆(x) = O(√x log³ x)` from the proved GRH** (`psi_chi_le_sqrt_log_cube` at `χ = χ₆`). -/
theorem psi6_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 55 ≤ x → |psi6 x| ≤ C * √x * Real.log x ^ 3 := by
  obtain ⟨C, hC0, hC⟩ := psi_chi_le_sqrt_log_cube chi6_ne_one
  refine ⟨C, hC0, fun x hx ↦ ?_⟩
  have := hC x hx
  rwa [← psi6_eq, Complex.norm_real, Real.norm_eq_abs] at this

theorem theta6_eq_sum_Ioc (x : ℝ) :
    theta6 x = ∑ p ∈ Finset.Ioc 0 ⌊x⌋₊ with p.Prime, w6 p * Real.log p := by
  rw [theta6, Finset.sum_filter, Finset.sum_filter, ← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le _)]
  simp

/-- `|ψ₆(x) - θ₆(x)| ≤ ψ(x) - θ(x)`: the prime powers. -/
theorem abs_psi6_sub_theta6_le (x : ℝ) : |psi6 x - theta6 x| ≤ ψ x - θ x := by
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, theta6_eq_sum_Ioc, psi6, Finset.sum_filter,
    Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ ↦ ?_)
  split_ifs with h
  · rw [ArithmeticFunction.vonMangoldt_apply_prime h, sub_self, abs_zero]
  · rw [sub_zero, abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg (abs_w6_le_one n)

theorem abs_theta6_le_theta (x : ℝ) : |theta6 x| ≤ θ x := by
  rw [theta6_eq_sum_Ioc, Chebyshev.theta]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p hp ↦ ?_)
  have hp2 := (Finset.mem_filter.1 hp).2.two_le
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp2.trans' one_le_two)
  rw [abs_mul, abs_of_nonneg hlog]
  exact mul_le_of_le_one_left hlog (abs_w6_le_one p)

/-- `|θ₆(t)| ≤ K √t log³ t` for every `t ≥ 2`: GRH for `t ≥ 55`, the trivial bound below. -/
theorem theta6_le : ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 2 ≤ t → |theta6 t| ≤ K * √t * Real.log t ^ 3 := by
  obtain ⟨C, hC0, hC⟩ := psi6_le
  refine ⟨C + 6 + 128, by positivity, fun t ht ↦ ?_⟩
  have ht0 : 0 < t := by linarith
  have hs0 : 0 ≤ √t := Real.sqrt_nonneg t
  have hl2 : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hL : 1 / 2 ≤ Real.log t := hl2.trans (Real.log_le_log two_pos ht)
  have hL3 : 1 / 8 ≤ Real.log t ^ 3 := by nlinarith [sq_nonneg (Real.log t - 1 / 2)]
  have hsL0 : 0 ≤ √t * Real.log t ^ 3 := by positivity
  rcases le_or_gt 55 t with h55 | h55
  · -- `x ≥ 55`: `|θ₆| ≤ |ψ₆| + (ψ - θ)`, and `ψ - θ ≤ 6 √t log t`
    have hL4 := four_le_log_of_le t h55
    have hpt : ψ t - θ t ≤ 6 * (√t * Real.log t) := by
      have h := Chebyshev.psi_sub_theta_le_log_four_mul ht0.le
      have hl4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      have hl4b : Real.log 4 ≤ 2 := by rw [hl4]; linarith [Real.log_two_lt_d9]
      have hl40 : 0 ≤ Real.log 4 := by rw [hl4]; positivity
      have hcube : t ^ ((1 : ℝ) / 3) ≤ √t := by
        rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      have hmax : max (Real.log t / Real.log 2 - 2) 0 ≤ Real.log t / Real.log 2 :=
        max_le (by linarith) (by positivity)
      have hprod : max (Real.log t / Real.log 2 - 2) 0 * t ^ ((1 : ℝ) / 3) ≤
          Real.log t / Real.log 2 * √t :=
        mul_le_mul hmax hcube (by positivity) (by positivity)
      have h1 : Real.log 4 * √t ≤ 2 * (√t * Real.log t) := by
        calc Real.log 4 * √t ≤ 2 * √t := mul_le_mul_of_nonneg_right hl4b hs0
          _ ≤ 2 * (√t * Real.log t) := by nlinarith
      have h2 : Real.log 4 * (Real.log t / Real.log 2 * √t) = 2 * (√t * Real.log t) := by
        rw [hl4]; field_simp
      have h3 := mul_le_mul_of_nonneg_left hprod hl40
      nlinarith
    have hL3' : Real.log t ≤ Real.log t ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
    have htri : |theta6 t| ≤ |psi6 t| + |psi6 t - theta6 t| := by
      have := abs_sub_abs_le_abs_sub (theta6 t) (psi6 t); rw [abs_sub_comm] at this; linarith
    calc |theta6 t| ≤ |psi6 t| + |psi6 t - theta6 t| := htri
      _ ≤ C * √t * Real.log t ^ 3 + 6 * (√t * Real.log t) := by
          linarith [hC t h55, abs_psi6_sub_theta6_le t]
      _ ≤ C * √t * Real.log t ^ 3 + 6 * (√t * Real.log t ^ 3) := by gcongr
      _ ≤ (C + 6 + 128) * √t * Real.log t ^ 3 := by nlinarith
  · -- `2 ≤ t < 55`: `|θ₆| ≤ θ(t) ≤ 2t ≤ 16 √t ≤ 128 √t log³ t`
    have hθ : θ t ≤ Real.log 4 * t := Chebyshev.theta_le_log4_mul_x ht0.le
    have hl4 : Real.log 4 ≤ 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast
      linarith [Real.log_two_lt_d9]
    have hsq : t = √t * √t := (Real.mul_self_sqrt ht0.le).symm
    have hs8 : √t ≤ 8 := by
      rw [show (8 : ℝ) = √64 by rw [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by linarith)
    calc |theta6 t| ≤ θ t := abs_theta6_le_theta t
      _ ≤ 2 * t := by nlinarith
      _ = 2 * √t * √t := by rw [mul_assoc, Real.mul_self_sqrt ht0.le]
      _ ≤ 16 * √t := by nlinarith
      _ ≤ 128 * (√t * Real.log t ^ 3) := by nlinarith
      _ ≤ (C + 6 + 128) * √t * Real.log t ^ 3 := by nlinarith

/-- **Abel summation for the twisted prime sum** (the proof of Mathlib's
`Chebyshev.primeCounting_eq_theta_div_log_add_integral` with the weight `w₆`): for `x ≥ 2`,
`∑_{p ≤ x} w₆(p) = θ₆(x) / log x + ∫_2^x θ₆(t) / (t log² t) dt`. -/
theorem primeSum6_eq_theta6_div_log_add_integral {x : ℝ} (hx : 2 ≤ x) :
    primeSum6 x = theta6 x / Real.log x + ∫ t in (2 : ℝ)..x, theta6 t / (t * Real.log t ^ 2) := by
  classical
  let a : ℕ → ℝ := Set.indicator (Set.ofPred Nat.Prime) (fun n ↦ w6 n * Real.log n)
  have ha (t : ℝ) : ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, a k = theta6 t := by
    rw [theta6, Finset.sum_filter]
    exact Finset.sum_congr rfl fun n _ ↦ by simp [a, Set.indicator_apply]
  rw [primeSum6, Finset.sum_filter]
  trans ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (Real.log n)⁻¹ * a n
  · refine Finset.sum_congr rfl fun n hn ↦ ?_
    split_ifs with h
    · have : Real.log n ≠ 0 :=
        Real.log_ne_zero_of_pos_of_ne_one (mod_cast h.pos) (mod_cast h.ne_one)
      simp [a, h, field]
    · simp [a, h]
  rw [sum_mul_eq_sub_integral_mul₁ a (f := fun n ↦ (Real.log n)⁻¹) (by simp [a]) (by simp [a]),
    ← intervalIntegral.integral_of_le hx]
  · have int_deriv (f : ℝ → ℝ) :
        ∫ u in (2 : ℝ)..x, deriv (fun x ↦ (Real.log x)⁻¹) u * f u =
        ∫ u in (2 : ℝ)..x, f u * -(u * Real.log u ^ 2)⁻¹ :=
      intervalIntegral.integral_congr fun u _ ↦ by simp [Real.deriv_inv_log_apply, field]
    rw [int_deriv, ha]
    simp_rw [ha]
    have hneg : ∫ u in (2 : ℝ)..x, theta6 u * -(u * Real.log u ^ 2)⁻¹ =
        -∫ t in (2 : ℝ)..x, theta6 t / (t * Real.log t ^ 2) := by
      rw [← intervalIntegral.integral_neg]
      exact intervalIntegral.integral_congr fun u _ ↦ by rw [div_eq_mul_inv]; ring
    rw [hneg, div_eq_inv_mul]; ring
  · intro z ⟨_, _⟩
    have : z ≠ 0 := by linarith
    have : Real.log z ≠ 0 := by apply Real.log_ne_zero_of_pos_of_ne_one <;> linarith
    fun_prop
  · refine ContinuousOn.integrableOn_Icc fun z ⟨_, _⟩ ↦ ContinuousWithinAt.congr ?_
      (fun _ _ ↦ Real.deriv_inv_log_apply) Real.deriv_inv_log_apply
    have : z ≠ 0 := by linarith
    have : Real.log z ^ 2 ≠ 0 := by
      refine pow_ne_zero 2 <| Real.log_ne_zero_of_pos_of_ne_one ?_ ?_ <;> linarith
    exact ContinuousAt.continuousWithinAt <| by fun_prop

/-- **The twisted prime sum is `O(√x log² x)`**: `|∑_{p ≤ x} w₆(p)| ≤ C √x log² x` for `x ≥ 3`,
by Abel summation from `theta6_le`. -/
theorem primeSum6_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 3 ≤ x →
    |primeSum6 x| ≤ C * √x * Real.log x ^ 2 := by
  obtain ⟨K, hK0, hK⟩ := theta6_le
  refine ⟨3 * K, by positivity, fun x hx ↦ ?_⟩
  have hx0 : 0 < x := by linarith
  have hx2 : 2 ≤ x := by linarith
  have hL1 : 1 ≤ Real.log x :=
    (Real.le_log_iff_exp_le hx0).2 (by linarith [Real.exp_one_lt_d9])
  have hL0 : 0 < Real.log x := by linarith
  have hs0 : 0 ≤ √x := Real.sqrt_nonneg x
  rw [primeSum6_eq_theta6_div_log_add_integral hx2]
  -- the boundary term
  have h1 : |theta6 x / Real.log x| ≤ K * √x * Real.log x ^ 2 := by
    rw [abs_div, abs_of_pos hL0, div_le_iff₀ hL0]
    calc |theta6 x| ≤ K * √x * Real.log x ^ 3 := hK x hx2
      _ = K * √x * Real.log x ^ 2 * Real.log x := by ring
  -- the integral: `|θ₆(t)| / (t log² t) ≤ K log t / √t ≤ K log x · t^(-1/2)`
  have hbound : ∀ t ∈ Set.Ioc (2 : ℝ) x, ‖theta6 t / (t * Real.log t ^ 2)‖ ≤
      K * Real.log x * t ^ (-(1 / 2) : ℝ) := fun t ht ↦ by
    have ht0 : 0 < t := by linarith [ht.1]
    have hlt : (1 : ℝ) / 2 ≤ Real.log t := by
      linarith [Real.log_two_gt_d9, Real.log_le_log two_pos ht.1.le]
    have hlx : Real.log t ≤ Real.log x := Real.log_le_log ht0 ht.2
    have hst : t = √t * √t := (Real.mul_self_sqrt ht0.le).symm
    have hpow : t ^ (-(1 / 2) : ℝ) = (√t)⁻¹ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg ht0.le]
    have hden : 0 < t * Real.log t ^ 2 := mul_pos ht0 (pow_pos (by linarith) 2)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hden, div_le_iff₀ hden, hpow]
    have hinv : (√t)⁻¹ * t = √t := by
      rw [inv_mul_eq_div, div_eq_iff (ne_of_gt (Real.sqrt_pos.2 ht0)), Real.mul_self_sqrt ht0.le]
    calc |theta6 t| ≤ K * √t * Real.log t ^ 3 := hK t ht.1.le
      _ = K * Real.log t * ((√t)⁻¹ * t * Real.log t ^ 2) := by rw [hinv]; ring
      _ = K * Real.log t * (√t)⁻¹ * (t * Real.log t ^ 2) := by ring
      _ ≤ K * Real.log x * (√t)⁻¹ * (t * Real.log t ^ 2) := by gcongr
  have hint : IntervalIntegrable (fun t : ℝ ↦ K * Real.log x * t ^ (-(1 / 2) : ℝ))
      MeasureTheory.volume 2 x :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul _
  have h2 : ‖∫ t in (2 : ℝ)..x, theta6 t / (t * Real.log t ^ 2)‖ ≤
      ∫ t in (2 : ℝ)..x, K * Real.log x * t ^ (-(1 / 2) : ℝ) :=
    intervalIntegral.norm_integral_le_of_norm_le hx2 (MeasureTheory.ae_of_all _ hbound) hint
  have h3 : ∫ t in (2 : ℝ)..x, K * Real.log x * t ^ (-(1 / 2) : ℝ) ≤ 2 * K * √x * Real.log x := by
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num))]
    have hxh : x ^ (-(1 / 2) + 1 : ℝ) = √x := by rw [Real.sqrt_eq_rpow]; norm_num
    have h2h : (0 : ℝ) ≤ 2 ^ (-(1 / 2) + 1 : ℝ) := by positivity
    rw [hxh]
    have : (√x - 2 ^ (-(1 / 2) + 1 : ℝ)) / (-(1 / 2) + 1) ≤ 2 * √x := by
      rw [div_le_iff₀ (by norm_num)]; linarith
    calc K * Real.log x * ((√x - 2 ^ (-(1 / 2) + 1 : ℝ)) / (-(1 / 2) + 1))
        ≤ K * Real.log x * (2 * √x) := by gcongr
      _ = 2 * K * √x * Real.log x := by ring
  rw [Real.norm_eq_abs] at h2
  have hL2 : Real.log x ≤ Real.log x ^ 2 := by nlinarith
  calc |theta6 x / Real.log x + ∫ t in (2 : ℝ)..x, theta6 t / (t * Real.log t ^ 2)|
      ≤ |theta6 x / Real.log x| + |∫ t in (2 : ℝ)..x, theta6 t / (t * Real.log t ^ 2)| :=
        abs_add_le _ _
    _ ≤ K * √x * Real.log x ^ 2 + 2 * K * √x * Real.log x := by linarith
    _ ≤ K * √x * Real.log x ^ 2 + 2 * K * √x * Real.log x ^ 2 := by gcongr
    _ = 3 * K * √x * Real.log x ^ 2 := by ring

/-! ## The wing families in wall words: `p = 6k + f`, facing `f = ±1` -/

open Classical in
/-- The wing count with facing `f`: the primes `p ≤ x` seated at `p = 6k + f`. For `f = 1` this
is the `6k + 1` family, for `f = -1` the `6k - 1` family (as in the wall definitions of the Sharp
file: `wall_walk_seat`, `passes`). -/
noncomputable def wingCount (f : ℤ) (x : ℝ) : ℕ :=
  Finset.card (Finset.filter (fun p : ℕ ↦ Nat.Prime p ∧ ∃ k : ℤ, (p : ℤ) = 6 * k + f)
    (Finset.Icc 0 ⌊x⌋₊))

open Classical in
theorem wingCount_one (x : ℝ) : wingCount 1 x =
    Finset.card (Finset.filter (fun p : ℕ ↦ Nat.Prime p ∧ p % 6 = 1) (Finset.Icc 0 ⌊x⌋₊)) := by
  unfold wingCount
  congr 1
  refine Finset.filter_congr fun p _ ↦ and_congr_right fun _ ↦ ?_
  constructor
  · rintro ⟨k, hk⟩; omega
  · intro h; exact ⟨(p : ℤ) / 6, by omega⟩

open Classical in
theorem wingCount_neg_one (x : ℝ) : wingCount (-1) x =
    Finset.card (Finset.filter (fun p : ℕ ↦ Nat.Prime p ∧ p % 6 = 5) (Finset.Icc 0 ⌊x⌋₊)) := by
  unfold wingCount
  congr 1
  refine Finset.filter_congr fun p _ ↦ and_congr_right fun _ ↦ ?_
  constructor
  · rintro ⟨k, hk⟩; omega
  · intro h; exact ⟨(p : ℤ) / 6 + 1, by omega⟩

/-- `∑_{p ≤ x} w₆(p) = #(6k + 1 family) - #(6k - 1 family)`. -/
theorem primeSum6_eq_wingCount_sub (x : ℝ) :
    primeSum6 x = (wingCount 1 x : ℝ) - wingCount (-1) x := by
  rw [wingCount_one, wingCount_neg_one, primeSum6, ← Finset.filter_filter, ← Finset.filter_filter,
    ← Finset.sum_boole, ← Finset.sum_boole, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  simp only [w6]
  split_ifs <;> first | (exfalso; omega) | norm_num

/-- For `x ≥ 3`, the two wing families and the two mirrors `2, 3` exhaust the primes up to `x`. -/
theorem wingCount_add_wingCount (x : ℝ) (hx : 3 ≤ x) :
    wingCount 1 x + wingCount (-1) x + 2 = Nat.primeCounting ⌊x⌋₊ := by
  rw [wingCount_one, wingCount_neg_one, ← Nat.primesLE_card_eq_primeCounting]
  have hS : Nat.primesLE ⌊x⌋₊ = Finset.filter Nat.Prime (Finset.Icc 0 ⌊x⌋₊) := by
    ext p; simp [Nat.mem_primesLE]
  rw [hS]
  have h3 : 3 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have h1 := Finset.card_filter_add_card_filter_not
    (s := Finset.filter Nat.Prime (Finset.Icc 0 ⌊x⌋₊)) (fun p ↦ p % 6 = 1)
  have h2 := Finset.card_filter_add_card_filter_not
    (s := Finset.filter (fun p ↦ Nat.Prime p ∧ ¬ p % 6 = 1) (Finset.Icc 0 ⌊x⌋₊)) (fun p ↦ p % 6 = 5)
  simp only [Finset.filter_filter] at h1 h2
  have hB : Finset.filter (fun p ↦ (Nat.Prime p ∧ ¬ p % 6 = 1) ∧ p % 6 = 5) (Finset.Icc 0 ⌊x⌋₊) =
      Finset.filter (fun p : ℕ ↦ Nat.Prime p ∧ p % 6 = 5) (Finset.Icc 0 ⌊x⌋₊) := by
    refine Finset.filter_congr fun p _ ↦ ?_
    constructor
    · rintro ⟨⟨hp, -⟩, h5⟩; exact ⟨hp, h5⟩
    · rintro ⟨hp, h5⟩; exact ⟨⟨hp, by omega⟩, h5⟩
  have hC : Finset.filter (fun p ↦ (Nat.Prime p ∧ ¬ p % 6 = 1) ∧ ¬ p % 6 = 5) (Finset.Icc 0 ⌊x⌋₊) =
      {2, 3} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨-, ⟨hp, h1⟩, h5⟩
      rcases (show p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p by have := hp.two_le; omega) with h | h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · subst h; exact absurd hp (by decide)
      · exact absurd (prime_seat p hp h) (by omega)
    · rintro (rfl | rfl)
      · exact ⟨⟨Nat.zero_le _, by omega⟩, ⟨Nat.prime_two, by omega⟩, by omega⟩
      · exact ⟨⟨Nat.zero_le _, by omega⟩, ⟨Nat.prime_three, by omega⟩, by omega⟩
  rw [hB, hC, Finset.card_pair (by norm_num)] at h2
  omega

/-! ## The wing families meet GRH -/

/-- **The lead of one wing family over the other is at most square-root size.** There are `C`
and `x₀` such that for every `x ≥ x₀`,
`|#{p ≤ x : p = 6k - 1} - #{p ≤ x : p = 6k + 1}| ≤ C √x log² x`.
The theorem bounds the size of the lead; it does not fix its sign. -/
theorem wing_lead_le : ∃ C x₀ : ℝ, ∀ x ≥ x₀,
    |(wingCount (-1) x : ℝ) - wingCount 1 x| ≤ C * √x * Real.log x ^ 2 := by
  obtain ⟨C, -, hC⟩ := primeSum6_le
  refine ⟨C, 3, fun x hx ↦ ?_⟩
  rw [abs_sub_comm, ← primeSum6_eq_wingCount_sub]
  exact hC x hx

/-- **Each wing family carries half the primes to square-root accuracy.** For the facing
`f = ±1` there are `C` and `x₀` such that for every `x ≥ x₀`,
`|#{p ≤ x : p = 6k + f} - Li(x) / 2| ≤ C √x log² x`. From `primeSum6_le` (GRH for `χ₆`) and the
Sharp file's `primeCounting_sub_logIntegral_le_sqrt_log_sq` (RH). -/
theorem wing_count_sub_half_li (f : ℤ) (hf : f = 1 ∨ f = -1) : ∃ C x₀ : ℝ, ∀ x ≥ x₀,
    |(wingCount f x : ℝ) - TauCeti.Real.logIntegral x / 2| ≤ C * √x * Real.log x ^ 2 := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := primeSum6_le
  obtain ⟨C₂, hC₂0, hC₂⟩ := WallsMeetRHSharp.primeCounting_sub_logIntegral_le_sqrt_log_sq
  refine ⟨(C₁ + C₂ + 1) / 2, 55, fun x hx ↦ ?_⟩
  have hx3 : 3 ≤ x := by linarith
  have hsum := wingCount_add_wingCount x hx3
  have hsumR : (wingCount 1 x : ℝ) + wingCount (-1) x + 2 = Nat.primeCounting ⌊x⌋₊ := by
    exact_mod_cast hsum
  have hdiff := hC₁ x hx3
  rw [primeSum6_eq_wingCount_sub] at hdiff
  have hπ := hC₂ x hx
  have hL4 := four_le_log_of_le x hx
  have hs1 : 1 ≤ √x := Real.one_le_sqrt.2 (by linarith)
  have hL16 : 16 ≤ Real.log x ^ 2 := by nlinarith
  have h1 : 16 ≤ √x * Real.log x ^ 2 := by nlinarith
  rw [abs_le] at hdiff hπ ⊢
  rcases hf with rfl | rfl
  · constructor <;> linarith
  · constructor <;> linarith

/-- **The wing families meet the proved GRH.** There are `C` and `x₀` such that for every
`x ≥ x₀`: the `6k + 1` family and the `6k - 1` family each count `Li(x)/2 + O(√x log² x)`
primes up to `x`, and the lead of the `6k - 1` family over the `6k + 1` family is at most
`C √x log² x` in absolute value. -/
theorem wing_families_meet_grh : ∃ C x₀ : ℝ, ∀ x ≥ x₀,
    |(wingCount 1 x : ℝ) - TauCeti.Real.logIntegral x / 2| ≤ C * √x * Real.log x ^ 2 ∧
    |(wingCount (-1) x : ℝ) - TauCeti.Real.logIntegral x / 2| ≤ C * √x * Real.log x ^ 2 ∧
    |(wingCount (-1) x : ℝ) - wingCount 1 x| ≤ C * √x * Real.log x ^ 2 := by
  obtain ⟨C₁, x₁, h₁⟩ := wing_count_sub_half_li 1 (Or.inl rfl)
  obtain ⟨C₂, x₂, h₂⟩ := wing_count_sub_half_li (-1) (Or.inr rfl)
  obtain ⟨C₃, x₃, h₃⟩ := wing_lead_le
  refine ⟨|C₁| + |C₂| + |C₃|, max (max x₁ x₂) (max x₃ 3), fun x hx ↦ ?_⟩
  have hx1 : x₁ ≤ x := le_trans (le_max_left _ _) ((le_max_left _ _).trans hx)
  have hx2 : x₂ ≤ x := le_trans (le_max_right _ _) ((le_max_left _ _).trans hx)
  have hx3 : x₃ ≤ x := le_trans (le_max_left _ _) ((le_max_right _ _).trans hx)
  have hx0 : 3 ≤ x := le_trans (le_max_right _ _) ((le_max_right _ _).trans hx)
  have hE : 0 ≤ √x * Real.log x ^ 2 := by positivity
  have key : ∀ C : ℝ, C ≤ |C₁| + |C₂| + |C₃| →
      C * √x * Real.log x ^ 2 ≤ (|C₁| + |C₂| + |C₃|) * √x * Real.log x ^ 2 := fun C hC ↦ by
    rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right hC hE
  have hc1 := le_abs_self C₁
  have hc2 := le_abs_self C₂
  have hc3 := le_abs_self C₃
  have ha1 := abs_nonneg C₁
  have ha2 := abs_nonneg C₂
  have ha3 := abs_nonneg C₃
  exact ⟨(h₁ x hx1).trans (key _ (by linarith)), (h₂ x hx2).trans (key _ (by linarith)),
    (h₃ x hx3).trans (key _ (by linarith))⟩

/-- The statement of `psi_chi_le_of_GRH` at the wing character `χ₆`. -/
theorem psi_chi6_le_of_GRH : ∃ C x₀ : ℝ, ∀ x ≥ x₀,
    ‖∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, chi6 n * (Λ n : ℂ)‖ ≤ C * √x * Real.log x ^ 3 :=
  psi_chi_le_of_GRH chi6_ne_one

end WingFamiliesGRH

#print axioms LFunction_eq_zero_re
#print axioms WingFamiliesGRH.logDeriv_LFunction_le_of_GRH_gap
#print axioms WingFamiliesGRH.psi_chi_le_of_gap
#print axioms WingFamiliesGRH.psi_chi_le_of_GRH
#print axioms WingFamiliesGRH.psi_chi_le_rpow_of_GRH
#print axioms WingFamiliesGRH.psi_chi6_le_of_GRH
#print axioms WingFamiliesGRH.chi6_apply
#print axioms WingFamiliesGRH.primeSum6_le
#print axioms WingFamiliesGRH.wing_lead_le
#print axioms WingFamiliesGRH.wing_count_sub_half_li
#print axioms WingFamiliesGRH.wing_families_meet_grh

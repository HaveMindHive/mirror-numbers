import Main
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import TauCeti.NumberTheory.LSeries.SmoothedSum.ZeroFreeRegion
import TauCeti.NumberTheory.LSeries.RiemannZeta.LogDeriv.RightOfCurve
import TauCeti.NumberTheory.Chebyshev.PsiSubTheta
import TauCeti.NumberTheory.Chebyshev.ThetaTransfer

/-!
# The walls meet the proved Riemann hypothesis: the sharp exponents (11-27-2026)

Companion of `WallsMeetRH_v1.0_11-27-2026.lean`, same environment (the locally built community
proof of RH by Alpöge with Claude, Mathlib `31ce06ea`, Tau Ceti pinned). Every step is
kernel-checked.

* Turaq Rayn-McLean's wall count `prime_count_walls` (copied from the first file): for `N ≥ 3`,
  `π(N) = 2 + #{n ≤ N that pass the wall test}`.
* `logDeriv_bound_of_RH_gap`: under RH, `‖ζ′/ζ(s) + 1/(s - 1)‖ ≤ (C / a) log(|Im s| + 2)` on
  `1/2 + a ≤ Re s ≤ 2`, uniformly in the gap `a ∈ (0, 1]`.
* `psi_sub_le_of_gap`: the explicit-formula contour (Tau Ceti's smoothed Perron estimate) at
  `η = 1/2 - a`, `T = x`, `ε = x^(-1/2)` gives `|ψ(x) - x| ≤ D x^(1/2 + a) log² x / a` for every
  `x ≥ 3` and `0 < a ≤ 1/4`, with one absolute constant `D`.
* Step 1 (`a` fixed): `psi_sub_le_of_RH`, `theta_sub_le_of_RH`,
  `primeCounting_sub_logIntegral_le_of_RH`, `walls_meet_rh_half`: error `O(x^(1/2 + δ))` for every
  `δ > 0`.
* Step 2 (`a = 1 / log x`): `psi_sub_le_sqrt_log_cube_of_RH` (`O(√x log³ x)`),
  `theta_sub_le_sqrt_log_cube_of_RH`, `primeCounting_sub_logIntegral_le_sqrt_log_sq_of_RH`
  (`O(√x log² x)`), `walls_meet_rh_sqrt`.

Two private lemmas of Tau Ceti (`finsum_subtype_riemannZeta_eq_sum` of `Window.lean` and
`nonneg_of_norm_mellin_smoothCutoff_le` of `ZeroFreeRegion.lean`) are copied in; Tau Ceti is
Apache-2.0, copyright The Tau Ceti contributors.
-/

open Complex

namespace WallsMeetRHSharp

/-! ## The wall count (Rayn-McLean), copied from `WallsMeetRH_v1.0_11-27-2026.lean` -/

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

/-! ## `ζ′/ζ` right of the critical line, with the gap made explicit -/

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

/-- From the proved `riemannHypothesis`: a zero of `ζ` in the strip `0 < Re ρ < 1` has
`Re ρ = 1/2`. -/
theorem re_eq_half_of_zero {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hζ : riemannZeta ρ = 0) :
    ρ.re = 1 / 2 := by
  refine riemannHypothesis ρ hζ ?_ fun h ↦ by rw [h, one_re] at h1; exact lt_irrefl _ h1
  rintro ⟨n, rfl⟩
  have : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
  rw [this] at h0
  linarith [n.cast_nonneg (α := ℝ)]

/-- Copy of a private lemma of Tau Ceti's `Window.lean` (Apache 2.0): a sum over the zeros of `ζ`
in a closed disc, as a `finsum` over a subtype, is the `Finset` sum over
`riemannZetaZerosClosedBall`. -/
theorem finsum_subtype_riemannZeta_eq_sum' {M : Type*} [AddCommMonoid M] (c : ℂ) (R : ℝ)
    (f : ℂ → M) :
    ∑ᶠ ρ : {z : ℂ // ‖z - c‖ ≤ R ∧ riemannZeta z = 0}, f ρ =
      ∑ z ∈ TauCeti.riemannZetaZerosClosedBall c R, f z := by
  rw [finsum_subtype_eq_finsum_cond (f := f)]
  exact finsum_cond_eq_sum_of_cond_iff _ fun {z} _ ↦ TauCeti.mem_riemannZetaZerosClosedBall.symm

/-- **Under the proved RH, `ζ′/ζ + 1/(s - 1)` is `O(log(|Im s| + 2) / a)` on
`1/2 + a ≤ Re s ≤ 2`**, with one absolute constant for every gap `a ∈ (0, 1]`. The window form
of `ζ′/ζ` (Tau Ceti) leaves the sum over the window zeros, each at distance at least `a` from `s`
because RH puts them on `Re = 1/2`, and the zeros in the disc of radius `4` number
`O(log(|Im s| + 2))` with order. -/
theorem logDeriv_bound_of_RH_gap : ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 0 < a → a ≤ 1 → ∀ s : ℂ, s ≠ 1 →
    1 / 2 + a ≤ s.re → s.re ≤ 2 →
    ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1)‖ ≤ C / a * Real.log (|s.im| + 2) := by
  classical
  obtain ⟨Cw, hCw⟩ := TauCeti.riemannZeta_logDeriv_window
  obtain ⟨Cc, hCc⟩ := TauCeti.exists_finsum_analyticOrderAt_riemannZeta_le 2 4
  refine ⟨|Cw| + |Cc|, by positivity, fun a ha ha1 s hs1 hs hs2 ↦ ?_⟩
  set t := s.im with ht
  set L := Real.log (|t| + 2)
  have hL : 0 ≤ L := Real.log_nonneg (by linarith [abs_nonneg t])
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_half_lt (by linarith)
  have hw := hCw s (by linarith) hs2 hs1 hζ
  set m : ℂ → ℕ := fun z ↦ (analyticOrderAt riemannZeta z).toNat
  set Z := TauCeti.riemannZetaZerosClosedBall (2 + t * I) 4
  rw [← ht, TauCeti.finsum_window_eq_sum_riemannZetaZerosClosedBall t
    fun z ↦ (m z : ℂ) / (s - z)] at hw
  set W := ∑ z ∈ Z with 0 < z.re ∧ z.re < 1 ∧ |z.im - t| ≤ 1 ∧ riemannZeta z = 0,
    (m z : ℂ) / (s - z)
  -- the zero count in the disc
  have hcount : ∑ z ∈ Z, (m z : ℝ) ≤ Cc * L := by
    have h := hCc (2 + t * I) (by simp)
    rwa [finsum_subtype_riemannZeta_eq_sum' (2 + t * I) 4 fun z ↦ (m z : ℝ),
      show (2 + t * I).im = t by simp] at h
  -- every window zero is at distance at least `a` from `s`
  have hW : ‖W‖ ≤ Cc * L / a := by
    calc ‖W‖ ≤ ∑ z ∈ Z with 0 < z.re ∧ z.re < 1 ∧ |z.im - t| ≤ 1 ∧ riemannZeta z = 0,
          (m z : ℝ) / a := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun z hz ↦ ?_)
          obtain ⟨-, h0, h1, -, hzζ⟩ := Finset.mem_filter.mp hz
          rw [norm_div, Complex.norm_natCast]
          refine div_le_div_of_nonneg_left (by positivity) ha ?_
          have hre : a ≤ (s - z).re := by rw [sub_re, re_eq_half_of_zero h0 h1 hzζ]; linarith
          exact hre.trans (re_le_norm _)
      _ ≤ ∑ z ∈ Z, (m z : ℝ) / a :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun _ _ _ ↦ by positivity
      _ = (∑ z ∈ Z, (m z : ℝ)) / a := by rw [Finset.sum_div]
      _ ≤ Cc * L / a := by gcongr
  set H := deriv riemannZeta s / riemannZeta s + 1 / (s - 1)
  have htri : ‖H‖ ≤ ‖H - W‖ + ‖W‖ := by
    have := norm_add_le (H - W) W
    rwa [sub_add_cancel] at this
  have h1 : Cw * L ≤ |Cw| * L / a :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) hL).trans (le_div_self (by positivity) ha ha1)
  have h2 : Cc * L / a ≤ |Cc| * L / a := by gcongr; exact le_abs_self _
  calc ‖H‖ ≤ Cw * L + Cc * L / a := by linarith
    _ ≤ |Cw| * L / a + |Cc| * L / a := add_le_add h1 h2
    _ = (|Cw| + |Cc|) / a * L := by ring

/-! ## The explicit-formula contour at `η = 1/2 - a`, `T = x`, `ε = x^(-1/2)` -/

/-- Copy of a private lemma of Tau Ceti's `ZeroFreeRegion.lean` (Apache 2.0): the Mellin bound at
`ε = 1`, `s = 1` forces `C ≥ 0`. -/
theorem nonneg_of_norm_mellin_smoothCutoff_le' {ν : ℝ → ℝ} {C : ℝ}
    (hC : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 2 →
      ‖mellin (fun x ↦ (TauCeti.smoothCutoff ν ε x : ℂ)) s‖ ≤ C / (‖s‖ * (1 + ε * ‖s‖))) :
    0 ≤ C := by
  have h := hC 1 one_pos le_rfl 1 (by norm_num) (by norm_num)
  rw [norm_one, one_mul, mul_one] at h
  exact (div_nonneg_iff.1 ((norm_nonneg _).trans h)).elim (·.1) fun h' ↦ absurd h'.2 (by norm_num)

open scoped Real in
/-- The arithmetic of the contour terms at `η = 1/2 - a`, `T = x = s²`, `ε = 1/s`:
`A = log(x + 2) ≤ 2L`, `P = log(1 + x/(1/2 + a)) ≤ 2L`, `L = log x ≥ 1`, `s ≤ y = x^(1/2 + a)`. -/
private lemma sharp_terms_le {C M₀ a x s y L A P : ℝ} (hC : 0 ≤ C) (hM₀ : 0 ≤ M₀) (ha : 0 < a)
    (ha4 : a ≤ 1 / 4) (hs : 1 ≤ s) (hx : x = s ^ 2) (hL : 1 ≤ L) (hA : 0 ≤ A) (hA2 : A ≤ 2 * L)
    (hP : 0 ≤ P) (hP2 : P ≤ 2 * L) (hy : s ≤ y) :
    1 / (2 * π) * (2 * (8 * 1 * L ^ 2 * C * (Real.exp 1 * x)) / (s⁻¹ * x) +
        4 * ((M₀ * A / a + 1 / (1 / 2 - a)) * C * y) * P +
        2 * ((L⁻¹ + (1 / 2 - a)) * ((M₀ * A / a + 1 / (1 / 2 - a)) * C) * (Real.exp 1 * x) /
          (s⁻¹ * x ^ 2))) +
      3 * (2 * s⁻¹ * x + 1) * L + 2 * Real.log 2 * s⁻¹ * x ≤
    (16 * Real.exp 1 * C + (8 + 3 * Real.exp 1) * (2 * M₀ + 4) * C + 11) * y * L ^ 2 / a := by
  subst hx
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  generalize Real.exp 1 = e at *
  have hs0 : 0 < s := by linarith
  have hy1 : 1 ≤ y := hs.trans hy
  have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL
  have hη : 0 < 1 / 2 - a := by linarith
  have hyQ : y ≤ y * L ^ 2 / a := by
    rw [le_div_iff₀ ha]; nlinarith
  have hsQ : s ≤ y * L ^ 2 / a := hy.trans hyQ
  have hLQ : L / a ≤ y * L ^ 2 / a := by
    apply div_le_div_of_nonneg_right _ ha.le; nlinarith
  have hsLQ : s * L ≤ y * L ^ 2 / a := by
    rw [le_div_iff₀ ha]
    have h1 : s * a ≤ y := by nlinarith
    have h2 : s * a * L ≤ y * L := mul_le_mul_of_nonneg_right h1 (by linarith)
    have h3 : y * L ≤ y * L ^ 2 :=
      mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
    linarith
  have hQ0 : 0 ≤ y * L ^ 2 / a := by positivity
  have hK : M₀ * A / a + 1 / (1 / 2 - a) ≤ (2 * M₀ + 4) * L / a := by
    have h1 : M₀ * A / a ≤ 2 * M₀ * L / a :=
      div_le_div_of_nonneg_right (by nlinarith) ha.le
    have h2 : 1 / (1 / 2 - a) ≤ 4 * L / a := by
      rw [div_le_div_iff₀ hη ha]
      nlinarith [mul_nonneg (sub_nonneg.2 hL) hη.le]
    calc _ ≤ 2 * M₀ * L / a + 4 * L / a := add_le_add h1 h2
      _ = _ := by ring
  have hK0 : 0 ≤ M₀ * A / a + 1 / (1 / 2 - a) :=
    add_nonneg (by positivity) (one_div_pos.2 hη).le
  generalize M₀ * A / a + 1 / (1 / 2 - a) = K at *
  have hK' : 0 ≤ (2 * M₀ + 4) * L / a := by positivity
  -- the five terms
  have t1 : 2 * (8 * 1 * L ^ 2 * C * (e * s ^ 2)) / (s⁻¹ * s ^ 2) ≤ 16 * e * C * (y * L ^ 2 / a) := by
    rw [show 2 * (8 * 1 * L ^ 2 * C * (e * s ^ 2)) / (s⁻¹ * s ^ 2) = 16 * e * C * (s * L ^ 2) by
      field_simp; ring]
    gcongr
    rw [le_div_iff₀ ha]
    nlinarith [mul_le_mul_of_nonneg_right hy (sq_nonneg L),
      mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ y) (sq_nonneg L)) (by linarith : (0:ℝ) ≤ 1 - a)]
  have t2 : 4 * (K * C * y) * P ≤ 8 * (2 * M₀ + 4) * C * (y * L ^ 2 / a) := by
    calc 4 * (K * C * y) * P ≤ 4 * ((2 * M₀ + 4) * L / a * C * y) * (2 * L) := by gcongr
      _ = _ := by ring
  have t3 : 2 * ((L⁻¹ + (1 / 2 - a)) * (K * C) * (e * s ^ 2) / (s⁻¹ * (s ^ 2) ^ 2)) ≤
      3 * e * (2 * M₀ + 4) * C * (y * L ^ 2 / a) := by
    have hLi : L⁻¹ + (1 / 2 - a) ≤ 3 / 2 := by
      have := inv_le_one_of_one_le₀ hL; linarith
    have hsi : s⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hs
    have hLi0 : 0 ≤ L⁻¹ + (1 / 2 - a) := by positivity
    calc 2 * ((L⁻¹ + (1 / 2 - a)) * (K * C) * (e * s ^ 2) / (s⁻¹ * (s ^ 2) ^ 2))
        = 2 * (L⁻¹ + (1 / 2 - a)) * K * C * e * s⁻¹ := by field_simp
      _ ≤ 2 * (3 / 2) * ((2 * M₀ + 4) * L / a) * C * e * 1 := by gcongr
      _ = 3 * e * (2 * M₀ + 4) * C * (L / a) := by ring
      _ ≤ _ := by gcongr
  have t4 : 3 * (2 * s⁻¹ * s ^ 2 + 1) * L ≤ 9 * (y * L ^ 2 / a) := by
    rw [show 2 * s⁻¹ * s ^ 2 = 2 * s by field_simp]
    nlinarith
  have t5 : 2 * Real.log 2 * s⁻¹ * s ^ 2 ≤ 2 * (y * L ^ 2 / a) := by
    rw [show 2 * Real.log 2 * s⁻¹ * s ^ 2 = 2 * Real.log 2 * s by field_simp]
    have := Real.log_two_lt_d9
    nlinarith [Real.log_pos one_lt_two]
  have hπ : 1 / (2 * π) ≤ 1 := by rw [div_le_one (by positivity)]; linarith [Real.two_le_pi]
  have hπ0 : 0 ≤ 1 / (2 * π) := by positivity
  have hsum0 : 0 ≤ 2 * (8 * 1 * L ^ 2 * C * (e * s ^ 2)) / (s⁻¹ * s ^ 2) +
      4 * (K * C * y) * P +
      2 * ((L⁻¹ + (1 / 2 - a)) * (K * C) * (e * s ^ 2) / (s⁻¹ * (s ^ 2) ^ 2)) := by
    have : 0 ≤ L⁻¹ + (1 / 2 - a) := by positivity
    positivity
  have hmul := mul_le_of_le_one_left hsum0 hπ
  have hD : (16 * e * C + (8 + 3 * e) * (2 * M₀ + 4) * C + 11) * y * L ^ 2 / a =
      16 * e * C * (y * L ^ 2 / a) + 8 * (2 * M₀ + 4) * C * (y * L ^ 2 / a) +
        3 * e * (2 * M₀ + 4) * C * (y * L ^ 2 / a) + 9 * (y * L ^ 2 / a) + 2 * (y * L ^ 2 / a) := by
    ring
  rw [hD]
  linarith

open scoped Chebyshev in
/-- **The explicit formula under the proved RH, with the gap `a` free.** There is one absolute
constant `D` such that for every `0 < a ≤ 1/4` and every `x ≥ 3`,
`|ψ(x) - x| ≤ D x^(1/2 + a) log² x / a`.

Tau Ceti's smoothed Perron contour (`norm_tsum_mul_smoothCutoff_sub_residue_le_of_norm_le_mul_log`)
for `a(n) = Λ(n)`, `G = -ζ′/ζ - 1/(s - 1)`, on the rectangle `[1/2 + a, 1 + 1/log x] × [-x, x]`,
with the cutoff scale `ε = x^(-1/2)`: the vertical tails give `√x log² x`, the left edge
`x^(1/2 + a) log² x / a` (through `logDeriv_bound_of_RH_gap`), the horizontal edges
`log x / (a √x)`; the sharp/smooth comparison and the main-term correction give `√x log x`. -/
theorem psi_sub_le_of_gap : ∃ D : ℝ, 0 ≤ D ∧ ∀ a : ℝ, 0 < a → a ≤ 1 / 4 → ∀ x : ℝ, 3 ≤ x →
    |ψ x - x| ≤ D * x ^ (1 / 2 + a) * Real.log x ^ 2 / a := by
  obtain ⟨Cg, hCg0, hCg⟩ := logDeriv_bound_of_RH_gap
  -- the bump and the uniform Mellin bound on the strip `1/2 ≤ Re s ≤ 2`
  obtain ⟨ν, hνd, hν0, hνs, hνm, -⟩ := TauCeti.exists_smooth_symmetric_bump one_lt_two
  have hνs' : Function.support ν ∩ Set.Ioi 0 ⊆ Set.Icc (1 / 2) 2 := fun y hy ↦ by
    simpa only [one_div] using hνs hy.1
  have hν0' : ∀ y > 0, 0 ≤ ν y := fun y _ ↦ hν0 y
  have hν1 : ContDiffOn ℝ 1 ν (Set.Ioi 0) := (hνd.of_le (by exact_mod_cast le_top)).contDiffOn
  obtain ⟨C, hC⟩ := TauCeti.exists_norm_mellin_smoothCutoff_le (k := 1) hν1 hνs'
    (σ₁ := 1 / 2) (σ₂ := 2) (by norm_num)
  simp only [pow_one] at hC
  have hC0 : 0 ≤ C := nonneg_of_norm_mellin_smoothCutoff_le' hC
  -- the regular part `G = -ζ′/ζ - 1/(s - 1)` of the L-series of `Λ`
  set U : Set ℂ := {s | 1 / 2 < s.re}
  have hζU {s : ℂ} (hs : s ∈ U) : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_half_lt (by simpa [U] using hs)
  set G : ℂ → ℂ := fun s ↦ -logDeriv (DirichletCharacter.LFunctionTrivChar₁ 1) s
  have hGU : DifferentiableOn ℂ G U := fun s hs ↦ by
    have hd := DirichletCharacter.differentiable_LFunctionTrivChar₁ 1
    exact ((((hd.analyticAt s).deriv).differentiableAt.div (hd s)
      (DirichletCharacter.LFunctionTrivChar₁_one_ne_zero (hζU hs))).neg).differentiableWithinAt
  have hGeq {s : ℂ} (hs1 : s ≠ 1) (hs : s ∈ U) :
      G s = -(deriv riemannZeta s / riemannZeta s + 1 / (s - 1)) := by
    simp only [G]
    rw [one_div, ← logDeriv_apply, TauCeti.logDeriv_riemannZeta_add_inv_sub_one hs1 (hζU hs)]
  have ha (n : ℕ) (hn : 1 ≤ n) : ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ ≤
      1 * Real.log (n + 1) := by
    rw [Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, one_mul]
    exact ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_log (by exact_mod_cast hn) (by linarith))
  have hLG (s : ℂ) (hs : 1 < s.re) :
      LSeries (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) s = G s + 1 / (s - 1) := by
    have hs1 : s ≠ 1 := fun h ↦ by simp [h] at hs
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs,
      hGeq hs1 (show (1 : ℝ) / 2 < s.re by linarith)]
    ring
  have hM₀ : 0 ≤ Cg + ‖G 1‖ := by positivity
  refine ⟨16 * Real.exp 1 * C + (8 + 3 * Real.exp 1) * (2 * (Cg + ‖G 1‖) + 4) * C + 11,
    by positivity, fun a ha0 ha4 x hx ↦ ?_⟩
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
  have hη : 0 < 1 / 2 - a := by linarith
  have hη1 : 1 / 2 - a < 1 := by linarith
  have hηT : 1 / 2 - a ≤ x := by linarith
  have h1η : 1 - (1 / 2 - a) = 1 / 2 + a := by ring
  -- the rectangle lies in `U`
  have hrect : Set.Icc (1 - (1 / 2 - a)) (1 + (Real.log x)⁻¹) ×ℂ Set.Icc (-x) x ⊆ U :=
    fun z hz ↦ by
      have := (mem_reProdIm.1 hz).1.1
      simp only [U, Set.mem_ofPred_eq]; linarith
  -- `G` is bounded by `M = (Cg + ‖G 1‖) log(x + 2) / a` on the rectangle
  have hlogx2 : 1 ≤ Real.log (x + 2) :=
    (Real.le_log_iff_exp_le (by linarith)).2 (by linarith [Real.exp_one_lt_d9])
  have hGb : ∀ z ∈ Set.Icc (1 - (1 / 2 - a)) (1 + (Real.log x)⁻¹) ×ℂ Set.Icc (-x) x,
      ‖G z‖ ≤ (Cg + ‖G 1‖) * Real.log (x + 2) / a := fun z hz ↦ by
    obtain ⟨⟨hre1, hre2⟩, him⟩ := mem_reProdIm.1 hz
    rcases eq_or_ne z 1 with rfl | hz1
    · calc ‖G 1‖ ≤ Cg + ‖G 1‖ := by linarith
        _ ≤ (Cg + ‖G 1‖) * Real.log (x + 2) := le_mul_of_one_le_right hM₀ hlogx2
        _ ≤ (Cg + ‖G 1‖) * Real.log (x + 2) / a :=
          le_div_self (by positivity) ha0 (by linarith)
    · rw [hGeq hz1 (hrect hz), norm_neg]
      refine (hCg a ha0 (by linarith) z hz1 (by linarith) (by linarith)).trans ?_
      have hzim : |z.im| ≤ x := abs_le.2 ⟨him.1, him.2⟩
      have hlog : Real.log (|z.im| + 2) ≤ Real.log (x + 2) :=
        Real.log_le_log (by positivity) (by linarith)
      calc Cg / a * Real.log (|z.im| + 2) ≤ Cg / a * Real.log (x + 2) := by gcongr
        _ = Cg * Real.log (x + 2) / a := by ring
        _ ≤ (Cg + ‖G 1‖) * Real.log (x + 2) / a := by gcongr; linarith [norm_nonneg (G 1)]
  -- the contour estimate, the sharp/smooth comparison, the main-term correction
  have hcont := TauCeti.LSeries.norm_tsum_mul_smoothCutoff_sub_residue_le_of_norm_le_mul_log
    (a := fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) ha hν1 hνs' hε (by linarith) hη hη1
    hηT (G := G) (r := 1) (hGU.continuousOn.mono hrect)
    (hGU.mono fun z hz ↦ hrect ⟨Set.Ioo_subset_Icc_self hz.1, Set.Ioo_subset_Icc_self hz.2⟩) hGb
    (fun z hz ↦ hLG z (by rw [hz]; linarith))
    (fun z hz1 hz2 ↦ hC (√x)⁻¹ hε hε1 z (by linarith) (by linarith))
  have hsm := TauCeti.norm_psi_sub_tsum_vonMangoldt_mul_smoothCutoff_le hν0' hνs' hνm hε hε1
    (X := x) (by linarith)
  have hmain := TauCeti.norm_mellin_smoothCutoff_one_sub_one_le hν0' hνs' hνm hε hε1
  rw [norm_one, h1η] at hcont
  set m := mellin (fun y ↦ (TauCeti.smoothCutoff ν (√x)⁻¹ y : ℂ)) 1
  set S := ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * TauCeti.smoothCutoff ν (√x)⁻¹ (n / x)
  have hdec : (ψ x : ℂ) - x = ((ψ x : ℂ) - S) + (S - 1 * m * x) + 1 * (m - 1) * x := by ring
  have hmt : ‖(1 : ℂ) * (m - 1) * x‖ ≤ 2 * Real.log 2 * (√x)⁻¹ * x := by
    rw [one_mul, norm_mul, Complex.norm_of_nonneg hx0.le]
    gcongr
  have hcast : |ψ x - x| = ‖(ψ x : ℂ) - (x : ℂ)‖ := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  -- the logarithms on the left edge
  have hlogsq : Real.log (x ^ 2) = 2 * Real.log x := by rw [Real.log_pow]; norm_num
  have hlogA : Real.log (x + 2) ≤ 2 * Real.log x := by
    rw [← hlogsq]; exact Real.log_le_log (by positivity) (by nlinarith)
  have hlogP : Real.log (1 + x / (1 / 2 + a)) ≤ 2 * Real.log x := by
    rw [← hlogsq]
    refine Real.log_le_log (by positivity) ?_
    have : x / (1 / 2 + a) ≤ 2 * x := by rw [div_le_iff₀ (by linarith)]; nlinarith
    nlinarith
  have hlogP0 : 0 ≤ Real.log (1 + x / (1 / 2 + a)) := Real.log_nonneg (by
    have : 0 ≤ x / (1 / 2 + a) := by positivity
    linarith)
  have hy : √x ≤ x ^ (1 / 2 + a) := by
    rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have harith := sharp_terms_le hC0 hM₀ ha0 ha4 hs1 hxs hL1 (Real.log_nonneg (by linarith))
    hlogA hlogP0 hlogP hy
  rw [hcast, hdec]
  calc ‖((ψ x : ℂ) - S) + (S - 1 * m * x) + 1 * (m - 1) * x‖
      ≤ ‖(ψ x : ℂ) - S‖ + ‖S - 1 * m * x‖ + ‖(1 : ℂ) * (m - 1) * x‖ := norm_add₃_le
    _ ≤ _ := by linarith

/-! ## Step 1: the exponent `1/2 + δ` for every `δ > 0` -/

open scoped Chebyshev in
/-- `|ψ(x) - x| ≤ C x^(1/2 + δ)` for all `x ≥ 3`: the gap `a = min(δ/2, 1/4)` in
`psi_sub_le_of_gap`, and `log² x ≤ 16 x^(δ/2) / δ²`. -/
theorem psi_sub_le_rpow_half_add (δ : ℝ) (hδ : 0 < δ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ x : ℝ, 3 ≤ x → |ψ x - x| ≤ C * x ^ (1 / 2 + δ) := by
  obtain ⟨D, hD0, hD⟩ := psi_sub_le_of_gap
  have ha0 : 0 < min (δ / 2) (1 / 4) := lt_min (by positivity) (by norm_num)
  have ha4 : min (δ / 2) (1 / 4) ≤ 1 / 4 := min_le_right _ _
  have haδ : min (δ / 2) (1 / 4) ≤ δ / 2 := min_le_left _ _
  refine ⟨D / ((δ / 4) ^ 2 * min (δ / 2) (1 / 4)), by positivity, fun x hx ↦ ?_⟩
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

open scoped Chebyshev in
/-- **`ψ(x) = x + O(x^(1/2 + δ))` for every `δ > 0`, from the proved RH.** -/
theorem psi_sub_le_of_RH (δ : ℝ) (hδ : 0 < δ) :
    ∃ C x₀ : ℝ, ∀ x ≥ x₀, |ψ x - x| ≤ C * x ^ (1 / 2 + δ) := by
  obtain ⟨C, -, hC⟩ := psi_sub_le_rpow_half_add δ hδ
  exact ⟨C, 3, fun x hx ↦ hC x hx⟩

open scoped Chebyshev in
/-- `|θ(x) - x| ≤ |ψ(x) - x| + 6 √x log x` for `x ≥ 3` (Tau Ceti's `ψ - θ` bound). -/
theorem theta_sub_le_psi_sub_add (x : ℝ) (hx : 3 ≤ x) :
    |θ x - x| ≤ |ψ x - x| + 6 * (√x * Real.log x) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hl4b : Real.log 4 ≤ 2 := by rw [hl4]; linarith [Real.log_two_lt_d9]
  have hl40 : 0 ≤ Real.log 4 := by rw [hl4]; positivity
  have hL : 1 ≤ Real.log x :=
    (Real.le_log_iff_exp_le hx0).2 (by linarith [Real.exp_one_lt_d9])
  have hs0 : 0 ≤ √x := Real.sqrt_nonneg x
  have h := Chebyshev.abs_theta_sub_le_abs_psi_sub_add (c := Real.log 4)
    (fun y hy ↦ Chebyshev.theta_le_log4_mul_x hy.le) hx0.le
  have hcube : x ^ ((1 : ℝ) / 3) ≤ √x := by
    rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hmax : max (Real.log x / Real.log 2 - 2) 0 ≤ Real.log x / Real.log 2 :=
    max_le (by linarith) (by positivity)
  have hprod : max (Real.log x / Real.log 2 - 2) 0 * x ^ ((1 : ℝ) / 3) ≤
      Real.log x / Real.log 2 * √x :=
    mul_le_mul hmax hcube (by positivity) (by positivity)
  have h1 : Real.log 4 * √x ≤ 2 * (√x * Real.log x) := by
    calc Real.log 4 * √x ≤ 2 * √x := mul_le_mul_of_nonneg_right hl4b hs0
      _ ≤ 2 * (√x * Real.log x) := by nlinarith
  have h2 : Real.log 4 * (Real.log x / Real.log 2 * √x) = 2 * (√x * Real.log x) := by
    rw [hl4]; field_simp
  have h3 := mul_le_mul_of_nonneg_left hprod hl40
  have h0 : 0 ≤ √x * Real.log x := by positivity
  nlinarith

open scoped Chebyshev in
/-- `|θ(x) - x| ≤ K x^(1/2 + δ)` for all `x ≥ 3`. -/
theorem theta_sub_le_rpow_half_add (δ : ℝ) (hδ : 0 < δ) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ x : ℝ, 3 ≤ x → |θ x - x| ≤ K * x ^ (1 / 2 + δ) := by
  obtain ⟨C, hC0, hC⟩ := psi_sub_le_rpow_half_add δ hδ
  refine ⟨C + 6 / δ, by positivity, fun x hx ↦ ?_⟩
  have hx0 : 0 < x := by linarith
  have hlog : Real.log x ≤ x ^ δ / δ := Real.log_le_rpow_div hx0.le hδ
  have hsl : √x * Real.log x ≤ x ^ (1 / 2 + δ) / δ := by
    calc √x * Real.log x ≤ √x * (x ^ δ / δ) :=
          mul_le_mul_of_nonneg_left hlog (Real.sqrt_nonneg x)
      _ = x ^ (1 / 2 + δ) / δ := by rw [Real.sqrt_eq_rpow, Real.rpow_add hx0]; ring
  calc |θ x - x| ≤ |ψ x - x| + 6 * (√x * Real.log x) := theta_sub_le_psi_sub_add x hx
    _ ≤ C * x ^ (1 / 2 + δ) + 6 * (x ^ (1 / 2 + δ) / δ) := by gcongr; exact hC x hx
    _ = (C + 6 / δ) * x ^ (1 / 2 + δ) := by ring

open scoped Chebyshev in
/-- **`θ(x) = x + O(x^(1/2 + δ))` for every `δ > 0`, from the proved RH.** -/
theorem theta_sub_le_of_RH (δ : ℝ) (hδ : 0 < δ) :
    ∃ C x₀ : ℝ, ∀ x ≥ x₀, |θ x - x| ≤ C * x ^ (1 / 2 + δ) := by
  obtain ⟨K, -, hK⟩ := theta_sub_le_rpow_half_add δ hδ
  exact ⟨K, 3, fun x hx ↦ hK x hx⟩

open scoped Chebyshev in
/-- **The transfer of a power-saving `θ`-bound to `π - Li`** (the argument of
`WallsMeetRH.primeCounting_sub_logIntegral_le_rpow_of_RH`, with the exponent free): if
`|θ(x) - x| ≤ K x^(1 - d)` for `x ≥ 3` with `0 < d ≤ 1/2`, then
`|π(⌊x⌋) - Li(x)| ≤ C x^(1 - d)` for `x ≥ 3`. -/
theorem primeCounting_sub_logIntegral_le_of_theta {d K : ℝ} (hd : 0 < d) (hd2 : d ≤ 1 / 2)
    (hK0 : 0 ≤ K) (hK : ∀ x : ℝ, 3 ≤ x → |θ x - x| ≤ K * x ^ (1 - d)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 3 ≤ x →
      |(Nat.primeCounting ⌊x⌋₊ : ℝ) - TauCeti.Real.logIntegral x| ≤ C * x ^ (1 - d) := by
  set D1 := |(Nat.primeCounting ⌊(3 : ℝ)⌋₊ : ℝ) - TauCeti.Real.logIntegral 3|
  set ε : ℝ → ℝ := fun t ↦ K * t ^ (-d)
  set D3 := 3 * ε 3 / Real.log 3
  have hl3 : 1 ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]; linarith [Real.exp_one_lt_d9]
  have hD3 : 0 ≤ D3 := by simp only [D3, ε]; positivity
  have hD1 : 0 ≤ D1 := abs_nonneg _
  refine ⟨D1 + K + D3 + 2 * K, by positivity, fun x hx ↦ ?_⟩
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
  change _ ≤ D1 + _ + D3 + _ at hmain
  nlinarith [mul_le_mul_of_nonneg_left hX1 hD1, mul_le_mul_of_nonneg_left hX1 hD3]

/-- `|π(⌊x⌋) - Li(x)| ≤ C x^(1/2 + δ)` for all `x ≥ 3`. -/
theorem primeCounting_sub_logIntegral_le_rpow_half_add (δ : ℝ) (hδ : 0 < δ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ x : ℝ, 3 ≤ x →
      |(Nat.primeCounting ⌊x⌋₊ : ℝ) - TauCeti.Real.logIntegral x| ≤ C * x ^ (1 / 2 + δ) := by
  -- work at `δ' = min δ (1/4)`, so that `d = 1/2 - δ' ∈ (0, 1/2]`
  have hδ'0 : 0 < min δ (1 / 4) := lt_min hδ (by norm_num)
  have hδ'4 : min δ (1 / 4) ≤ 1 / 4 := min_le_right _ _
  have hδ'δ : min δ (1 / 4) ≤ δ := min_le_left _ _
  obtain ⟨K, hK0, hK⟩ := theta_sub_le_rpow_half_add _ hδ'0
  have hexp : (1 : ℝ) - (1 / 2 - min δ (1 / 4)) = 1 / 2 + min δ (1 / 4) := by ring
  obtain ⟨C, hC0, hC⟩ := primeCounting_sub_logIntegral_le_of_theta (d := 1 / 2 - min δ (1 / 4))
    (by linarith) (by linarith) hK0 (fun x hx ↦ by rw [hexp]; exact hK x hx)
  refine ⟨C, hC0, fun x hx ↦ (hC x hx).trans ?_⟩
  rw [hexp]
  gcongr; linarith

/-- **`π(⌊x⌋) = Li(x) + O(x^(1/2 + δ))` for every `δ > 0`, from the proved RH.** -/
theorem primeCounting_sub_logIntegral_le_of_RH (δ : ℝ) (hδ : 0 < δ) : ∃ C x₀ : ℝ, ∀ x ≥ x₀,
    |(Nat.primeCounting ⌊x⌋₊ : ℝ) - TauCeti.Real.logIntegral x| ≤ C * x ^ (1 / 2 + δ) := by
  obtain ⟨C, -, hC⟩ := primeCounting_sub_logIntegral_le_rpow_half_add δ hδ
  exact ⟨C, 3, fun x hx ↦ hC x hx⟩

open Classical in
/-- **The walls meet RH at the exponent `1/2 + δ`.** For every `δ > 0` there are `C` and `N₀`
such that for every `N ≥ N₀` the wall count `2 + #{n ≤ N that pass the wall test}` differs from
`Li(N)` by at most `C N^(1/2 + δ)`. From `riemannHypothesis` (through
`primeCounting_sub_logIntegral_le_rpow_half_add`) and Rayn-McLean's `prime_count_walls`. -/
theorem walls_meet_rh_half (δ : ℝ) (hδ : 0 < δ) : ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    |((2 + ((Finset.range (N + 1)).filter passes).card : ℕ) : ℝ) -
      TauCeti.Real.logIntegral N| ≤ C * (N : ℝ) ^ (1 / 2 + δ) := by
  obtain ⟨C, -, hC⟩ := primeCounting_sub_logIntegral_le_rpow_half_add δ hδ
  refine ⟨C, 3, fun N hN ↦ ?_⟩
  have h := hC N (by exact_mod_cast hN)
  rwa [Nat.floor_natCast, prime_count_walls N hN] at h

/-! ## Step 2: the gap `a = 1 / log x`, error `√x log³ x` for `ψ`, `√x log² x` for `π` -/

/-- For `x ≥ 55`, `log x ≥ 4` (as `e⁴ < 55`). -/
theorem four_le_log_of_le (x : ℝ) (hx : 55 ≤ x) : 4 ≤ Real.log x := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have h := Real.exp_one_lt_d9
  have h0 := Real.exp_pos 1
  calc Real.exp 4 = Real.exp 1 ^ 4 := by rw [Real.exp_one_pow]; norm_num
    _ ≤ 2.7182818286 ^ 4 := by gcongr
    _ ≤ 55 := by norm_num
    _ ≤ x := hx

open scoped Chebyshev in
/-- `|ψ(x) - x| ≤ D e √x log³ x` for `x ≥ 55`: the gap `a = 1 / log x` in `psi_sub_le_of_gap`,
where `x^(1/2 + 1/log x) = e √x`. -/
theorem psi_sub_le_sqrt_log_cube : ∃ C : ℝ, 0 ≤ C ∧
    ∀ x : ℝ, 55 ≤ x → |ψ x - x| ≤ C * √x * Real.log x ^ 3 := by
  obtain ⟨D, hD0, hD⟩ := psi_sub_le_of_gap
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

open scoped Chebyshev in
/-- **`ψ(x) = x + O(√x log³ x)`, from the proved RH.** -/
theorem psi_sub_le_sqrt_log_cube_of_RH :
    ∃ C x₀ : ℝ, ∀ x ≥ x₀, |ψ x - x| ≤ C * √x * Real.log x ^ 3 := by
  obtain ⟨C, -, hC⟩ := psi_sub_le_sqrt_log_cube
  exact ⟨C, 55, fun x hx ↦ hC x hx⟩

open scoped Chebyshev in
/-- `|θ(x) - x| ≤ K √x log³ x` for `x ≥ 55`. -/
theorem theta_sub_le_sqrt_log_cube : ∃ K : ℝ, 0 ≤ K ∧
    ∀ x : ℝ, 55 ≤ x → |θ x - x| ≤ K * √x * Real.log x ^ 3 := by
  obtain ⟨C, hC0, hC⟩ := psi_sub_le_sqrt_log_cube
  refine ⟨C + 6, by positivity, fun x hx ↦ ?_⟩
  have hL4 := four_le_log_of_le x hx
  have hs0 : 0 ≤ √x := Real.sqrt_nonneg x
  have hL3 : Real.log x ≤ Real.log x ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
  calc |θ x - x| ≤ |ψ x - x| + 6 * (√x * Real.log x) := theta_sub_le_psi_sub_add x (by linarith)
    _ ≤ C * √x * Real.log x ^ 3 + 6 * (√x * Real.log x ^ 3) := by
        gcongr
        exact hC x hx
    _ = (C + 6) * √x * Real.log x ^ 3 := by ring

open scoped Chebyshev in
/-- **`θ(x) = x + O(√x log³ x)`, from the proved RH.** -/
theorem theta_sub_le_sqrt_log_cube_of_RH :
    ∃ C x₀ : ℝ, ∀ x ≥ x₀, |θ x - x| ≤ C * √x * Real.log x ^ 3 := by
  obtain ⟨K, -, hK⟩ := theta_sub_le_sqrt_log_cube
  exact ⟨K, 55, fun x hx ↦ hK x hx⟩

open scoped Chebyshev in
/-- `|π(⌊x⌋) - Li(x)| ≤ C √x log² x` for `x ≥ 55`: Tau Ceti's `θ → π` transfer with
`ε(t) = K t^(-1/2) log³ t`, whose integral `∫ ε / log²` is `K ∫ t^(-1/2) log t ≤ 2 K √x log x`. -/
theorem primeCounting_sub_logIntegral_le_sqrt_log_sq : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 55 ≤ x →
    |(Nat.primeCounting ⌊x⌋₊ : ℝ) - TauCeti.Real.logIntegral x| ≤ C * √x * Real.log x ^ 2 := by
  obtain ⟨K, hK0, hK⟩ := theta_sub_le_sqrt_log_cube
  set D1 := |(Nat.primeCounting ⌊(55 : ℝ)⌋₊ : ℝ) - TauCeti.Real.logIntegral 55|
  set ε : ℝ → ℝ := fun t ↦ K * t ^ (-(1 / 2) : ℝ) * Real.log t ^ 3
  set D3 := 55 * ε 55 / Real.log 55
  have hl55 : 4 ≤ Real.log 55 := four_le_log_of_le 55 le_rfl
  have hD3 : 0 ≤ D3 := by simp only [D3, ε]; positivity
  have hD1 : 0 ≤ D1 := abs_nonneg _
  refine ⟨D1 + D3 + K + 2 * K, by positivity, fun x hx ↦ ?_⟩
  have hx0 : 0 < x := by linarith
  have hL4 := four_le_log_of_le x hx
  have hs1 : 1 ≤ √x := Real.one_le_sqrt.2 (by linarith)
  have hsL : 1 ≤ √x * Real.log x ^ 2 := one_le_mul_of_one_le_of_one_le hs1 (by nlinarith)
  have hsL0 : 0 ≤ √x * Real.log x ^ 2 := by positivity
  have hεt (t : ℝ) (ht : 0 < t) : t * ε t = K * √t * Real.log t ^ 3 := by
    simp only [ε]
    have : t * t ^ (-(1 / 2) : ℝ) = √t := by
      rw [Real.sqrt_eq_rpow]
      calc t * t ^ (-(1 / 2) : ℝ) = t ^ (1 : ℝ) * t ^ (-(1 / 2) : ℝ) := by rw [Real.rpow_one]
        _ = t ^ ((1 : ℝ) + -(1 / 2)) := (Real.rpow_add ht _ _).symm
        _ = t ^ (1 / 2 : ℝ) := by norm_num
    rw [← this]; ring
  -- integrability of `ε` on `[55, x]`
  have hcontε : ContinuousOn ε (Set.uIcc 55 x) := by
    rw [Set.uIcc_of_le hx]
    refine (continuousOn_const.mul (ContinuousOn.rpow_const continuousOn_id
      fun t ht ↦ Or.inl (ne_of_gt (show (0 : ℝ) < t by linarith [ht.1])))).mul
      ((Real.continuousOn_log.mono fun t ht ↦ ?_).pow 3)
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [ht.1]
  have hint : IntervalIntegrable ε MeasureTheory.volume 55 x := hcontε.intervalIntegrable
  have hmain := Chebyshev.abs_primeCounting_sub_logIntegral_le (ε := ε) (x₀ := 55) (x := x)
    (by norm_num) hx hint (fun t ht ↦ by
      rw [hεt t (by linarith [ht.1])]; exact hK t ht.1)
  have h2 : x * ε x / Real.log x ≤ K * (√x * Real.log x ^ 2) := by
    rw [hεt x hx0, div_le_iff₀ (by linarith)]; ring_nf; rfl
  -- the integral: `ε(t) / log² t = K t^(-1/2) log t ≤ K log x · t^(-1/2)`
  have hcont : ContinuousOn (fun t ↦ ε t / Real.log t ^ 2) (Set.uIcc 55 x) := by
    rw [Set.uIcc_of_le hx] at hcontε ⊢
    refine hcontε.div ((Real.continuousOn_log.mono fun t ht ↦ ?_).pow 2) fun t ht ↦ ?_
    · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [ht.1]
    · have : 4 ≤ Real.log t := four_le_log_of_le t ht.1
      positivity
  have hint2 : IntervalIntegrable (fun t : ℝ ↦ K * Real.log x * t ^ (-(1 / 2) : ℝ))
      MeasureTheory.volume 55 x :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul _
  have h4 : ∫ t in (55 : ℝ)..x, ε t / Real.log t ^ 2 ≤ 2 * K * (√x * Real.log x ^ 2) := by
    calc ∫ t in (55 : ℝ)..x, ε t / Real.log t ^ 2
        ≤ ∫ t in (55 : ℝ)..x, K * Real.log x * t ^ (-(1 / 2) : ℝ) :=
          intervalIntegral.integral_mono_on hx hcont.intervalIntegrable hint2 fun t ht ↦ by
            have hlt : 4 ≤ Real.log t := four_le_log_of_le t ht.1
            have hlx : Real.log t ≤ Real.log x := Real.log_le_log (by linarith [ht.1]) ht.2
            have ht0 : 0 ≤ t ^ (-(1 / 2) : ℝ) := by have := ht.1; positivity
            simp only [ε]
            rw [div_le_iff₀ (by positivity)]
            calc K * t ^ (-(1 / 2) : ℝ) * Real.log t ^ 3
                = K * t ^ (-(1 / 2) : ℝ) * Real.log t * Real.log t ^ 2 := by ring
              _ ≤ K * t ^ (-(1 / 2) : ℝ) * Real.log x * Real.log t ^ 2 := by gcongr
              _ = K * Real.log x * t ^ (-(1 / 2) : ℝ) * Real.log t ^ 2 := by ring
      _ = K * Real.log x * ((x ^ (-(1 / 2) + 1 : ℝ) - 55 ^ (-(1 / 2) + 1 : ℝ)) / (-(1 / 2) + 1)) := by
          rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num))]
      _ ≤ K * Real.log x * (2 * √x) := by
          gcongr
          have h55 : (0 : ℝ) ≤ 55 ^ (-(1 / 2) + 1 : ℝ) := by positivity
          have hxh : x ^ (-(1 / 2) + 1 : ℝ) = √x := by
            rw [Real.sqrt_eq_rpow]; norm_num
          rw [hxh, div_le_iff₀ (by norm_num)]
          linarith
      _ ≤ 2 * K * (√x * Real.log x ^ 2) := by
          have : Real.log x ≤ Real.log x ^ 2 := by nlinarith
          have hsx : 0 ≤ √x := Real.sqrt_nonneg x
          nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hK0 hsx)]
  change _ ≤ D1 + _ + D3 + _ at hmain
  nlinarith [mul_le_mul_of_nonneg_left hsL hD1, mul_le_mul_of_nonneg_left hsL hD3]

/-- **`π(⌊x⌋) = Li(x) + O(√x log² x)`, from the proved RH.** -/
theorem primeCounting_sub_logIntegral_le_sqrt_log_sq_of_RH : ∃ C x₀ : ℝ, ∀ x ≥ x₀,
    |(Nat.primeCounting ⌊x⌋₊ : ℝ) - TauCeti.Real.logIntegral x| ≤ C * √x * Real.log x ^ 2 := by
  obtain ⟨C, -, hC⟩ := primeCounting_sub_logIntegral_le_sqrt_log_sq
  exact ⟨C, 55, fun x hx ↦ hC x hx⟩

open Classical in
/-- **The walls meet RH at `√N log² N`.** There are `C` and `N₀` such that for every `N ≥ N₀`
the wall count `2 + #{n ≤ N that pass the wall test}` differs from `Li(N)` by at most
`C √N log² N`. From `riemannHypothesis` (through `primeCounting_sub_logIntegral_le_sqrt_log_sq`)
and Rayn-McLean's `prime_count_walls`. -/
theorem walls_meet_rh_sqrt : ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    |((2 + ((Finset.range (N + 1)).filter passes).card : ℕ) : ℝ) -
      TauCeti.Real.logIntegral N| ≤ C * √(N : ℝ) * Real.log (N : ℝ) ^ 2 := by
  obtain ⟨C, -, hC⟩ := primeCounting_sub_logIntegral_le_sqrt_log_sq
  refine ⟨C, 55, fun N hN ↦ ?_⟩
  have h := hC N (by exact_mod_cast hN)
  rwa [Nat.floor_natCast, prime_count_walls N (by omega)] at h

end WallsMeetRHSharp

#print axioms riemannHypothesis
#print axioms WallsMeetRHSharp.prime_count_walls
#print axioms WallsMeetRHSharp.logDeriv_bound_of_RH_gap
#print axioms WallsMeetRHSharp.psi_sub_le_of_gap
#print axioms WallsMeetRHSharp.psi_sub_le_of_RH
#print axioms WallsMeetRHSharp.theta_sub_le_of_RH
#print axioms WallsMeetRHSharp.primeCounting_sub_logIntegral_le_of_RH
#print axioms WallsMeetRHSharp.walls_meet_rh_half
#print axioms WallsMeetRHSharp.psi_sub_le_sqrt_log_cube_of_RH
#print axioms WallsMeetRHSharp.theta_sub_le_sqrt_log_cube_of_RH
#print axioms WallsMeetRHSharp.primeCounting_sub_logIntegral_le_sqrt_log_sq_of_RH
#print axioms WallsMeetRHSharp.walls_meet_rh_sqrt

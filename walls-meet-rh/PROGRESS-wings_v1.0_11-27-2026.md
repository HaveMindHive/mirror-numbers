# PROGRESS: WingFamiliesGRH (11-27-2026) - COMPLETE, all four targets

File: `WingFamiliesGRH_v1.0_11-27-2026.lean` (900 lines, namespace `WingFamiliesGRH`), no `sorry`.
Check: `./check-wings_v1.0_11-27-2026.sh` (step 1 compiles the Sharp file to `build/WallsMeetRHSharp.olean` with `lake env lean --root=build -o`, step 2 checks the wings file with that olean on `LEAN_PATH`; nothing is written in the RH repo). Output saved in `check-wings-output_v1.0_11-27-2026.txt`: zero errors, zero warnings, every `#print axioms` = `[propext, Classical.choice, Quot.sound]`.
Credit: GRH/RH by Alpoge with Claude (community condensed proof: `LFunction_ne_zero_of_half_lt_re`, `LFunction_eq_zero_re`, `riemannHypothesis` in `Main`); wall seating `p = 6k + f` by Rayn-McLean (Sharp file). Tau Ceti lemmas used under Apache-2.0 (The Tau Ceti contributors); one private lemma copied (`nonneg_of_norm_mellin_smoothCutoff_le`); the Abel-summation proof follows Mathlib's `Chebyshev.primeCounting_eq_theta_div_log_add_integral` (Apache-2.0).

## Compiled (all sorry-free)
### GRH as used (any nonprincipal chi mod N)
- `LFunction_ne_zero_of_half_lt (hχ : χ ≠ 1) : 1/2 < s.re → LFunction χ s ≠ 0`
- `re_eq_half_of_LFunction_eq_zero : 0 < ρ.re → ρ.re < 1 → LFunction χ ρ = 0 → ρ.re = 1/2`
### Log-derivative right of the critical line
- `logDeriv_LFunction_le_of_GRH_gap (hχ : χ ≠ 1) : ∃ C, 0 ≤ C ∧ ∀ a, 0 < a → a ≤ 1 → ∀ s, 1/2 + a ≤ s.re → s.re ≤ 2 → ‖logDeriv (LFunction χ) s‖ ≤ C / a * log(|s.im| + 2)`
  Landau's local lemma directly (discs 8/5 < 19/10 about 2 + i Im s, inside Re > 1/10 where ‖L‖ ≤ N‖s‖/Re s), zeros on Re = 1/2 by GRH, Jensen count. No window lemma and no Dirichlet growth bound at negative Re needed.
### Contour (target 1)
- `psi_chi_le_of_gap (hχ) : ∃ D, 0 ≤ D ∧ ∀ a, 0 < a → a ≤ 1/4 → ∀ x ≥ 3, ‖∑ n ∈ Ioc 0 ⌊x⌋₊, χ n * Λ n‖ ≤ D * x^(1/2 + a) * log x ^ 2 / a`
- `psi_chi_le_sqrt_log_cube (hχ) : ∃ C, 0 ≤ C ∧ ∀ x ≥ 55, ‖∑ ...‖ ≤ C * √x * log x ^ 3`
- `psi_chi_le_of_GRH (hχ) : ∃ C x₀, ∀ x ≥ x₀, ‖∑ n ∈ Ioc 0 ⌊x⌋₊, χ n * Λ n‖ ≤ C * √x * log x ^ 3`
- `psi_chi_le_rpow_of_GRH (hχ) (δ) (hδ) : ∃ C x₀, ∀ x ≥ x₀, ‖∑ ...‖ ≤ C * x^(1/2 + δ)`
- `psi_chi6_le_of_GRH` : the same at the wing character `chi6`.
### The wing character mod 6
- `chi6 : DirichletCharacter ℂ 6`, `chi6_apply (n) : chi6 n = if n % 6 = 1 then 1 else if n % 6 = 5 then -1 else 0`, `chi6_ne_one`, real weight `w6`, `chi6_eq_w6`.
- `psi6`, `theta6`, `primeSum6`; `psi6_le` (x ≥ 55), `abs_psi6_sub_theta6_le : |psi6 x - theta6 x| ≤ ψ x - θ x`, `theta6_le : ∃ K, 0 ≤ K ∧ ∀ t ≥ 2, |theta6 t| ≤ K √t log³ t`.
- `primeSum6_eq_theta6_div_log_add_integral (hx : 2 ≤ x) : primeSum6 x = theta6 x / log x + ∫ t in 2..x, theta6 t / (t log² t)` (Abel summation).
- `primeSum6_le : ∃ C, 0 ≤ C ∧ ∀ x ≥ 3, |primeSum6 x| ≤ C * √x * log x ^ 2`.
### Wing counts in wall words (targets 2, 3, 4)
- `wingCount (f : ℤ) (x : ℝ) : ℕ := #{p ∈ Icc 0 ⌊x⌋₊ | p.Prime ∧ ∃ k : ℤ, (p : ℤ) = 6 * k + f}`; `wingCount_one`, `wingCount_neg_one` (p % 6 = 1, resp. 5).
- `primeSum6_eq_wingCount_sub : primeSum6 x = wingCount 1 x - wingCount (-1) x`
- `wingCount_add_wingCount (hx : 3 ≤ x) : wingCount 1 x + wingCount (-1) x + 2 = π ⌊x⌋₊`
- `wing_lead_le : ∃ C x₀, ∀ x ≥ x₀, |(wingCount (-1) x : ℝ) - wingCount 1 x| ≤ C * √x * log x ^ 2` (x₀ = 3)
- `wing_count_sub_half_li (f) (hf : f = 1 ∨ f = -1) : ∃ C x₀, ∀ x ≥ x₀, |(wingCount f x : ℝ) - Li x / 2| ≤ C * √x * log x ^ 2` (x₀ = 55; uses Sharp's `primeCounting_sub_logIntegral_le_sqrt_log_sq`)
- `wing_families_meet_grh : ∃ C x₀, ∀ x ≥ x₀, |wingCount 1 x - Li x / 2| ≤ C √x log² x ∧ |wingCount (-1) x - Li x / 2| ≤ C √x log² x ∧ |wingCount (-1) x - wingCount 1 x| ≤ C √x log² x`

## Remaining
Nothing for the four targets. Not done (not required): the sign of the lead (Chebyshev's bias) is not addressed; the theorem bounds only its size.

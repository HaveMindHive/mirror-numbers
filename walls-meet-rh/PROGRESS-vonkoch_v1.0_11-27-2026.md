# PROGRESS: WallsMeetRHVonKoch (11-27-2026) - COMPLETE, Stage 1 and Stage 2

File: `WallsMeetRHVonKoch_v1.0_11-27-2026.lean` (1168 lines, namespace `WallsMeetRHVonKoch`), no `sorry`,
no `admit`, no `native_decide`.
Check: `./check-vonkoch_v1.0_11-27-2026.sh` (lake env lean inside the built RH repo; writes nothing there).
Output saved in `check-vonkoch-output_v1.0_11-27-2026.txt`: zero errors, zero warnings, every
`#print axioms` = `[propext, Classical.choice, Quot.sound]`.
Credit: RH by Alpoge with Claude (community condensed proof, `riemannHypothesis` in `Main`); wall count
equals `Nat.primeCounting` by Rayn-McLean's wall theorem (`prime_count_walls`). Tau Ceti (Apache-2.0,
The Tau Ceti contributors): two private lemmas copied, one proof adapted (`Contour.lean`).

## Route
The gap method of the Sharp file (left edge at Re s = 1/2 + a) cannot reach von Koch: near the critical
line the sup of zeta'/zeta is log t / a, so every a gives sqrt(x) log^2 x / a, and a = 1/log x is forced
by the factor x^a. Instead: the truncated explicit formula. Tau Ceti has the rectangle residue theorem
with a finite pole set (`TauCeti.Contour.integral_vertical_eq_uShaped_symm_add_two_pi_mul_sum_residue`),
the residue of a log-derivative (`logDeriv_eventuallyEq_principalPart`), safe heights
(`riemannZeta_safe_height`: zeta'/zeta << log^2 T on Im s = +-T', T' in [T, T+1]) and the window zero
count. Rectangle [1/4, 1 + 1/log x] x [-T, T], T in [x, x+1], epsilon = x^(-1/2): residue at 1 is the
main term; residues at the zeros give sum m(rho) M(rho) x^rho, bounded by sqrt(x) sum m(rho)/|rho|
<< sqrt(x) log^2 T; left edge at distance 1/4 from the zeros is O(x^(1/4) log^2 x); tails
O(sqrt(x) log^2 x); horizontal edges O(log^2 x / sqrt(x)).

## Compiled (all sorry-free)
- Copied: wall section (`prime_count_walls`), `riemannZeta_ne_zero_of_half_lt`, `re_eq_half_of_zero`,
  Tau Ceti private copies, `four_le_log_of_le`, `theta_sub_le_psi_sub_add`.
- `riemannZeta_ne_zero_of_re_ne_half`: RH gives zeta(s) != 0 for Re s > -2, Re s != 1/2.
- `logDeriv_bound_of_RH_dist : ∃ C, 0 ≤ C ∧ ∀ a, 0 < a → a ≤ 1 → ∀ s ≠ 1, -1 ≤ Re s → Re s ≤ 2 →
  a ≤ |Re s - 1/2| → ‖zeta'/zeta(s) + 1/(s-1)‖ ≤ C/a log(|Im s|+2)`.
- `riemannZeta_eventually_ne_zero`, `residue_neg_logDeriv_riemannZeta_mul`: residue at a zero rho of any
  F agreeing near rho with -(logDeriv zeta) H (H analytic) is -m(rho) H(rho).
- `one_le_log_add_two`, `sum_order_div_norm_le_half`, `sum_order_div_norm_le : ∃ C, 0 ≤ C ∧ ∀ T ≥ 1,
  ∀ P : Finset ℂ, (zeros with 1/4 ≤ Re ≤ 1, |Im| ≤ T) → ∑ m(z)/‖z‖ ≤ C log(T+2)^2` (unit windows +
  harmonic sum).
- `tsum_mul_smoothCutoff_eq_contour_add_sum_residue`: Tau Ceti's smoothed-sum contour identity with a
  finite pole set P (tails + left edge + horizontal term, over 2 pi, plus ∑_{p ∈ P} residue f p).
- `norm_mul_mul_cpow_le'` (copy), `vk_terms_le` (private arithmetic of the seven terms).
- `psi_sub_le_sqrt_log_sq : ∃ C, 0 ≤ C ∧ ∀ x ≥ 55, |ψ x - x| ≤ C * √x * log x ^ 2` (von Koch).
- `psi_sub_le_sqrt_log_sq_of_RH : ∃ C x₀, ∀ x ≥ x₀, |ψ x - x| ≤ C * √x * log x ^ 2`.
- `theta_sub_le_sqrt_log_sq`, `theta_sub_le_sqrt_log_sq_of_RH` (same for θ).
- `primeCounting_sub_logIntegral_le_sqrt_log : ∃ C, 0 ≤ C ∧ ∀ x ≥ 55, |π⌊x⌋₊ - Li x| ≤ C * √x * log x`.
- `primeCounting_sub_logIntegral_le_sqrt_log_of_RH : ∃ C x₀, ∀ x ≥ x₀, ...` (Stage 2 reduced to Stage 1
  plus the existing transfer `Chebyshev.abs_primeCounting_sub_logIntegral_le` with
  ε(t) = K t^(-1/2) log^2 t; no log lost).
- `walls_meet_rh_sqrt_log : ∃ C, ∃ N₀ : ℕ, ∀ N ≥ N₀, |(2 + #{n ≤ N | passes n} : ℝ) - Li N| ≤
  C * √N * log N` (N₀ = 55).

## Remaining
Nothing for the two requested stages. No WIP file needed.

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
The external input has exactly mathlib's type `RiemannHypothesis`.
Upstream supplies `riemannHypothesis` in `src/Main.lean` at
40e56bab026552e089d7afcfeff08d2defb9c005. This module accepts the
proof as an argument so it can also be checked on the local toolchain.
-/
namespace RHFilter.External

open Filter
open scoped Topology

theorem zeroFreeRight (rh : RiemannHypothesis) {s : ℂ}
    (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) : riemannZeta s ≠ 0 := by
  intro hz
  have htriv : ¬ ∃ n : ℕ, s = -2 * (n + 1) := by
    rintro ⟨n, rfl⟩
    norm_num [Complex.mul_re] at hs
    linarith [Nat.cast_nonneg (α := ℝ) n]
  exact (ne_of_gt hs) (rh s hz htriv hs1)

/-- Analytic convention for the reciprocal at the pole of zeta. -/
noncomputable def reciprocal (s : ℂ) : ℂ :=
  if s = 1 then 0 else (riemannZeta s)⁻¹

theorem reciprocal_deriv_one : HasDerivAt reciprocal 1 1 := by
  rw [hasDerivAt_iff_tendsto_slope, slope_fun_def_field]
  have h := riemannZeta_residue_one.inv₀ (by norm_num : (1 : ℂ) ≠ 0)
  rw [inv_one] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz1 : z ≠ 1 := hz
  simp [reciprocal, hz1, div_eq_mul_inv, mul_comm]

theorem reciprocal_holomorphic (rh : RiemannHypothesis) :
    AnalyticOnNhd ℂ reciprocal {s : ℂ | 1 / 2 < s.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro s hs
  by_cases hs1 : s = 1
  · subst s
    exact reciprocal_deriv_one.differentiableAt.differentiableWithinAt
  · have hd := (differentiableAt_riemannZeta hs1).inv (zeroFreeRight rh hs hs1)
    apply DifferentiableAt.differentiableWithinAt
    apply hd.congr_of_eventuallyEq
    filter_upwards [isOpen_compl_singleton.mem_nhds hs1] with z hz
    simp [reciprocal, show z ≠ 1 from hz]

/-- Compact subsets admit a bound that can depend on the height of the contour. -/
theorem reciprocal_bounded_on_compact (rh : RiemannHypothesis) {K : Set ℂ}
    (hK : IsCompact K) (hsub : K ⊆ {s : ℂ | 1 / 2 < s.re}) :
    ∃ C : ℝ, ∀ s ∈ K, ‖reciprocal s‖ ≤ C :=
  hK.exists_bound_of_continuousOn ((reciprocal_holomorphic rh).continuousOn.mono hsub)

end RHFilter.External

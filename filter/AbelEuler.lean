import Abel
import JumpSeries
import Mathlib.NumberTheory.LSeries.SumCoeff

noncomputable section
open Set Filter MeasureTheory Asymptotics

namespace RHFilter.Abel

/-- The signed jumps telescope with the actual inclusive endpoint. -/
theorem sum_jumps (N : ℕ) : (∑ k ∈ Finset.Icc 1 N, Source.jumps k) = (grid N : ℂ) := by
  induction N with
  | zero => simp [grid, pref, partialSum]
  | succ n ih =>
    rw [← Finset.insert_Icc_right_eq_Icc_add_one (by omega : 1 ≤ n + 1),
      Finset.sum_insert (by simp : n+1 ∉ Finset.Icc 1 n), ih, Source.jumps_eq _ (by omega)]
    simp

/-- At the half-integer convention the inclusive prefix is precisely N. -/
theorem half_step (N : ℕ) : step ((N : ℝ) + 1/2) = ∑ k ∈ Finset.Icc 1 N, Source.jumps k := by
  rw [step_grid, sum_jumps]
  have h := RHRealGrid.half_floor_div N 1
  simpa using congrArg (fun n => (grid n : ℂ)) (by simpa using h : ⌊(N:ℝ)+1/2⌋₊ = N)

private theorem jump_sum_linear :
    (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, Source.jumps k) =O[atTop] fun n => (n : ℝ)^(1 : ℝ) := by
  refine isBigO_iff.mpr ⟨5/2, Filter.Eventually.of_forall ?_⟩
  intro n
  rw [sum_jumps, Real.rpow_one, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n)]
  have hn : ‖(grid n : ℂ)‖ = |(grid n : ℝ)| := Complex.norm_intCast _
  rw [hn]
  exact abs_grid_le_five_halves n

/-- Euler-half-plane partial summation for the full signed filter.
The contribution on (0,1) vanishes and the point 1 has zero Lebesgue mass. -/
theorem transform_eq_jumpSeries {s : ℂ} (hs : 1 < s.re) : transform s = LSeries Source.jumps s := by
  rw [LSeries_eq_mul_integral _ zero_le_one hs (Source.jumps_hasSum hs).summable jump_sum_linear,
    transform, mellin]
  congr 1
  let g : ℝ → ℂ := fun t => (t : ℂ)^(-s - 1) • step t
  calc
    (∫ t : ℝ in Ioi 0, g t) = ∫ t : ℝ in Ici 1, g t := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
        (Ici_subset_Ioi.mpr (by norm_num : (0 : ℝ) < 1))
      intro t ht
      have hlt : t < 1 := lt_of_not_ge ht.2
      simp [g, step_zero (le_of_lt ht.1) hlt]
    _ = ∫ t : ℝ in Ioi 1, g t := integral_Ici_eq_integral_Ioi
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      simp only [g, smul_eq_mul, step_grid, sum_jumps]
      rw [show -(s + 1) = -s - 1 by ring, mul_comm]

/-- The analytic Euler-side identity with the source multiplier. -/
theorem transform_eq_source {s : ℂ} (hs : 1 < s.re) :
    transform s = Contour.poly (Contour.phase s) * (1 / riemannZeta s) :=
  (transform_eq_jumpSeries hs).trans (Source.jumps_hasSum hs).tsum_eq

end RHFilter.Abel

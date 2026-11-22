import Linear
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Function.Floor

noncomputable section
open Set Filter MeasureTheory Asymptotics
open scoped Topology

namespace RHFilter.Abel

/-- The inclusive summatory function at scale one, with the original endpoints. -/
def step (t : ℝ) : ℂ := (F (t/4) : ℂ)

/-- Abel continuation at scale one. The factor s is from partial summation. -/
def transform (s : ℂ) : ℂ := s * mellin step (-s)

theorem step_grid (t : ℝ) : step t = (grid ⌊t⌋₊ : ℂ) := by
  rw [step, F_grid, show 4*(t/4)=t by ring]
  norm_cast

theorem step_zero {t : ℝ} (ht : 0 ≤ t) (hu : t < 1) : step t = 0 := by
  simp only [step, F_zero_before_first (div_nonneg ht (by norm_num)) (by linarith : t/4 < 1/4),
    Complex.ofReal_zero]

theorem measurable_step : Measurable step := by
  simp_rw [funext step_grid]
  exact (measurable_of_countable (f := fun n : ℕ => (grid n : ℂ))).comp Nat.measurable_floor

theorem locallyIntegrableOn_step : LocallyIntegrableOn step (Ioi 0) := by
  have hc : Continuous (fun t : ℝ => (5/2 : ℝ)*max t 0) := by fun_prop
  apply (hc.locallyIntegrable.locallyIntegrableOn (Ioi 0)).mono measurable_step.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro t
  rw [step_grid]
  have hnorm : ‖(grid ⌊t⌋₊ : ℂ)‖ = |(grid ⌊t⌋₊ : ℝ)| := by
    have hcast (z : ℤ) : (z : ℂ) = ((z : ℝ) : ℂ) := by norm_cast
    rw [hcast (grid ⌊t⌋₊), Complex.norm_real, Real.norm_eq_abs]
  have hpos : (0 : ℝ) ≤ (5/2)*max t 0 := mul_nonneg (by norm_num) (le_max_right _ _)
  rw [hnorm, Real.norm_eq_abs, abs_of_nonneg hpos]
  apply (abs_grid_le_five_halves _).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  by_cases ht : 0 ≤ t
  · simpa [max_eq_left ht] using Nat.floor_le ht
  · rw [Nat.floor_eq_zero.mpr (by linarith), Nat.cast_zero]
    exact le_max_right _ _

/-- This is an input to the reverse implication. It bounds both signs of F. -/
def Bilateral : Prop := ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
  ∀ x : ℝ, 0 < x → |F x| ≤ C*x^(1/2+ε)

private theorem step_top (h : Bilateral) {ε : ℝ} (he : 0 < ε) :
    step =O[atTop] (fun t : ℝ => t^(1/2+ε)) := by
  obtain ⟨C, hC, hb⟩ := h ε he
  refine isBigO_iff.mpr ⟨C, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  simp only [step, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg ht.le _)]
  exact (hb _ (by positivity : 0 < t/4)).trans <| mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)) hC

private theorem step_bot (b : ℝ) : step =O[𝓝[>] 0] (fun t : ℝ => t^(-b)) := by
  refine isBigO_iff.mpr ⟨1, ?_⟩
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0:ℝ)<1))]
    with t ht hu
  rw [step_zero (le_of_lt ht) hu, norm_zero, one_mul]
  exact norm_nonneg _

theorem convergent_and_differentiable (h : Bilateral) {s : ℂ} (hs : 1/2 < s.re) :
    MellinConvergent step (-s) ∧ DifferentiableAt ℂ transform s := by
  let ε := (s.re-1/2)/2
  have he : 0 < ε := by dsimp [ε]; linarith
  have hout : (-s).re < -(1/2+ε) := by dsimp [ε]; linarith
  have hin : (-s).re - 1 < (-s).re := by linarith
  have htop : step =O[atTop] (fun t : ℝ => t^(-(-(1/2+ε)))) := by
    simpa only [neg_neg] using step_top h he
  exact ⟨mellinConvergent_of_isBigO_rpow locallyIntegrableOn_step htop hout (step_bot _) hin,
    differentiableAt_id.mul ((mellin_differentiableAt_of_isBigO_rpow locallyIntegrableOn_step
      htop hout (step_bot _) hin).comp s differentiableAt_id.neg)⟩

theorem transform_analytic (h : Bilateral) :
    AnalyticOnNhd ℂ transform {s : ℂ | 1/2 < s.re} := by
  have hd : DifferentiableOn ℂ transform {s : ℂ | 1/2 < s.re} :=
    fun s hs => (convergent_and_differentiable h hs).2.differentiableWithinAt
  exact hd.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)

end RHFilter.Abel

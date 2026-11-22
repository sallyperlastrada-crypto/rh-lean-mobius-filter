import AbelEuler
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

noncomputable section
open Set Filter MeasureTheory Asymptotics

namespace RHFilter.LandauSource

/-- The compensator is attached to the same inclusive, signed filter. -/
def shifted (a C t : ℝ) : ℝ := (Abel.step t).re + C * t^a

theorem measurable_shifted (a C : ℝ) : Measurable (shifted a C) :=
  (Complex.continuous_re.measurable.comp Abel.measurable_step).add
    (measurable_const.mul (measurable_id.pow_const a))

theorem shifted_nonneg {a C : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hF : ∀ x : ℝ, 0 < x → -C*x^a ≤ F x) {t : ℝ} (ht : 1 < t) : 0 ≤ shifted a C t := by
  have ht' : 0 < t := by linarith
  have hpower := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (by positivity : 0 ≤ t/4) (by linarith : t/4 ≤ t) ha) hC
  simp only [shifted, Abel.step, Complex.ofReal_re]
  linarith [hF (t/4) (by positivity)]

theorem step_integrable {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ => Abel.step t * (t : ℂ)^(-s-1)) (Ioi 1) := by
  have hk : Measurable (fun t : ℝ => (t : ℂ)^(-s-1)) := by fun_prop
  apply ((integrableOn_Ioi_rpow_of_lt (by linarith : -s.re < -1)
    (by norm_num : (0 : ℝ) < 1)).const_mul (5/2 : ℝ)).mono'
    (Abel.measurable_step.mul hk).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht' : 0 < t := lt_trans (by norm_num : (0:ℝ) < 1) ht
  have hb : ‖Abel.step t‖ ≤ (5/2)*t := by
    rw [Abel.step_grid, Complex.norm_intCast]
    exact (abs_grid_le_five_halves _).trans
      (mul_le_mul_of_nonneg_left (Nat.floor_le ht'.le) (by norm_num))
  change ‖Abel.step t * (t : ℂ)^(-s-1)‖ ≤ (5/2)*t^(-s.re)
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht', Complex.sub_re, Complex.neg_re,
    Complex.one_re]
  calc
    _ ≤ ((5/2)*t)*t^(-s.re-1) := mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg ht'.le _)
    _ = (5/2) * t^(-s.re) := by
      have h := Real.rpow_add ht' (1 : ℝ) (-s.re-1)
      rw [Real.rpow_one, show (1 : ℝ)+(-s.re-1) = -s.re by ring] at h
      rw [mul_assoc, ← h]

private theorem shifted_kernel {a C t : ℝ} (ht : 0 < t) (s : ℂ) :
    (shifted a C t : ℂ) * (t : ℂ)^(-s-1) =
    Abel.step t * (t : ℂ)^(-s-1) + (C : ℂ)*(t : ℂ)^((a : ℂ)-s-1) := by
  have hr : ((Abel.step t).re : ℂ) = Abel.step t := by simp [Abel.step]
  rw [shifted, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_cpow ht.le, hr, add_mul,
    mul_assoc, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ht.ne'),
    show (a : ℂ)+(-s-1) = a-s-1 by ring]

theorem shifted_complex_integrable {a : ℝ} (C : ℝ) (ha : a ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ => (shifted a C t : ℂ) * (t : ℂ)^(-s-1)) (Ioi 1) := by
  have hpow : ((a : ℂ)-s-1).re < -1 := by simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re]; linarith
  have h := (step_integrable hs).add
    ((integrableOn_Ioi_cpow_of_lt hpow (by norm_num : (0 : ℝ) < 1)).const_mul (C : ℂ))
  exact h.congr (ae_restrict_mem measurableSet_Ioi |>.mono fun t ht =>
    (shifted_kernel (lt_trans (by norm_num : (0:ℝ)<1) ht) s).symm)

/-- The initially convergent real integrals required by Landau. -/
theorem shifted_integrable {a : ℝ} (C : ℝ) (ha : a ≤ 1) {σ : ℝ} (hσ : 1 < σ) :
    IntegrableOn (fun t : ℝ => shifted a C t * t^(-σ-1)) (Ioi 1) := by
  have h := (shifted_complex_integrable C ha (s := (σ : ℂ)) (by simpa using hσ)).re
  apply h.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht' : 0 < t := lt_trans (by norm_num : (0:ℝ)<1) ht
  rw [show -(σ : ℂ)-1 = ((-σ-1 : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_cpow ht'.le, ← Complex.ofReal_mul]
  rfl

/-- Exact compensator on the Euler side, including its complete simple pole. -/
theorem transform_shifted {a : ℝ} (C : ℝ) (ha : a ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    (∫ t : ℝ in Ioi 1, (shifted a C t : ℂ) * (t : ℂ)^(-s-1)) =
      Abel.transform s / s + (C : ℂ)/(s-(a : ℂ)) := by
  have hpow : ((a : ℂ)-s-1).re < -1 := by simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re]; linarith
  have heq := setIntegral_congr_fun (μ := volume) measurableSet_Ioi
    (fun (t : ℝ) (ht : t ∈ Ioi 1) => shifted_kernel (lt_trans (by norm_num : (0:ℝ) < 1) ht) s (a := a) (C := C))
  rw [heq, integral_add (step_integrable hs)
    ((integrableOn_Ioi_cpow_of_lt hpow (by norm_num : (0:ℝ) < 1)).const_mul (C : ℂ)),
    integral_const_mul, integral_Ioi_cpow_of_lt hpow (by norm_num : (0:ℝ) < 1)]
  congr 1
  · have hs0 : s ≠ 0 := Complex.ne_zero_of_re_pos (by linarith)
    rw [Abel.transform, mul_div_cancel_left₀ _ hs0, mellin]
    let g : ℝ → ℂ := fun t => (t : ℂ)^(-s-1) • Abel.step t
    have hcut : (∫ t in Ioi (0:ℝ), g t) = ∫ t in Ici (1:ℝ), g t := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
        (Ici_subset_Ioi.mpr (by norm_num : (0 : ℝ) < 1))
      intro t ht
      simp [g, Abel.step_zero (le_of_lt ht.1) (lt_of_not_ge ht.2)]
    rw [show (∫ t in Ioi (0:ℝ), (t:ℂ)^(-s-1) • Abel.step t) = _ from hcut, integral_Ici_eq_integral_Ioi]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    exact mul_comm _ _
  · rw [Complex.ofReal_one, Complex.one_cpow, show (a : ℂ)-s-1+1 = -(s-a) by ring]
    simp [div_eq_mul_inv]

end RHFilter.LandauSource

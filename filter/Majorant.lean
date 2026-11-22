import Contour
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.Positivity

noncomputable section
open Complex
open scoped Interval

namespace RHFilter.Majorant
open RHFilter.Contour

theorem norm_phase_le_one {s : ℂ} (hs : 0 ≤ s.re) : ‖phase s‖ ≤ 1 := by
  rw [phase, Complex.norm_exp, Real.exp_le_one_iff]
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im, neg_zero, zero_mul, sub_zero]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Real.log_nonneg (by norm_num))) hs

theorem norm_filter_le {s : ℂ} (hs : 0 ≤ s.re) : ‖poly (phase s)‖ ≤ 18 := by
  let z := phase s
  have hz : ‖z‖ ≤ 1 := norm_phase_le_one hs
  have hc : ‖(2:ℂ)*z‖ ≤ 2 := by
    rw [norm_mul]
    norm_num
    linarith
  have h1 : ‖(1:ℂ)-z‖ ≤ 2 := (norm_sub_le _ _).trans (by simp; linarith)
  have h2 : ‖(1:ℂ)-2*z‖ ≤ 3 := (norm_sub_le _ _).trans (by simp; linarith)
  change ‖poly z‖ ≤ 18
  rw [poly_factor, norm_mul, norm_neg, norm_pow]
  calc
    _ ≤ 2 * 3^2 := mul_le_mul h1 (pow_le_pow_left₀ (norm_nonneg _) h2 2) (by positivity) (by norm_num)
    _ = 18 := by norm_num

/-- Estimate the complete signed filter before bounding its contour. -/
theorem kernel_le (Z : ℂ → ℂ) {y : ℝ} {s : ℂ} (hy : 0 < y) (hs : 0 ≤ s.re) :
    ‖kernel Z y s‖ ≤ 18 * y^s.re * ‖Z s‖ / ‖s‖ := by
  rw [kernel, norm_mul, base, norm_div, norm_mul, Complex.norm_exp, Real.rpow_def_of_pos hy]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  calc
    _ ≤ 18 * (Real.exp (Real.log y * s.re) * ‖Z s‖ / ‖s‖) :=
      mul_le_mul_of_nonneg_right (norm_filter_le hs) (by positivity)
    _ = _ := by ring

private theorem line_norm (a t : ℝ) : |t| ≤ ‖(a:ℂ) + t*I‖ := by
  simpa using Complex.abs_im_le_norm ((a:ℂ) + t*I)

/-- Uniform majorant on either horizontal side given a reciprocal bound at that height. -/
theorem horizontal_le (Z : ℂ → ℂ) {y t b c B : ℝ} (hy : 1 ≤ y)
    (hb : 0 ≤ b) (hbc : b ≤ c) (ht : t ≠ 0)
    (hZ : ∀ a ∈ Set.Icc b c, ‖Z (a+t*I)‖ ≤ B) :
    ‖horiz (kernel Z y) t b c‖ ≤ (18 * y^c * B / |t|) * |c-b| := by
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro a ha
  rw [Set.uIoc_of_le hbc] at ha
  have hmem : a ∈ Set.Icc b c := ⟨ha.1.le,ha.2⟩
  have hA := kernel_le Z (s := (a:ℂ) + t*I) (lt_of_lt_of_le zero_lt_one hy)
    (by simpa using hb.trans hmem.1)
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
      mul_zero, Complex.ofReal_im, Complex.I_im, zero_mul, sub_zero, add_zero] at hA
  refine hA.trans ?_
  apply div_le_div₀ _ _ (abs_pos.mpr ht) (line_norm a t)
  · have := (norm_nonneg (Z (a+t*I))).trans (hZ a hmem)
    positivity
  · apply mul_le_mul _ (hZ a hmem) (norm_nonneg _) (by positivity)
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hy hmem.2) (by norm_num)

/-- The compact middle of the vertical segment is bounded using its positive abscissa. -/
theorem vertical_centre_le (Z : ℂ → ℂ) {y b B : ℝ} (hy : 0 < y) (hb : 0 < b)
    (hZ : ∀ t ∈ Set.Icc (-1:ℝ) 1, ‖Z (b+t*I)‖ ≤ B) :
    ‖vert (kernel Z y) b (-1) 1‖ ≤ (18 * y^b * B / b) * 2 := by
  have hlen : |(1:ℝ)-(-1)| = 2 := by norm_num
  rw [← hlen]
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro t ht
  rw [Set.uIoc_of_le (by norm_num : (-1:ℝ) ≤ 1)] at ht
  have hzt := hZ t ⟨ht.1.le, ht.2⟩
  have hA := kernel_le Z (s := (b:ℂ) + t*I) hy (by simpa using hb.le)
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
      mul_zero, Complex.ofReal_im, Complex.I_im, zero_mul, sub_zero, add_zero] at hA
  refine hA.trans (div_le_div₀ ?_ ?_ hb ?_)
  · have := (norm_nonneg _).trans hzt
    positivity
  · exact mul_le_mul_of_nonneg_left hzt (by positivity)
  · simpa using Complex.re_le_norm ((b:ℂ)+t*I)

/-- On either outer vertical ray the denominator controls the actual height. -/
theorem vertical_tail_le (Z : ℂ → ℂ) {y b t C η : ℝ} (hy : 0 < y)
    (hb : 0 ≤ b) (ht : t ≠ 0) (hZ : ‖Z (b+t*I)‖ ≤ C * |t|^η) :
    ‖kernel Z y (b+t*I)‖ ≤ 18 * y^b * C * |t|^(η-1) := by
  have hA := kernel_le Z (s := (b:ℂ) + t*I) hy (by simpa using hb)
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
      mul_zero, Complex.ofReal_im, Complex.I_im, zero_mul, sub_zero, add_zero] at hA
  have hpos := abs_pos.mpr ht
  calc
    _ ≤ _ := hA
    _ ≤ 18 * y^b * (C * |t|^η) / |t| := by
      apply div_le_div₀ _ _ hpos (line_norm b t)
      · have := (norm_nonneg (Z (b+t*I))).trans hZ
        positivity
      · exact mul_le_mul_of_nonneg_left hZ (by positivity)
    _ = _ := by rw [Real.rpow_sub_one hpos.ne']; ring

/-- Actual integral over either exterior segment, parametrized by its positive height.
The endpoints 1 and T give the subtraction of 1 in the power moment. -/
theorem vertical_arc_le (Z : ℂ → ℂ) {y b C η d T : ℝ} (hy : 0 < y)
    (hb : 0 ≤ b) (hη : 0 < η) (hd : |d| = 1) (hT : 1 ≤ T)
    (hZ : ∀ t ∈ Set.Icc 1 T, ‖Z (b + (d*t : ℝ)*I)‖ ≤ C * t^η) :
    ‖∫ t : ℝ in (1:ℝ)..T, kernel Z y (b + (d*t : ℝ)*I)‖ ≤
      (18 * y^b * C) * ((T^η - 1) / η) := by
  calc
    _ ≤ ∫ t : ℝ in (1:ℝ)..T, (18 * y^b * C) * t^(η-1) := by
      apply intervalIntegral.norm_integral_le_of_norm_le hT
      · apply Filter.Eventually.of_forall
        intro t ht
        have ht0 : 0 < t := lt_trans zero_lt_one ht.1
        have habs : |d*t| = t := by rw [abs_mul, hd, one_mul, abs_of_pos ht0]
        have hdt : d*t ≠ 0 := abs_pos.mp (habs.symm ▸ ht0)
        simpa only [habs] using vertical_tail_le Z hy hb hdt (by simpa only [habs] using hZ t ⟨ht.1.le, ht.2⟩)
      · exact (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < η-1)).const_mul _
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith : -1 < η-1))]
      simp

/-- The two tails and the compact middle on the shifted line. -/
theorem vertical_full_le (Z : ℂ → ℂ) {y b B C η T : ℝ} (hy : 0 < y)
    (hb : 0 < b) (hη : 0 < η) (hT : 1 ≤ T)
    (hcont : Continuous (fun t : ℝ => kernel Z y (b+t*I)))
    (hmid : ∀ t ∈ Set.Icc (-1:ℝ) 1, ‖Z (b+t*I)‖ ≤ B)
    (hZ : ∀ t : ℝ, 1 ≤ |t| → |t| ≤ T → ‖Z (b+t*I)‖ ≤ C * |t|^η) :
    ‖vert (kernel Z y) b (-T) T‖ ≤ (18*y^b*B/b)*2 + 2*(18*y^b*C)*((T^η-1)/η) := by
  let f := fun t : ℝ => kernel Z y (b + t*I)
  have hi (u v : ℝ) : IntervalIntegrable f MeasureTheory.volume u v :=
    hcont.intervalIntegrable _ _
  have hsum : (∫ t in -T..T, f t) = ((∫ t in -T..(-1:ℝ), f t) +
      (∫ t in (-1:ℝ)..1, f t)) + (∫ t in (1:ℝ)..T, f t) := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hi _ _) (hi _ _),
        intervalIntegral.integral_add_adjacent_intervals (hi _ _) (hi _ _)]
  have ha (d : ℝ) (hd : |d| = 1) := vertical_arc_le Z hy hb.le hη hd hT
    (C := C) (by
      intro t ht
      have he : |d*t| = t := by rw [abs_mul, hd, one_mul, abs_of_nonneg (by linarith [ht.1] : 0 ≤ t)]
      simpa only [he] using hZ (d*t) (he.symm ▸ ht.1) (he.symm ▸ ht.2))
  have pos := ha 1 (by norm_num)
  simp only [one_mul] at pos
  have neg := ha (-1) (by norm_num)
  simp only [neg_one_mul] at neg
  change ‖∫ t in (1:ℝ)..T, f (-t)‖ ≤ _ at neg
  rw [intervalIntegral.integral_comp_neg] at neg
  have mid := vertical_centre_le Z hy hb hmid
  change ‖∫ t in -T..T, f t‖ ≤ _
  rw [hsum]
  have dn := norm_add_le ((∫ t in -T..(-1:ℝ), f t) + (∫ t in (-1:ℝ)..1, f t)) (∫ t in (1:ℝ)..T, f t)
  have dm := norm_add_le (∫ t in -T..(-1:ℝ), f t) (∫ t in (-1:ℝ)..1, f t)
  change ‖∫ t in (1:ℝ)..T, f t‖ ≤ _ at pos
  change ‖∫ t in (-1:ℝ)..1, f t‖ ≤ _ at mid
  linarith

end RHFilter.Majorant

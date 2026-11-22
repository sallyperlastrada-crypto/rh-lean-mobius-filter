import FilterConverse

/-! Analytic continuation along the real axis needed by the one-sided
Mellin argument. The pole at one is removed in the definition of the
candidate, where its denominator uses mathlib's entire regularization. -/
namespace RHFilter.LandauAxis
noncomputable section

open Complex RHFilter.Contour

abbrev regular := DirichletCharacter.LFunctionTrivChar₁ 1

theorem regular_eq {s : ℂ} (h : s ≠ 1) : regular s = (s-1)*riemannZeta s := by
  simp only [regular, DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne h,
    DirichletCharacter.LFunctionTrivChar, DirichletCharacter.LFunction_modOne_eq]

def candidate (a C : ℝ) (s : ℂ) : ℂ :=
  (s-1) * poly (phase s) / (s * regular s) + C / (s-a)

theorem candidate_analytic {a C : ℝ} {s : ℂ} (hs : s ≠ 0)
    (hr : regular s ≠ 0) (ha : s ≠ (a : ℂ)) : AnalyticAt ℂ (candidate a C) s := by
  have hReg : AnalyticAt ℂ regular s :=
    (DirichletCharacter.differentiable_LFunctionTrivChar₁ 1).analyticAt s
  have hNum : AnalyticAt ℂ (fun z : ℂ => (z-1)*poly (phase z)) s := by
    unfold poly phase
    fun_prop
  exact (hNum.div (analyticAt_id.mul hReg) (mul_ne_zero hs hr)).add
    (analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr ha))

theorem candidate_on_right {a C : ℝ} (ha : a < 1) {s : ℂ} (hs : 1 < s.re) :
    AnalyticAt ℂ (candidate a C) s := by
  have h₁ : s ≠ 1 := by rintro rfl; simp at hs
  apply candidate_analytic
  · rintro rfl; norm_num at hs
  · rw [regular_eq h₁]
    exact mul_ne_zero (sub_ne_zero.mpr h₁) (riemannZeta_ne_zero_of_one_lt_re hs)
  · rintro rfl; change 1 < a at hs; linarith

/-- The real input here is unconditional and strictly weaker than a complex
zero-free half-plane. The point one uses the value of the regularization. -/
theorem candidate_on_real {a C : ℝ} (ha : 0 < a)
    (axis : ∀ u : ℝ, 0 < u → u < 1 → riemannZeta (u : ℂ) ≠ 0)
    {u : ℝ} (hu : a < u) (hb : u ≤ 1) : AnalyticAt ℂ (candidate a C) (u : ℂ) := by
  have hu0 : 0 < u := ha.trans hu
  apply candidate_analytic
  · exact_mod_cast hu0.ne'
  · rcases hb.eq_or_lt with rfl | hlt
    · simpa only [ofReal_one] using DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero 1
    · have h1 : (u : ℂ) ≠ 1 := by exact_mod_cast hlt.ne
      rw [regular_eq h1]
      exact mul_ne_zero (sub_ne_zero.mpr h1) (axis u hu0 hlt)
  · exact_mod_cast hu.ne'

theorem candidate_eq_right {a C : ℝ} {s : ℂ} (hs : 1 < s.re) :
    candidate a C s = poly (phase s)/(s*riemannZeta s) + C/(s-a) := by
  have h₁ : s ≠ 1 := by rintro rfl; simp at hs
  have h₀ : s ≠ 0 := by rintro rfl; norm_num at hs
  have hz := riemannZeta_ne_zero_of_one_lt_re hs
  unfold candidate
  rw [regular_eq h₁]
  congr 1
  field_simp [h₀, hz, sub_ne_zero.mpr h₁]

end
end RHFilter.LandauAxis

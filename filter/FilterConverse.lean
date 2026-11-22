import Contour
import RHReduction
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Convex
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-! Converse for the dyadic symbol. An extension of the Euler-side source
identity suffices. The regularized product is continued through the pole
before it is evaluated at a hypothetical zero. -/
namespace RHFilter.Converse

open Complex Filter RHFilter.Contour
open scoped Topology

private theorem regularized_zeta {s : ℂ} (hs : s ≠ 1) :
    DirichletCharacter.LFunctionTrivChar₁ 1 s = (s - 1) * riemannZeta s := by
  simp only [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs,
    DirichletCharacter.LFunctionTrivChar, DirichletCharacter.LFunction_modOne_eq]

/-- The exact dyadic symbol has no roots between the critical line and Re = 1. -/
theorem symbol_ne_zero {s : ℂ} (hl : 1 / 2 < s.re) (hu : s.re < 1) :
    poly (phase s) ≠ 0 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnorm : ‖phase s‖ = Real.exp (-(Real.log 2) * s.re) := by
    simp only [phase, Complex.norm_exp, Complex.mul_re, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, neg_zero, zero_mul, sub_zero]
  have hlt : ‖phase s‖ < 1 := by
    rw [hnorm, ← Real.exp_zero]
    apply Real.exp_lt_exp.mpr
    nlinarith
  have hgt : 1 / 2 < ‖phase s‖ := by
    have h : Real.exp (-(Real.log 2)) < Real.exp (-(Real.log 2) * s.re) :=
      Real.exp_lt_exp.mpr (by nlinarith)
    simpa [hnorm, Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ)<2), one_div] using h
  have h₁ : 1 - phase s ≠ 0 := by
    intro h
    rw [← sub_eq_zero.mp h, norm_one] at hlt
    exact (lt_irrefl _) hlt
  have h₂ : 1 - 2 * phase s ≠ 0 := by
    intro h
    have hm := congrArg norm (sub_eq_zero.mp h)
    rw [norm_one, norm_mul] at hm
    norm_num at hm
    linarith
  rw [poly_factor]
  exact mul_ne_zero (neg_ne_zero.mpr h₁) (pow_ne_zero _ h₂)

/-- Continue the product after regularizing the pole of zeta at one. -/
theorem continued_product_above {a : ℝ} (ha : a < 1) {G : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ G {s : ℂ | a < s.re})
    (source : ∀ s : ℂ, 1 < s.re → riemannZeta s * G s = poly (phase s)) :
    ∀ s : ℂ, a < s.re → s ≠ 1 → riemannZeta s * G s = poly (phase s) := by
  let U := {s : ℂ | a < s.re}
  have hL : AnalyticOnNhd ℂ (fun s => DirichletCharacter.LFunctionTrivChar₁ 1 s * G s) U :=
    fun s hs => ((DirichletCharacter.differentiable_LFunctionTrivChar₁ 1).analyticAt s).mul (hg s hs)
  have hR : AnalyticOnNhd ℂ (fun s : ℂ => (s - 1) * poly (phase s)) U := by
    intro s _
    unfold poly phase
    fun_prop
  have hagree : (fun s : ℂ => DirichletCharacter.LFunctionTrivChar₁ 1 s * G s)
      =ᶠ[𝓝 (2 : ℂ)] (fun s : ℂ => (s - 1) * poly (phase s)) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (2 : ℂ) ∈ {s : ℂ | 1 < s.re} by norm_num)] with s hs
    have h : 1 < s.re := hs
    have h1 : s ≠ 1 := by rintro rfl; simp at h
    rw [regularized_zeta h1, mul_assoc, source s h]
  have hid := hL.eqOn_of_preconnected_of_eventuallyEq hR
    (convex_halfSpace_re_gt a).isPreconnected
    (show (2 : ℂ) ∈ U by change a < (2 : ℂ).re; norm_num; linarith) hagree
  intro s hs h1
  have he := hid (show s ∈ U from hs)
  change DirichletCharacter.LFunctionTrivChar₁ 1 s * G s = (s-1) * poly (phase s) at he
  rw [regularized_zeta h1, mul_assoc] at he
  exact mul_left_cancel₀ (sub_ne_zero.mpr h1) he

theorem continued_product {G : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ G {s : ℂ | 1/2 < s.re})
    (source : ∀ s : ℂ, 1 < s.re → riemannZeta s * G s = poly (phase s)) :
    ∀ s : ℂ, 1/2 < s.re → s ≠ 1 → riemannZeta s * G s = poly (phase s) :=
  continued_product_above (by norm_num : (1/2 : ℝ) < 1) hg source

/-- Holomorphic extension of the authentic signed symbol divided by zeta
implies RH. No half-plane zero-free theorem is required as input. -/
theorem rh_of_filtered_extension {G : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ G {s : ℂ | 1/2 < s.re})
    (source : ∀ s : ℂ, 1 < s.re → riemannZeta s * G s = poly (phase s)) :
    RiemannHypothesis := by
  apply RHReduction.of_zeta_right_nonvanishing
  intro s hs h1
  by_cases hu : 1 ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re hu
  · intro hz
    have h := continued_product hg source s hs h1
    rw [hz, zero_mul] at h
    exact symbol_ne_zero hs (lt_of_not_ge hu) h.symm

end RHFilter.Converse

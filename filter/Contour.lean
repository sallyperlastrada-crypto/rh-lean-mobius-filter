import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp

noncomputable section
open Complex
open scoped Interval

namespace RHFilter.Contour

def poly (z : ℂ) : ℂ := -1 + 5*z - 8*z^2 + 4*z^3
def phase (s : ℂ) : ℂ := exp (-(Real.log 2 : ℂ)*s)
def base (Z : ℂ → ℂ) (y : ℝ) (s : ℂ) := exp ((Real.log y : ℂ)*s) * Z s / s
def kernel (Z : ℂ → ℂ) (y : ℝ) (s : ℂ) := poly (phase s) * base Z y s
def atom (Z : ℂ → ℂ) (y : ℝ) (j : ℕ) (s : ℂ) := phase s ^ j * base Z y s

theorem poly_factor (z : ℂ) : poly z = -(1-z)*(1-2*z)^2 := by unfold poly; ring
theorem signed_kernel (Z : ℂ → ℂ) (y : ℝ) (s : ℂ) :
    kernel Z y s = -atom Z y 0 s + 5*atom Z y 1 s - 8*atom Z y 2 s + 4*atom Z y 3 s := by
  unfold kernel atom poly
  ring

def vert (f : ℂ → ℂ) (a L U : ℝ) := ∫ t : ℝ in L..U, f (a+t*I)
def horiz (f : ℂ → ℂ) (t b c : ℝ) := ∫ a : ℝ in b..c, f (a+t*I)
def read (v : ℂ) : ℝ := v.re / (2*Real.pi)

theorem signed_vert (Z : ℂ → ℂ) (y c L U : ℝ)
    (hint : ∀ j : ℕ, IntervalIntegrable (fun t : ℝ => atom Z y j (c+t*I))
       MeasureTheory.volume L U) :
    vert (kernel Z y) c L U = -vert (atom Z y 0) c L U + 5*vert (atom Z y 1) c L U
       - 8*vert (atom Z y 2) c L U + 4*vert (atom Z y 3) c L U := by
  have h0 := (hint 0).neg
  change IntervalIntegrable (fun t : ℝ => -atom Z y 0 (c+t*I)) MeasureTheory.volume L U at h0
  have h1 := (hint 1).const_mul (5:ℂ)
  have h2 := (hint 2).const_mul (8:ℂ)
  have h3 := (hint 3).const_mul (4:ℂ)
  unfold vert
  simp_rw [signed_kernel]
  rw [intervalIntegral.integral_add ((h0.add h1).sub h2) h3,
      intervalIntegral.integral_sub (h0.add h1) h2, intervalIntegral.integral_add h0 h1]
  simp only [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul]

theorem kernel_diff (Z : ℂ → ℂ) (y : ℝ) {s : ℂ} (hZ : DifferentiableAt ℂ Z s)
    (hs : s ≠ 0) : DifferentiableAt ℂ (kernel Z y) s := by
  unfold kernel poly phase base
  fun_prop (disch := assumption)

/-- The complete signed filter crosses the rectangle with both horizontal sides retained. -/
theorem rectangle (Z : ℂ → ℂ) (y b c L U : ℝ) (hb : 1/2 < b) (hbc : b ≤ c)
    (hZ : ∀ s : ℂ, 1/2 < s.re → DifferentiableAt ℂ Z s) :
    horiz (kernel Z y) L b c - horiz (kernel Z y) U b c +
      I * vert (kernel Z y) c L U - I * vert (kernel Z y) b L U = 0 := by
  apply Complex.integral_boundary_rect_eq_zero_of_differentiableOn (kernel Z y)
    (⟨b,L⟩ : ℂ) (⟨c,U⟩ : ℂ)
  intro s hs
  have hr : s.re ∈ Set.uIcc b c := hs.1
  rw [Set.uIcc_of_le hbc] at hr
  have hsr := hb.trans_le hr.1
  exact (kernel_diff Z y (hZ s hsr) (fun he => by simp [he] at hsr; linarith)).differentiableWithinAt

end RHFilter.Contour

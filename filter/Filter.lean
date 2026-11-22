import Parity
import Grid
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

noncomputable section
namespace RHFilter

/-- The original source defined by its four signed odd bands. -/
def F (x : ℝ) : ℝ := (RHRealGrid.bands oddPref x : ℤ)

theorem F_grid (x : ℝ) : F x = (grid ⌊4*x⌋₊ : ℝ) := by
  unfold F
  rw [RHRealGrid.bands_eq_oddSource, RHRealGrid.oddSource_eq_grid pref oddPref pref_eq_odd_sub_half]
  rfl

theorem F_endpoint (N : ℕ) : F ((N:ℝ)/4) = (grid N : ℝ) := by
  unfold F
  rw [RHRealGrid.bands_eq_oddSource, RHRealGrid.oddSource_endpoint pref oddPref pref_eq_odd_sub_half]
  rfl

theorem F_zero_before_first {x : ℝ} (hx : 0 ≤ x) (h : x < 1/4) : F x = 0 := by
  rw [F_grid, (RHRealGrid.cell_iff hx 0).2 (by push_cast; constructor <;> linarith)]
  simp [grid, pref, partialSum]

/-- Exact cost of transport from the integer grid; the input estimate is visible. -/
theorem transfer_grid_lower {a C : ℝ} (ha : 0 < a) (hC : 0 ≤ C)
    (h : ∀ N : ℕ, 0 < N → -C * (N:ℝ)^a ≤ (grid N : ℝ)) {x : ℝ} (hx : 0 < x) :
    -(C * (4:ℝ)^a) * x^a ≤ F x := by
  rw [F_grid]
  let N := ⌊4*x⌋₊
  have hn : (N:ℝ) ≤ 4*x := Nat.floor_le (by linarith)
  have ht := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ (N:ℝ)) hn ha.le
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) hx.le] at ht
  change _ ≤ (grid N : ℝ)
  by_cases hp : 0 < N
  · have := mul_le_mul_of_nonneg_left ht hC
    linarith [h N hp]
  · have hn0 : N = 0 := by omega
    rw [hn0, show grid 0 = 0 by simp [grid, pref, partialSum], Int.cast_zero]
    have : 0 ≤ C * (4:ℝ)^a * x^a := by positivity
    linarith

theorem grid_lower_of_real {a C : ℝ}
    (h : ∀ x : ℝ, 0 < x → -C * x^a ≤ F x) (N : ℕ) (hn : 0 < N) :
    -C * ((N:ℝ)/4)^a ≤ (grid N : ℝ) := by
  rw [← F_endpoint]
  exact h _ (by positivity)

end RHFilter

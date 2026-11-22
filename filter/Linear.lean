import Filter
import Intervals

namespace RHFilter

theorem abs_grid_le_five_halves (N : ℕ) : |(grid N : ℝ)| ≤ (5/2) * (N:ℝ) := by
  have h := abs_grid_le_budget N
  have hi : 2 * |grid N| ≤ 5 * (N:ℤ) := by omega
  have hr : (2:ℝ) * |(grid N : ℝ)| ≤ 5 * (N:ℝ) := by exact_mod_cast hi
  linarith

/-- Unconditional range where 1/2+ε is at least linear, including small x. -/
theorem F_lower_large_epsilon {ε : ℝ} (hε : 1/2 ≤ ε) {x : ℝ} (hx : 0 < x) :
    -((5/2) * (4:ℝ)^(1/2+ε)) * x^(1/2+ε) ≤ F x := by
  apply transfer_grid_lower (by linarith) (by norm_num) _ hx
  intro N hN
  have hn : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have ht := Real.rpow_le_rpow_of_exponent_le hn (by linarith : (1:ℝ) ≤ 1/2+ε)
  rw [Real.rpow_one] at ht
  linarith [(abs_le.mp (abs_grid_le_five_halves N)).1]

end RHFilter

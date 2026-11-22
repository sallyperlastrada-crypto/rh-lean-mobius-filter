import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith

noncomputable section
open Filter
namespace RHFilter.Growth

/-- Any strict gain over log t in the logarithm pays for every positive
power of t. The height threshold may depend on all three real parameters. -/
theorem exp_log_power_subpower (C β η : ℝ) (hβ : β < 1) (hη : 0 < η) :
    ∀ᶠ t : ℝ in atTop, Real.exp (C*(Real.log t)^β) ≤ t^η := by
  have hlim : Tendsto (fun t : ℝ => (Real.log t)^(1-β)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < 1-β)).comp Real.tendsto_log_atTop
  filter_upwards [hlim.eventually (eventually_ge_atTop (C/η)), eventually_gt_atTop (1:ℝ)]
    with t ht h1
  have hl : 0 < Real.log t := Real.log_pos h1
  have hC : C ≤ η*(Real.log t)^(1-β) := by
    simpa [mul_comm] using (div_le_iff₀ hη).mp ht
  rw [Real.rpow_def_of_pos (lt_trans zero_lt_one h1), Real.exp_le_exp]
  calc C*(Real.log t)^β ≤ (η*(Real.log t)^(1-β))*(Real.log t)^β :=
         mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hl.le _)
       _ = Real.log t * η := by
         rw [mul_assoc, ← Real.rpow_add hl, sub_add_cancel, Real.rpow_one, mul_comm]

#print axioms exp_log_power_subpower

end RHFilter.Growth

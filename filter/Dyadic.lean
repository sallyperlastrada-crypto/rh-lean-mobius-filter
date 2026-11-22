import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace RHFilter.Dyadic

def lo (v : ℕ → ℝ) (k : ℕ) := 2*v (k+1) - v k
noncomputable def hi (u : ℕ → ℝ) (k : ℕ) := (u (k+1) - u k) / (2:ℝ)^k

theorem low_step (v : ℕ → ℝ) (k : ℕ) :
    lo v k - lo v (k+1) = -(v k - 3*v (k+1) + 2*v (k+2)) := by
  unfold lo
  ring

theorem high_step (u : ℕ → ℝ) (k : ℕ) :
    hi u k - hi u (k+1) = -(u (k+2) - 3*u (k+1) + 2*u k)/(2:ℝ)^(k+1) := by
  unfold hi
  rw [pow_succ]
  field_simp
  ring

/-- u and v record the upper and lower halves of the orbit, sharing its centre. -/
theorem finite_inverse (u v : ℕ → ℝ) (center : u 0 = v 0) (m n : ℕ) :
    u 0 = -(u 1 - 3*u 0 + 2*v 1)
      + ∑ k ∈ Finset.range m, -(v k - 3*v (k+1) + 2*v (k+2))
      + ∑ k ∈ Finset.range n, -(u (k+2) - 3*u (k+1) + 2*u k)/(2:ℝ)^(k+1)
      + lo v m + hi u n := by
  have tel (g : ℕ → ℝ) (r : ℕ) :
      ∑ k ∈ Finset.range r, (g k - g (k+1)) = g 0 - g r := by
    induction r with
    | zero => simp
    | succ r ih => rw [Finset.sum_range_succ, ih]; ring
  simp_rw [← low_step, ← high_step, tel]
  simp only [lo, hi, zero_add, pow_zero, div_one]
  linarith

end RHFilter.Dyadic

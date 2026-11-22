import Filter
import Dyadic

noncomputable section
namespace RHFilter

def M (x : ℝ) : ℝ := (pref ⌊x⌋₊ : ℤ)
def velocity (x : ℝ) := M (2*x) - 2*M x

theorem F_eq_velocity (x : ℝ) : F x = -(velocity (2*x) - 3*velocity x + 2*velocity (x/2)) := by
  rw [F_grid]
  change (RHRealGrid.grid pref ⌊4*x⌋₊ : ℝ) = _
  rw [← RHRealGrid.ordinary_eq_grid]
  unfold RHRealGrid.ordinary velocity M
  push_cast
  rw [show 2*(2*x) = 4*x by ring, show 2*(x/2) = x by ring]
  ring

theorem inverse_F_with_endpoints (x : ℝ) (m n : ℕ) :
    velocity x = F x + ∑ k ∈ Finset.range m, F (x/2^(k+1)) +
      ∑ k ∈ Finset.range n, F (2^(k+1)*x)/(2:ℝ)^(k+1) +
      (2*velocity (x/2^(m+1)) - velocity (x/2^m)) +
      (velocity (2^(n+1)*x) - velocity (2^n*x))/(2:ℝ)^n := by
  let u (k : ℕ) := velocity (2^k*x)
  let v (k : ℕ) := velocity (x/2^k)
  have hc : u 0 = v 0 := by simp [u,v]
  have mid : F x = -(u 1 - 3*u 0 + 2*v 1) := by simp [F_eq_velocity,u,v]
  have small (k : ℕ) : F (x/2^(k+1)) = -(v k - 3*v (k+1) + 2*v (k+2)) := by
    rw [F_eq_velocity]
    unfold v
    have h₁ : 2*(x/2^(k+1)) = x/2^k := by rw [pow_succ]; ring
    have h₂ : (x/2^(k+1))/2 = x/2^(k+2) := by rw [pow_succ (2:ℝ) (k+1)]; ring
    rw [h₁,h₂]
  have large (k : ℕ) : F (2^(k+1)*x) = -(u (k+2) - 3*u (k+1) + 2*u k) := by
    rw [F_eq_velocity]
    unfold u
    have h₁ : 2*(2^(k+1)*x) = 2^(k+2)*x := by rw [pow_succ (2:ℝ) (k+1)]; ring
    have h₂ : (2^(k+1)*x)/2 = 2^k*x := by rw [pow_succ]; ring
    rw [h₁,h₂]
  simp_rw [small,large]
  rw [mid]
  simpa only [u, pow_zero, one_mul, Dyadic.lo, Dyadic.hi, v] using
    Dyadic.finite_inverse u v hc m n

end RHFilter

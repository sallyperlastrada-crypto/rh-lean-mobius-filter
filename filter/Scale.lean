import Contour
import Filter
import Mathlib.NumberTheory.LSeries.Dirichlet

noncomputable section
open Complex

namespace RHFilter.Contour

def radius (y : ℝ) (j : ℕ) := y / 2^j

theorem radius_pos {y : ℝ} (hy : 0 < y) (j : ℕ) : 0 < radius y j := by
  unfold radius
  positivity

/-- The dyadic multiplier is exactly the same contour kernel at the scaled radius. -/
theorem atom_eq_base_radius (Z : ℂ → ℂ) {y : ℝ} (hy : 0 < y) (j : ℕ) (s : ℂ) :
    atom Z y j s = base Z (radius y j) s := by
  have he : (exp (-(Real.log 2 : ℂ) * s))^j * exp ((Real.log y : ℂ)*s) =
      exp ((Real.log (radius y j) : ℂ)*s) := by
    rw [← exp_nat_mul, ← exp_add, radius, Real.log_div hy.ne' (by positivity), Real.log_pow]
    congr 1
    push_cast
    ring
  unfold atom phase base
  rw [← he]
  ring

theorem floor_radius_half (N j : ℕ) :
    ⌊radius ((N:ℝ)+1/2) j⌋₊ = N / 2^j := by
  simpa only [radius, Nat.cast_pow, Nat.cast_ofNat] using RHRealGrid.half_floor_div N (2^j)

/-- All four signed prefixes use the same half-integer centre, including exact endpoints. -/
theorem grid_at_radii (N : ℕ) :
    let y := (N:ℝ)+1/2
    grid N = -pref ⌊radius y 0⌋₊ + 5*pref ⌊radius y 1⌋₊
      - 8*pref ⌊radius y 2⌋₊ + 4*pref ⌊radius y 3⌋₊ := by
  dsimp only
  simp only [floor_radius_half]
  norm_num [grid]

/-- The coefficients whose prefixes define the grid sum to 1/ζ in the Euler half-plane. -/
theorem source_hasSum_reciprocal {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n => (mu n : ℂ)) s (1 / riemannZeta s) := by
  rw [LSeriesHasSum_iff]
  refine ⟨ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs,
    (eq_div_iff (riemannZeta_ne_zero_of_one_lt_re hs)).2 ?_⟩
  rw [mul_comm]
  have h := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs] at h
  exact h

end RHFilter.Contour

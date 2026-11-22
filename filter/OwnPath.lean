import AbelEuler
import FilterConverse
import MertensTransfer

namespace RHFilter

/-- Identity for the Abel transform of the actual signed grid, in the half-plane
of absolute convergence. No estimates on F at the critical exponent enter here. -/
theorem euler_product_of_signed_grid (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s * Abel.transform s = Contour.poly (Contour.phase s) := by
  rw [Abel.transform_eq_jumpSeries hs, (Source.jumps_hasSum hs).LSeries_eq]
  field_simp [riemannZeta_ne_zero_of_one_lt_re hs]

/-- The two-sided square-root-plus-epsilon estimate on the project’s F suffices
for RH. The arithmetic estimate itself is visible in the type. -/
theorem rh_of_bilateral_filter (h : Abel.Bilateral) : RiemannHypothesis :=
  Converse.rh_of_filtered_extension (Abel.transform_analytic h) euler_product_of_signed_grid

theorem rh_via_filter_of_prefix_bounds
    (hM : ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 0 ≤ A ∧
      ∀ n : ℕ, 0 < n → |(pref n : ℝ)| ≤ A*(n:ℝ)^(1/2+ε)) : RiemannHypothesis := by
  apply rh_of_bilateral_filter
  intro ε he
  obtain ⟨A, hA, h⟩ := hM ε he
  exact ⟨18*A*(4:ℝ)^(1/2+ε), by positivity,
    fun _ hx => abs_F_sqrt_eps_of_mertens he hA h hx.le⟩

#print axioms euler_product_of_signed_grid
#print axioms rh_of_bilateral_filter
#print axioms rh_via_filter_of_prefix_bounds
#check rh_of_bilateral_filter

end RHFilter

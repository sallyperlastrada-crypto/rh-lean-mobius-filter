import EdgeAssembly
import Linear

namespace RHFilter
open Perron

/-- All remaining analytic inputs are stated on the reciprocal or on the four
individual Perron errors. The signed filter bound is the conclusion. -/
theorem minorant_from_truncation_and_growth (rh : RiemannHypothesis)
    (tr : Truncation)
    (hg : ∀ ε : ℝ, 0 < ε → ε < 1/2 → ReciprocalGrowth (1/2+ε/2) (ε/2)) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
       ∀ x : ℝ, 0 < x → -C*x^(1/2+ε) ≤ F x := by
  intro ε he
  by_cases hsmall : ε < 1/2
  · exact minorant_of_analytic_steps rh he hsmall tr
      (edges_of_reciprocal_growth rh he hsmall (hg ε he hsmall))
  · exact ⟨(5/2)*(4:ℝ)^(1/2+ε), by positivity, fun _ hx =>
      F_lower_large_epsilon (le_of_not_gt hsmall) hx⟩

end RHFilter

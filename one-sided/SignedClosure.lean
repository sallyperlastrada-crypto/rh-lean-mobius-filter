import OneSidedConverse
import Formalism.ZetaNonvanishing.LandauEq
import Formalism.ZetaNonvanishing.ZetaRealNonvanish

namespace RHFilter

/-- A one-sided estimate for the signed Möbius filter implies RH. The three
external lemmas concern positive Mellin transforms and the real axis. -/
theorem rh_of_signed_filter_minorant
    (lower : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : ℝ, 0 < x → -C*x^(1/2+ε) ≤ F x) : RiemannHypothesis :=
  OneSided.rh_of_filter_lower Formalism.landauEq
    (fun hm hp hi => Formalism.LandauMellinIdentity.imel_differentiableOn hm hp hi)
    Formalism.zetaRealNonvanish lower

/-- It suffices to prove the estimate on the inclusive integer grid from
the four signed Möbius prefixes, including every dyadic endpoint. -/
theorem rh_of_signed_grid_minorant
    (lower : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
      ∀ N : ℕ, 0 < N → -C*(N:ℝ)^(1/2+ε) ≤ (grid N : ℝ)) :
    RiemannHypothesis := by
  apply rh_of_signed_filter_minorant
  intro ε he
  obtain ⟨C, hC, bound⟩ := lower ε he
  exact ⟨C*(4:ℝ)^(1/2+ε), mul_nonneg hC (Real.rpow_nonneg (by norm_num) _),
    fun _ hx => transfer_grid_lower (by linarith : 0 < 1/2+ε) hC bound hx⟩

end RHFilter

#check @RHFilter.rh_of_signed_filter_minorant
#print axioms RHFilter.rh_of_signed_filter_minorant
#check @RHFilter.rh_of_signed_grid_minorant
#print axioms RHFilter.rh_of_signed_grid_minorant

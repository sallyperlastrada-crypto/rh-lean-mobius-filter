import RHReduction

/-! Exact API of Alpöge–Claude's arithmetic theorem, checked independently
of their proof. `verify_upstream.py` compares this definition with the pin.
The production module `ClosedRH` imports the actual proved theorem. -/
namespace RHDeposit.Interface

def DirichletLNonvanishingRightOfHalf : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

theorem apply_verified_signature : DirichletLNonvanishingRightOfHalf → RiemannHypothesis :=
  RHReduction.of_every_character

#print axioms apply_verified_signature

end RHDeposit.Interface

import Main
import RHReduction

/-!
The arithmetic input comes from Levent Alpöge's work with Claude. The public
theorem supplies nonvanishing for Dirichlet characters. RHReduction specializes
to modulus one and reflects the zeros using the functional equation. `tree`
and the Lean version are pinned in this directory.
-/

namespace RHDeposit

theorem riemannHypothesis : RiemannHypothesis :=
  RHReduction.of_every_character _root_.LFunction_ne_zero_of_half_lt_re

end RHDeposit

#print axioms RHDeposit.riemannHypothesis

import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! The input for RH is the nonvanishing of the character of modulus one in
the open right half-plane, away from the pole. Reflection uses the completed
zeta function. The exceptions where its real gamma factor vanishes are
handled before division. -/
namespace RHReduction

/-- A nontrivial zero of zeta gives a zero of its completion. -/
theorem completed_zero_of_nontrivial {s : ℂ} (hz : riemannZeta s = 0)
    (hnt : ¬ ∃ n : ℕ, s = -2 * (n + 1)) :
    completedRiemannZeta s = 0 := by
  have hs : s ≠ 0 := by
    rintro rfl
    norm_num [riemannZeta_zero] at hz
  have hg : Complex.Gammaℝ s ≠ 0 := by
    intro h
    obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp h
    cases n with
    | zero => exact hs (by simpa using hn)
    | succ k =>
      apply hnt
      exact ⟨k, by rw [hn]; push_cast; ring⟩
  exact (div_eq_zero_iff.mp ((riemannZeta_def_of_ne_zero hs).symm.trans hz)).resolve_right hg

/-- The half-plane to the left of the critical line is handled by reflection. -/
theorem of_zeta_right_nonvanishing
    (right : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0) :
    RiemannHypothesis := by
  intro s hz hnt hp
  rcases lt_trichotomy s.re (1 / 2) with hlt | heq | hgt
  · have hs0 : s ≠ 0 := by
      rintro rfl
      norm_num [riemannZeta_zero] at hz
    have h₀ : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hp)
    have h₁ : 1 - s ≠ 1 := by simpa using hs0
    have hright : 1 / 2 < (1 - s).re := by
      rw [Complex.sub_re, Complex.one_re]
      linarith
    have hmirror : riemannZeta (1 - s) = 0 := by
      rw [riemannZeta_def_of_ne_zero h₀, completedRiemannZeta_one_sub,
        completed_zero_of_nontrivial hz hnt, zero_div]
    exact False.elim (right (1 - s) hright h₁ hmirror)
  · exact heq
  · exact False.elim (right s hgt hp hz)

/-- Specialize the arithmetic input to the trivial character modulo one. -/
theorem of_conductor_one
    (right : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 →
      DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) s ≠ 0) :
    RiemannHypothesis := by
  apply of_zeta_right_nonvanishing
  simpa only [DirichletCharacter.LFunction_modOne_eq] using right

/-- The input type matches the independently audited nonvanishing theorem
for Dirichlet characters exported by the Alpöge--Claude submission. -/
theorem of_every_character
    (right : ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
      1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0) :
    RiemannHypothesis :=
  of_conductor_one (fun s hs hp => right 1 1 s hs (Or.inr hp))

end RHReduction

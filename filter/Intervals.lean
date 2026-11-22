import Parity

namespace RHFilter

/-- Möbius mass on (a,b], as a sum over its b-a integer atoms. -/
def intervalMass (a b : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (b-a), mu (a+j+1)

theorem pref_add_interval (a k : ℕ) :
    pref (a+k) = pref a + ∑ j ∈ Finset.range k, mu (a+j+1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← Nat.add_assoc, show pref (a+k+1) = pref (a+k) + mu (a+k+1)
      from prefix_succ _ _, ih, Finset.sum_range_succ, add_assoc]

theorem intervalMass_eq_diff (a b : ℕ) (hab : a ≤ b) :
    intervalMass a b = pref b - pref a := by
  have hh := pref_add_interval a (b-a)
  rw [show a+(b-a)=b by omega] at hh
  unfold intervalMass
  linarith

theorem grid_eq_intervals (N : ℕ) :
    grid N = -intervalMass (N/2) N + 4*intervalMass (N/4) (N/2)
      - 4*intervalMass (N/8) (N/4) := by
  rw [intervalMass_eq_diff _ _ (by omega), intervalMass_eq_diff _ _ (by omega),
      intervalMass_eq_diff _ _ (by omega)]
  unfold grid
  ring

theorem abs_intervalMass_le (a b : ℕ) : |intervalMass a b| ≤ ((b-a : ℕ) : ℤ) := by
  have hs (k : ℕ) : |∑ j ∈ Finset.range k, mu (a+j+1)| ≤ (k : ℤ) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ]
      exact (abs_add_le ..).trans (by
        have hm : |mu (a+k+1)| ≤ 1 := ArithmeticFunction.abs_moebius_le_one
        push_cast
        linarith)
  exact hs (b-a)

theorem abs_grid_le_budget (N : ℕ) :
    |grid N| ≤ (N : ℤ) + 3*((N/2 : ℕ) : ℤ) - 4*((N/8 : ℕ) : ℤ) := by
  rw [grid_eq_intervals, abs_le]
  have h₁ := abs_le.mp (abs_intervalMass_le (N/2) N)
  have h₂ := abs_le.mp (abs_intervalMass_le (N/4) (N/2))
  have h₃ := abs_le.mp (abs_intervalMass_le (N/8) (N/4))
  omega

theorem abs_grid_le_two_mul_add_three (N : ℕ) : |grid N| ≤ 2*(N : ℤ)+3 := by
  have hh := abs_grid_le_budget N
  omega

theorem abs_grid_le_four_mul (N : ℕ) : |grid N| ≤ 4*(N : ℤ) := by
  have hh := abs_grid_le_budget N
  omega

end RHFilter

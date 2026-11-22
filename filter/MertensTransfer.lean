import Filter

namespace RHFilter

/-- An absolute estimate on the ordinary, inclusive Möbius prefix controls
the original signed filter on its entire real grid, including endpoints. -/
theorem abs_F_of_mertens_prefix {a A : ℝ} (ha : 0 ≤ a) (hA : 0 ≤ A)
    (hM : ∀ n : ℕ, 0 < n → |(pref n : ℝ)| ≤ A * (n : ℝ) ^ a)
    {x : ℝ} (hx : 0 ≤ x) : |F x| ≤ 18 * A * (4 * x) ^ a := by
  let N := ⌊4 * x⌋₊
  let budget := A * (4 * x) ^ a
  have hbound (n : ℕ) (hn : n ≤ N) : |(pref n : ℝ)| ≤ budget := by
    by_cases hn0 : n = 0
    · subst n
      simp only [pref, partialSum, Finset.range_zero, Finset.sum_empty, Int.cast_zero, abs_zero]
      exact mul_nonneg hA (Real.rpow_nonneg (by positivity) _)
    · have hnx : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn
      have hN : (N : ℝ) ≤ 4 * x := Nat.floor_le (by positivity)
      exact (hM n (Nat.pos_of_ne_zero hn0)).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg n) (hnx.trans hN) ha) hA)
  obtain ⟨h1l, h1u⟩ := abs_le.mp (hbound N le_rfl)
  obtain ⟨h2l, h2u⟩ := abs_le.mp (hbound (N / 2) (Nat.div_le_self N 2))
  obtain ⟨h4l, h4u⟩ := abs_le.mp (hbound (N / 4) (Nat.div_le_self N 4))
  obtain ⟨h8l, h8u⟩ := abs_le.mp (hbound (N / 8) (Nat.div_le_self N 8))
  rw [F_grid]
  change |(grid N : ℝ)| ≤ _
  rw [show 18 * A * (4 * x) ^ a = 18 * budget by dsimp [budget]; ring]
  unfold grid
  push_cast
  exact abs_le.mpr ⟨by linarith only [h1u, h2l, h4u, h8l],
    by linarith only [h1l, h2u, h4l, h8u]⟩

/-- The square-root-plus-epsilon exponent survives passage from the
Möbius prefix to F, with a completely explicit loss in the constant. -/
theorem abs_F_sqrt_eps_of_mertens {ε A : ℝ} (hε : 0 < ε) (hA : 0 ≤ A)
    (hM : ∀ n : ℕ, 0 < n → |(pref n : ℝ)| ≤ A * (n : ℝ) ^ (1/2+ε))
    {x : ℝ} (hx : 0 ≤ x) :
    |F x| ≤ (18 * A * (4 : ℝ) ^ (1/2+ε)) * x ^ (1/2+ε) := by
  have h := abs_F_of_mertens_prefix (by linarith : 0 ≤ 1/2+ε) hA hM hx
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hx] at h
  linarith only [h, mul_assoc (18 * A) ((4 : ℝ) ^ (1/2+ε)) (x ^ (1/2+ε))]

end RHFilter

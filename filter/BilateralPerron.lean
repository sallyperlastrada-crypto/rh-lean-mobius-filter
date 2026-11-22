import Abel
import EdgeAssembly

namespace RHFilter
open Perron

/-- Transfer an absolute estimate at the actual grid, including its cell at zero. -/
theorem transfer_abs_grid {a C : ℝ} (ha : 0 < a) (hC : 0 ≤ C)
    (h : ∀ N : ℕ, 0 < N → |(grid N : ℝ)| ≤ C * (N : ℝ)^a)
    {x : ℝ} (hx : 0 < x) : |F x| ≤ (C * (4 : ℝ)^a) * x^a := by
  rw [F_grid]
  let N := ⌊4*x⌋₊
  change |(grid N : ℝ)| ≤ _
  by_cases hn : 0 < N
  · have hf : (N : ℝ) ≤ 4*x := Nat.floor_le (by linarith)
    have hp := Real.rpow_le_rpow (by positivity : 0 ≤ (N : ℝ)) hf ha.le
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hx.le] at hp
    calc
      _ ≤ C*(N : ℝ)^a := h N hn
      _ ≤ C * ((4 : ℝ)^a * x^a) := mul_le_mul_of_nonneg_left hp hC
      _ = _ := (mul_assoc ..).symm
  · have hz : N = 0 := Nat.eq_zero_of_not_pos hn
    rw [hz, show grid 0 = 0 by simp [grid, pref, partialSum]]
    simp only [Int.cast_zero, abs_zero]
    positivity

/-- Both signs from the three contour sides and the four individual prefix errors. -/
theorem abs_grid_of_analytic_steps (rh : RiemannHypothesis) {ε : ℝ}
    (he : 0 < ε) (hs : ε < 1/2) (tr : Truncation) (ed : EdgeEstimates ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 0 < N → |(grid N : ℝ)| ≤ C*(N : ℝ)^(1/2+ε) := by
  obtain ⟨K,hK,htr⟩ := tr
  obtain ⟨B,hB,hed⟩ := ed
  let a : ℝ := 1/2+ε
  have ha : 0 < a := by dsimp [a]; linarith
  let D := 18*K/a+3*B
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let C := max 40 (D * (2 : ℝ)^a)
  have h40 : 40 ≤ C := le_max_left _ _
  refine ⟨C, by linarith, ?_⟩
  intro N hn
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast hn
  have hPow := Real.one_le_rpow hN ha.le
  change _ ≤ C*(N : ℝ)^a
  by_cases hlarge : 16 ≤ N
  · have hb : (1/2 : ℝ) < 1/2+ε/2 := by linarith
    have hbc : 1/2+ε/2 ≤ rightEdge N := by linarith [right_gt_one N hlarge]
    obtain ⟨hv,hl,hu⟩ := hed N hlarge
    have h := local_budget rh N hlarge _ _ _ _ _ hb hbc (htr N hlarge) hv hl hu
    have hy : 0 ≤ cutoff N := by unfold cutoff; positivity
    have hlog := mul_le_mul_of_nonneg_left (Real.log_le_rpow_div hy ha) hK
    have hp := Real.rpow_le_rpow hy (show cutoff N ≤ 2*(N:ℝ) by unfold cutoff; linarith) ha.le
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by positivity)] at hp
    calc
      _ ≤ 18*(K*Real.log (cutoff N)) + 3*(B*cutoff N^a) := by linarith only [h]
      _ ≤ 18*(K*(cutoff N^a/a)) + 3*(B*cutoff N^a) := by linarith
      _ = D*cutoff N^a := by dsimp [D]; ring
      _ ≤ D*((2:ℝ)^a*(N:ℝ)^a) := mul_le_mul_of_nonneg_left hp hD
      _ = (D*(2:ℝ)^a)*(N:ℝ)^a := (mul_assoc ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  · have hsmall : (N:ℝ) ≤ 16 := by exact_mod_cast (show N ≤ 16 by omega)
    calc
      _ ≤ (5/2)*(N:ℝ) := abs_grid_le_five_halves N
      _ ≤ 40 := by linarith
      _ ≤ C := h40
      _ ≤ _ := le_mul_of_one_le_right (by linarith) hPow

/-- Forward implication in the bilateral form used by Abel continuation. -/
theorem bilateral_from_truncation_and_growth (rh : RiemannHypothesis) (tr : Truncation)
    (growth : ∀ ε : ℝ, 0 < ε → ε < 1/2 → ReciprocalGrowth (1/2+ε/2) (ε/2)) :
    Abel.Bilateral := by
  intro ε he
  have ha : 0 < 1/2+ε := by linarith
  by_cases hs : ε < 1/2
  · obtain ⟨C,hC,hgrid⟩ := abs_grid_of_analytic_steps rh he hs tr
      (edges_of_reciprocal_growth rh he hs (growth ε he hs))
    exact ⟨C*(4:ℝ)^(1/2+ε), by positivity, fun _ hx => transfer_abs_grid ha hC hgrid hx⟩
  · refine ⟨(5/2)*(4:ℝ)^(1/2+ε), by positivity, fun x hx => transfer_abs_grid ha (by norm_num) ?_ hx⟩
    intro N hn
    have hn' : (1:ℝ) ≤ N := by exact_mod_cast hn
    have hp := Real.rpow_le_rpow_of_exponent_le hn' (by linarith : (1:ℝ) ≤ 1/2+ε)
    rw [Real.rpow_one] at hp
    exact (abs_grid_le_five_halves N).trans (mul_le_mul_of_nonneg_left hp (by norm_num))

end RHFilter

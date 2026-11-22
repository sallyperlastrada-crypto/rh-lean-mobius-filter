import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace RHRealGrid

/-- Discrete four-scale filter on an inclusive counting function. -/
def grid (P : ℕ → ℤ) (N : ℕ) : ℤ :=
  -P N + 5 * P (N/2) - 8 * P (N/4) + 4 * P (N/8)

noncomputable def ordinary (P : ℕ → ℤ) (x : ℝ) : ℤ :=
  -P ⌊4*x⌋₊ + 5 * P ⌊2*x⌋₊ - 8 * P ⌊x⌋₊ + 4 * P ⌊x/2⌋₊

noncomputable def oddSource (Q : ℕ → ℤ) (x : ℝ) : ℤ :=
  -Q ⌊4*x⌋₊ + 6 * Q ⌊2*x⌋₊ - 13 * Q ⌊x⌋₊ + 12 * Q ⌊x/2⌋₊ - 4 * Q ⌊x/4⌋₊

/-- Weighted counts over (x/4,x/2], (x/2,x], (x,2x], (2x,4x]. -/
noncomputable def bands (Q : ℕ → ℤ) (x : ℝ) : ℤ :=
  4 * (Q ⌊x/2⌋₊ - Q ⌊x/4⌋₊) - 8 * (Q ⌊x⌋₊ - Q ⌊x/2⌋₊) +
  5 * (Q ⌊2*x⌋₊ - Q ⌊x⌋₊) - (Q ⌊4*x⌋₊ - Q ⌊2*x⌋₊)

theorem bands_eq_oddSource (Q : ℕ → ℤ) (x : ℝ) :
    bands Q x = oddSource Q x := by unfold bands oddSource; ring

private theorem floors (x : ℝ) :
    ⌊2*x⌋₊ = ⌊4*x⌋₊/2 ∧ ⌊x⌋₊ = ⌊4*x⌋₊/4 ∧
    ⌊x/2⌋₊ = ⌊4*x⌋₊/8 ∧ ⌊x/4⌋₊ = ⌊4*x⌋₊/16 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Nat.floor_div_ofNat (4*x) 2, show 4*x/2 = 2*x by ring]
  · rw [← Nat.floor_div_ofNat (4*x) 4, show 4*x/4 = x by ring]
  · rw [← Nat.floor_div_ofNat (4*x) 8, show 4*x/8 = x/2 by ring]
  · rw [← Nat.floor_div_ofNat (4*x) 16, show 4*x/16 = x/4 by ring]

theorem ordinary_eq_grid (P : ℕ → ℤ) (x : ℝ) : ordinary P x = grid P ⌊4*x⌋₊ := by
  obtain ⟨a,b,c,-⟩ := floors x
  simp only [ordinary, grid, a, b, c]

theorem oddSource_eq_grid (P Q : ℕ → ℤ)
    (h : ∀ N, P N = Q N - Q (N/2)) (x : ℝ) :
    oddSource Q x = grid P ⌊4*x⌋₊ := by
  obtain ⟨a,b,c,d⟩ := floors x
  simp only [oddSource, grid, a, b, c, d, h, Nat.div_div_eq_div_mul]
  norm_num
  ring

/-- The left endpoint belongs to the cell, the right endpoint belongs to the next. -/
theorem cell_iff {x : ℝ} (hx : 0 ≤ x) (N : ℕ) :
    ⌊4*x⌋₊ = N ↔ (N:ℝ)/4 ≤ x ∧ x < ((N:ℝ)+1)/4 := by
  rw [Nat.floor_eq_iff (by linarith : 0 ≤ 4*x)]
  constructor <;> intro ⟨a,b⟩ <;> constructor <;> linarith

theorem oddSource_on_cell (P Q : ℕ → ℤ)
    (h : ∀ N, P N = Q N - Q (N/2)) (N : ℕ) {x : ℝ}
    (hlo : (N:ℝ)/4 ≤ x) (hhi : x < ((N:ℝ)+1)/4) :
    oddSource Q x = grid P N := by
  have hx : 0 ≤ x := by have := Nat.cast_nonneg (α := ℝ) N; linarith
  rw [oddSource_eq_grid P Q h x, (cell_iff hx N).2 ⟨hlo,hhi⟩]

theorem oddSource_endpoint (P Q : ℕ → ℤ)
    (h : ∀ N, P N = Q N - Q (N/2)) (N : ℕ) :
    oddSource Q ((N:ℝ)/4) = grid P N :=
  oddSource_on_cell P Q h N le_rfl (by linarith)

/-- The half-integer convention evaluates the inclusive prefix at exactly N/q. -/
theorem half_floor_div (N q : ℕ) :
    ⌊((N:ℝ) + 1/2)/(q:ℝ)⌋₊ = N/q := by
  rw [Nat.floor_div_natCast]
  have ha : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg _
  have hf : ⌊(N:ℝ)+1/2⌋₊ = N :=
    (Nat.floor_eq_iff (by linarith)).2 ⟨by linarith, by linarith⟩
  rw [hf]

/-- The distance from a scaled half-integer to any integer has an explicit gap. -/
theorem half_distance_lower (N q : ℕ) (hq : 0 < q) (k : ℤ) :
    1 / (2 * (q:ℝ)) ≤ |((N:ℝ) + 1/2)/(q:ℝ) - (k:ℝ)| := by
  have hq' : 0 < (q:ℝ) := by exact_mod_cast hq
  by_cases h : (q:ℤ) * k ≤ (N:ℤ)
  · have hk : (q:ℝ) * (k:ℝ) ≤ (N:ℝ) := by exact_mod_cast h
    apply le_trans _ (le_abs_self _)
    rw [le_sub_iff_add_le, ← mul_le_mul_iff_of_pos_right hq', div_mul_cancel₀ _ hq'.ne']
    have hi : (1 / (2 * (q:ℝ))) * (q:ℝ) = 1/2 := by
      rw [div_mul_eq_div_div, div_mul_cancel₀ _ hq'.ne']
    rw [add_mul, hi, mul_comm (k:ℝ)]
    linarith
  · have h' : (N:ℤ)+1 ≤ (q:ℤ)*k := by omega
    have hk : (N:ℝ)+1 ≤ (q:ℝ)*(k:ℝ) := by exact_mod_cast h'
    apply le_trans _ (neg_le_abs _)
    rw [neg_sub, le_sub_iff_add_le, ← mul_le_mul_iff_of_pos_right hq', add_mul,
      div_mul_cancel₀ _ hq'.ne']
    have hi : (1 / (2 * (q:ℝ))) * (q:ℝ) = 1/2 := by
      rw [div_mul_eq_div_div, div_mul_cancel₀ _ hq'.ne']
    rw [hi, mul_comm (k:ℝ)]
    linarith

end RHRealGrid

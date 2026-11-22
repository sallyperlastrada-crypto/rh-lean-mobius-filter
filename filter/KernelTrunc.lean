import Grid
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

namespace RHFilter.Trunc

private theorem harmonic_log (H : ℕ) :
    ∑ i ∈ Finset.range H, (1:ℝ)/((i:ℝ)+1) ≤ 1 + Real.log (H+1) := by
  have hsharp (n : ℕ) :
      ∑ i ∈ Finset.range (n+1), (1:ℝ)/((i:ℝ)+1) ≤ 1 + Real.log ((n:ℝ)+1) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hp : 0 < (n:ℝ)+1 := by positivity
      have hq : 0 < (n:ℝ)+2 := by positivity
      have h := Real.one_sub_inv_le_log_of_pos (div_pos hq hp)
      rw [Real.log_div hq.ne' hp.ne', inv_div] at h
      have he : 1 - ((n:ℝ)+1)/((n:ℝ)+2) = 1/((n:ℝ)+2) := by field_simp; ring
      rw [he] at h
      rw [Finset.sum_range_succ, Nat.cast_succ, show (n:ℝ)+1+1 = n+2 by ring]
      linarith
  cases H with
  | zero => simp
  | succ n =>
    apply le_trans (hsharp n)
    exact add_le_add_right (Real.log_le_log (by positivity) (by push_cast; linarith)) _

private def leftPt (k : ℤ) (i : ℕ) : ℤ := k-i
private def rightPt (k : ℤ) (i : ℕ) : ℤ := k+1+i

/-- Every finite subset of a window of radii H+1. The two central atoms each
cost at most b, while each later pair costs at most 2/i. -/
theorem window_log (S : Finset ℤ) (k : ℤ) (H : ℕ) {r b : ℝ}
    (hk : (k:ℝ) ≤ r) (hk' : r ≤ (k:ℝ)+1)
    (h0 : 1/|r-(k:ℝ)| ≤ b) (h1 : 1/|r-((k:ℝ)+1)| ≤ b)
    (hs : ∀ n ∈ S, k-(H:ℤ) ≤ n ∧ n ≤ k+1+(H:ℤ)) :
    ∑ n ∈ S, 1/|r-(n:ℝ)| ≤ 2*b + 2*(1 + Real.log (H+1)) := by
  let I := Finset.range (H+1)
  let L := I.image (leftPt k)
  let R := I.image (rightPt k)
  let cost (z : ℤ) := 1/|r-(z:ℝ)|
  have hsub : S ⊆ L ∪ R := by
    intro z hz
    obtain ⟨za,zb⟩ := hs z hz
    by_cases zle : z ≤ k
    · apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      exact ⟨(k-z).toNat, Finset.mem_range.mpr (by omega), by unfold leftPt; omega⟩
    · apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      exact ⟨(z-k-1).toNat, Finset.mem_range.mpr (by omega), by unfold rightPt; omega⟩
  have hd : Disjoint L R := by
    apply Finset.disjoint_left.mpr
    intro z hz1 hz2
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hz1
    obtain ⟨j,_,e⟩ := Finset.mem_image.mp hz2
    unfold leftPt rightPt at e
    omega
  have li : Function.Injective (leftPt k) := by intro a b e; unfold leftPt at e; omega
  have ri : Function.Injective (rightPt k) := by intro a b e; unfold rightPt at e; omega
  have bound (i : ℕ) : cost (leftPt k (i+1)) + cost (rightPt k (i+1))
      ≤ 2 * (1/((i:ℝ)+1)) := by
    have hp : 0 < (i:ℝ)+1 := by positivity
    have hl : (i:ℝ)+1 ≤ r - (↑(leftPt k (i+1)):ℝ) := by
      unfold leftPt
      push_cast
      linarith
    have hr : (i:ℝ)+1 ≤ (↑(rightPt k (i+1)):ℝ) - r := by
      unfold rightPt
      push_cast
      linarith
    unfold cost
    rw [abs_of_nonneg (by linarith : 0 ≤ r-↑(leftPt k (i+1))),
      abs_sub_comm r (↑(rightPt k (i+1)):ℝ), abs_of_nonneg (by linarith)]
    linarith [one_div_le_one_div_of_le hp hl, one_div_le_one_div_of_le hp hr]
  have hsum := Finset.sum_le_sum (s := Finset.range H) (fun i _ => bound i)
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at hsum
  have central : cost (leftPt k 0) + cost (rightPt k 0) ≤ 2*b := by
    simp [cost, leftPt, rightPt]
    simp only [one_div] at h0 h1
    linarith
  calc
    _ ≤ ∑ n ∈ L ∪ R, cost n := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro n _ _
      positivity
    _ = (∑ i ∈ I, cost (leftPt k i)) + ∑ i ∈ I, cost (rightPt k i) := by
      rw [Finset.sum_union hd, show L = I.image (leftPt k) by rfl,
        show R = I.image (rightPt k) by rfl, Finset.sum_image li.injOn, Finset.sum_image ri.injOn]
    _ ≤ _ := by
      dsimp only [I]
      rw [Finset.sum_range_succ', Finset.sum_range_succ']
      linarith [harmonic_log H]

/-- The near part of each Perron cutoff for q = 1,2,4,8. Only the error
majorant is estimated absolutely. N is the original grid index. -/
theorem near_half_log (N q : ℕ) (hq : 0 < q) (hq8 : q ≤ 8)
    (S : Finset ℤ) (hS : ∀ n ∈ S,
      (((N:ℝ)+1/2)/(q:ℝ))/2 < (n:ℝ) ∧ (n:ℝ) < 2*(((N:ℝ)+1/2)/(q:ℝ))) :
    ∑ n ∈ S, 1 / |((N:ℝ)+1/2)/(q:ℝ) - (n:ℝ)|
      ≤ 34 + 2*Real.log ((N:ℝ)+2) := by
  let r : ℝ := ((N:ℝ)+1/2)/(q:ℝ)
  let k : ℤ := ⌊r⌋
  have kr : (k:ℝ) ≤ r := Int.floor_le _
  have rk : r < (k:ℝ)+1 := Int.lt_floor_add_one _
  have hqp : (0:ℝ) < q := by exact_mod_cast hq
  have hq1 : 1 ≤ (q:ℝ) := by exact_mod_cast hq
  have hn : (0:ℝ) ≤ N := Nat.cast_nonneg _
  have hrp : 0 ≤ r := by dsimp [r]; positivity
  have hrN : r ≤ (N:ℝ)+1 := by
    dsimp [r]
    rw [div_le_iff₀ hqp]
    nlinarith
  have hdist (z : ℤ) : 1 / |r-(z:ℝ)| ≤ 16 := by
    have hgap := RHRealGrid.half_distance_lower N q hq z
    change 1/(2*(q:ℝ)) ≤ |r-(z:ℝ)| at hgap
    have hlow : (0:ℝ) < 1/(2*(q:ℝ)) := by positivity
    have h := one_div_le_one_div_of_le hlow hgap
    simp only [one_div, inv_inv] at h
    have h8 : (q:ℝ) ≤ 8 := by exact_mod_cast hq8
    simpa only [one_div] using (show |r-(z:ℝ)|⁻¹ ≤ 16 by linarith)
  have hwin (n : ℤ) (hnS : n ∈ S) :
      k-((N+1:ℕ):ℤ) ≤ n ∧ n ≤ k+1+((N+1:ℕ):ℤ) := by
    obtain ⟨lo,hi⟩ := hS n hnS
    change r/2 < (n:ℝ) at lo
    change (n:ℝ) < 2*r at hi
    constructor
    · have e : (k:ℝ)-((N:ℝ)+1) ≤ (n:ℝ) := by linarith
      exact_mod_cast e
    · have e : (n:ℝ) ≤ (k:ℝ)+1+((N:ℝ)+1) := by linarith
      exact_mod_cast e
  have hright : 1/|r-((k:ℝ)+1)| ≤ 16 := by simpa using hdist (k+1)
  have h := window_log S k (N+1) kr rk.le (hdist k) hright hwin
  change ∑ n ∈ S, 1/|r-(n:ℝ)| ≤ _
  rw [Nat.cast_succ, show (N:ℝ)+1+1 = N+2 by ring] at h
  linarith

end RHFilter.Trunc

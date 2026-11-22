import Scale
import Mathlib.NumberTheory.LSeries.Linearity

noncomputable section
open Complex

namespace RHFilter.Source

def muC (n : ℕ) : ℂ := mu n

/-- Put the original sequence at multiples of the dilation; keep its sign. -/
def atMultiples (d n : ℕ) : ℂ := if d ∣ n then muC (n / d) else 0

theorem dilated_hasSum (d : ℕ) (hd : 0 < d) {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (atMultiples d) s ((d : ℂ) ^ (-s) * (1 / riemannZeta s)) := by
  have inj : Function.Injective (fun n : ℕ => d*n) := fun _ _ h => Nat.eq_of_mul_eq_mul_left hd h
  change HasSum (LSeries.term (atMultiples d) s) _
  apply (inj.hasSum_iff ?_).mp
  · have h : HasSum (LSeries.term muC s) (1 / riemannZeta s) := Contour.source_hasSum_reciprocal hs
    apply (h.mul_left ((d : ℂ)^(-s))).congr_fun
    intro n
    by_cases hn : n = 0
    · subst n
      simp [LSeries.term]
    · have hdn : d*n ≠ 0 := Nat.mul_ne_zero hd.ne' hn
      simp only [Function.comp_apply, LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hdn,
        atMultiples, dvd_mul_right, ite_true, Nat.mul_div_cancel_left _ hd,
        Nat.cast_mul, natCast_mul_natCast_cpow, cpow_neg]
      ring
  · intro n hnot
    have hn : ¬ d ∣ n := by rintro ⟨k,rfl⟩; exact hnot ⟨k,rfl⟩
    simp [LSeries.term, atMultiples, hn]

def jumps : ℕ → ℂ := -muC + (5:ℂ) • atMultiples 2 - (8:ℂ) • atMultiples 4 + (4:ℂ) • atMultiples 8

theorem jumps_eq (n : ℕ) (hn : 0 < n) : jumps n = ((grid n - grid (n-1) : ℤ) : ℂ) := by
  rw [grid_jump n hn]
  simp only [jumps, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul,
    atMultiples, muC]
  push_cast
  split_ifs <;> norm_num

private theorem dyadic_power (s : ℂ) (j : ℕ) :
    ((2^j : ℕ) : ℂ)^(-s) = (Contour.phase s)^j := by
  rw [cpow_def_of_ne_zero (by exact_mod_cast (pow_ne_zero j (by decide : (2:ℕ) ≠ 0)))]
  rw [Contour.phase, ← exp_nat_mul]
  congr 1
  have hlog : Complex.log ((2^j : ℕ) : ℂ) = (j : ℂ) * (Real.log 2 : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (by positivity)]
    norm_cast
    simp [Real.log_pow]
  rw [hlog]
  ring

theorem jumps_hasSum {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum jumps s (Contour.poly (Contour.phase s) * (1 / riemannZeta s)) := by
  have h : LSeriesHasSum muC s (1 / riemannZeta s) := Contour.source_hasSum_reciprocal hs
  have h2 := dilated_hasSum (2^1) (by decide) hs
  have h4 := dilated_hasSum (2^2) (by decide) hs
  have h8 := dilated_hasSum (2^3) (by decide) hs
  rw [dyadic_power, pow_one] at h2
  rw [dyadic_power] at h4 h8
  convert (((h.neg.add (h2.smul 5)).sub (h4.smul 8)).add (h8.smul 4)) using 1 <;>
    first | rfl | (unfold Contour.poly; ring)

end RHFilter.Source

import Majorant
import Perron
import Mathlib.Analysis.Complex.ExponentialBounds

noncomputable section
open Complex

namespace RHFilter.Perron
open Contour External Majorant

/-- A growth statement about the reciprocal alone, on a fixed closed half-plane. -/
def ReciprocalGrowth (b η : ℝ) : Prop := ∃ C : ℝ, 0 ≤ C ∧
  ∀ s : ℂ, b ≤ s.re → ‖reciprocal s‖ ≤ C * (max 1 |s.im|)^η

private theorem scaled_part_le {z : ℂ} {u : ℝ} (hu : |u| ≤ ‖z‖) :
    |u / (2*Real.pi)| ≤ ‖z‖ := by
  rw [abs_div, abs_of_pos (by positivity : 0 < 2*Real.pi)]
  exact (div_le_self (abs_nonneg u) (by linarith [Real.two_le_pi])).trans hu

private theorem on_line (rh : RiemannHypothesis) (y b : ℝ) (hb : 1/2 < b) :
    Continuous (fun t : ℝ => kernel reciprocal y (b+t*I)) := by
  rw [continuous_iff_continuousAt]
  intro t
  let s : ℂ := b+t*I
  have hr : 1/2 < s.re := by simpa [s] using hb
  have hn : s ≠ 0 := by intro h; simp [h] at hr; linarith
  have hd := kernel_diff reciprocal y ((reciprocal_holomorphic rh) s hr).differentiableAt hn
  have ht : ContinuousAt (fun u : ℝ => (b:ℂ)+(u:ℂ)*I) t := by fun_prop
  exact ContinuousAt.comp (f := fun u : ℝ => (b:ℂ)+(u:ℂ)*I) (x := t) hd.continuousAt ht

theorem edges_of_reciprocal_growth (rh : RiemannHypothesis) {ε : ℝ}
    (hε : 0 < ε) (hε' : ε < 1/2)
    (hg : ReciprocalGrowth (1/2+ε/2) (ε/2)) : EdgeEstimates ε := by
  let η := ε/2
  let b := 1/2+ε/2
  let a := 1/2+ε
  have hη : 0 < η := by dsimp [η]; linarith
  have hbh : 1/2 < b := by dsimp [b]; linarith
  have hb : 0 < b := by linarith
  have hba : b ≤ a := by dsimp [b,a]; linarith
  have hsum : b+η = a := by dsimp [b,η,a]; ring
  obtain ⟨C,hC,hg⟩ := hg
  let K := 36*C/b + 36*C/η + 36*Real.exp 1*C
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro N hN
  let y := cutoff N
  let c := rightEdge N
  change |V N b| ≤ K*y^a ∧ |H N b (-y)| ≤ K*y^a ∧ |H N b y| ≤ K*y^a
  have hn : (16:ℝ) ≤ N := by exact_mod_cast hN
  have hy : 1 < y := by dsimp [y,cutoff]; linarith
  have hy0 : 0 < y := by linarith
  have hlog : 1 ≤ Real.log y := by
    rw [← Real.exp_le_exp, Real.exp_log hy0]
    dsimp [y,cutoff]
    linarith [Real.exp_one_lt_three]
  have hbc : b ≤ c := by dsimp [b,c]; linarith [right_gt_one N hN]
  have hc2 : c ≤ 2 := by
    have hdiv : 1/Real.log y ≤ 1 := by
      apply (div_le_iff₀ (by linarith : 0 < Real.log y)).2
      linarith
    change 1+1/Real.log y ≤ 2
    linarith
  have hright : y^c = y * Real.exp 1 := by
    rw [Real.rpow_def_of_pos hy0]
    change Real.exp (Real.log y*(1+1/Real.log y)) = _
    rw [mul_add, mul_one, mul_one_div_cancel (by linarith : Real.log y ≠ 0),
      Real.exp_add, Real.exp_log hy0]
  have hl (u t : ℝ) (hu : b ≤ u) :
      ‖reciprocal (u+t*I)‖ ≤ C * (max 1 |t|)^η := by
    simpa using hg ((u:ℂ)+t*I) (by simpa [b] using hu)
  have hV := vertical_full_le reciprocal hy0 hb hη hy.le (on_line rh y b hbh)
    (B := C) (C := C) (by
      intro t ht
      simpa [max_eq_left (abs_le.mpr ht)] using hl b t le_rfl)
    (by
      intro t h1 _
      simpa [max_eq_right h1] using hl b t le_rfl)
  have hx : |V N b| ≤ ‖vert (kernel reciprocal y) b (-y) y‖ :=
    scaled_part_le (Complex.abs_re_le_norm _)
  have hyp := Real.rpow_le_rpow_of_exponent_le hy.le hba
  have hyη := Real.rpow_nonneg hy0.le η
  have hya := Real.rpow_nonneg hy0.le a
  have hyb := Real.rpow_nonneg hy0.le b
  have hprod : y^b*y^η = y^a := by rw [←Real.rpow_add hy0, hsum]
  have hV' : |V N b| ≤ K*y^a := by
    calc
      _ ≤ (18*y^b*C/b)*2 + 2*(18*y^b*C)*((y^η-1)/η) := hx.trans hV
      _ ≤ (36*C/b)*y^b + (36*C/η)*(y^b*y^η) := by
        have hpos : 0 ≤ 36*C*y^b/η := by positivity
        linarith only [hpos, show (18*y^b*C/b)*2 + 2*(18*y^b*C)*((y^η-1)/η)
          = (36*C/b)*y^b + (36*C/η)*(y^b*y^η) - 36*C*y^b/η by ring]
      _ ≤ (36*C/b)*y^a + (36*C/η)*y^a := by
        rw [hprod]
        gcongr
      _ ≤ K*y^a := by
        dsimp [K]
        rw [add_mul, add_mul]
        linarith [show 0 ≤ 36*Real.exp 1*C*y^a by positivity]
  have horizBound (t : ℝ) (ht : |t| = y) : |H N b t| ≤ K*y^a := by
    have ht' := abs_pos.mp (ht.symm ▸ hy0)
    have hh := horizontal_le reciprocal (y := y) hy.le hb.le hbc ht' (B := C*y^η) (by
      intro u hu
      simpa [ht, max_eq_right hy.le] using hl u t hu.1)
    have hh' : |H N b t| ≤ ‖horiz (kernel reciprocal y) t b c‖ :=
      scaled_part_le (Complex.abs_im_le_norm _)
    have hw : |c-b| ≤ 2 := by rw [abs_of_nonneg (sub_nonneg.mpr hbc)]; linarith
    have hηa : η ≤ a := by dsimp [η,a]; linarith
    have hp := Real.rpow_le_rpow_of_exponent_le hy.le hηa
    calc
      _ ≤ (18*y^c*(C*y^η)/|t|) * |c-b| := hh'.trans hh
      _ = (18*Real.exp 1*C*y^η) * |c-b| := by
        rw [ht,hright]
        congr 1
        apply (div_eq_iff hy0.ne').2
        ring
      _ ≤ (18*Real.exp 1*C*y^η)*2 := mul_le_mul_of_nonneg_left hw (by positivity)
      _ = (36*Real.exp 1*C)*y^η := by ring
      _ ≤ (36*Real.exp 1*C)*y^a := mul_le_mul_of_nonneg_left hp (by positivity)
      _ ≤ K*y^a := by
        apply mul_le_mul_of_nonneg_right _ hya
        dsimp [K]; linarith [show 0 ≤ 36*C/b by positivity, show 0 ≤ 36*C/η by positivity]
  exact ⟨hV', horizBound (-y) (by rw [abs_neg, abs_of_pos hy0]), horizBound y (abs_of_pos hy0)⟩

end RHFilter.Perron

import Filter
import Intervals
import Contour
import ExternalZF
import Mathlib.NumberTheory.LSeries.Dirichlet

noncomputable section
namespace RHFilter.Perron
open Complex Contour External

def cutoff (N : ℕ) : ℝ := N + 1/2
def rightEdge (N : ℕ) : ℝ := 1 + 1 / Real.log (cutoff N)
def A (N j : ℕ) : ℝ := read (vert (atom reciprocal (cutoff N) j)
  (rightEdge N) (-(cutoff N)) (cutoff N))
def V (N : ℕ) (b : ℝ) : ℝ := read (vert (kernel reciprocal (cutoff N)) b (-(cutoff N)) (cutoff N))
def H (N : ℕ) (b t : ℝ) : ℝ :=
  (horiz (kernel reciprocal (cutoff N)) t b (rightEdge N)).im / (2*Real.pi)

theorem right_gt_one (N : ℕ) (hn : 16 ≤ N) : 1 < rightEdge N := by
  have hN : (16:ℝ) ≤ N := by exact_mod_cast hn
  have h : 1 < cutoff N := by unfold cutoff; linarith
  unfold rightEdge
  linarith [one_div_pos.mpr (Real.log_pos h)]

theorem atom_integrable (N j : ℕ) (hn : 16 ≤ N) :
    IntervalIntegrable (fun t : ℝ => atom reciprocal (cutoff N) j (rightEdge N+t*I))
       MeasureTheory.volume (-(cutoff N)) (cutoff N) := by
  apply Continuous.intervalIntegrable
  rw [continuous_iff_continuousAt]
  intro t
  let s : ℂ := rightEdge N + t*I
  have hre : s.re = rightEdge N := by simp [s]
  have hsr : 1/2 < s.re := by rw [hre]; linarith [right_gt_one N hn]
  have heuler : 1 < s.re := by rw [hre]; exact right_gt_one N hn
  have hs1 : s ≠ 1 := by intro h; simp [h] at heuler
  have hd := (differentiableAt_riemannZeta hs1).inv (riemannZeta_ne_zero_of_one_lt_re heuler)
  have hz : DifferentiableAt ℂ reciprocal s := by
    apply hd.congr_of_eventuallyEq
    filter_upwards [isOpen_compl_singleton.mem_nhds hs1] with z hz
    simp [reciprocal, show z ≠ 1 from hz]
  have hs : s ≠ 0 := by intro h; simp [h] at hsr; linarith
  have hA : DifferentiableAt ℂ (atom reciprocal (cutoff N) j) s := by
    unfold atom phase base
    fun_prop (disch := assumption)
  have ht : ContinuousAt (fun u : ℝ => (rightEdge N : ℂ) + (u:ℂ)*I) t := by fun_prop
  exact ContinuousAt.comp (f := fun u : ℝ => (rightEdge N : ℂ) + (u:ℂ)*I)
    (x := t) hA.continuousAt ht

/-- The two horizontal edges occur with opposite orientations. -/
theorem signed_shift (rh : RiemannHypothesis) (N : ℕ) (hn : 16 ≤ N)
    (b : ℝ) (hb : 1/2 < b) (hbc : b ≤ rightEdge N) :
    -A N 0 + 5*A N 1 - 8*A N 2 + 4*A N 3 =
      V N b + H N b (cutoff N) - H N b (-(cutoff N)) := by
  have hR := rectangle reciprocal (cutoff N) b (rightEdge N) (-(cutoff N)) (cutoff N) hb hbc
    (fun s hs => ((reciprocal_holomorphic rh) s hs).differentiableAt)
  rw [signed_vert _ _ _ _ _ (fun j => atom_integrable N j hn)] at hR
  have h := congrArg Complex.im hR
  simp only [Complex.sub_im, Complex.add_im, Complex.I_mul_im, Complex.zero_im] at h
  simp [Complex.mul_re] at h
  unfold A V H Contour.read
  linear_combination h / (2*Real.pi)

/-- Truncation errors are four individual prefix errors. The sides concern
the actual three integrals of the complete polynomial. There is no estimate of F in the inputs. -/
theorem local_budget (rh : RiemannHypothesis) (N : ℕ) (hn : 16 ≤ N)
    (b E B L U : ℝ) (hb : 1/2 < b) (hbc : b ≤ rightEdge N)
    (herr : ∀ j : Fin 4, |(pref (N/2^j.val) : ℝ) - A N j.val| ≤ E)
    (hv : |V N b| ≤ B) (hl : |H N b (-(cutoff N))| ≤ L) (hu : |H N b (cutoff N)| ≤ U) :
    |(grid N : ℝ)| ≤ 18*E + B + L + U := by
  have s := signed_shift rh N hn b hb hbc
  have e0 := abs_le.mp (herr 0)
  have e1 := abs_le.mp (herr 1)
  have e2 := abs_le.mp (herr 2)
  have e3 := abs_le.mp (herr 3)
  norm_num at e0 e1 e2 e3
  obtain ⟨v₁,v₂⟩ := abs_le.mp hv
  obtain ⟨l₁,l₂⟩ := abs_le.mp hl
  obtain ⟨u₁,u₂⟩ := abs_le.mp hu
  unfold grid
  push_cast
  rw [abs_le]
  constructor <;> linarith [e0.1,e0.2,e1.1,e1.2,e2.1,e2.2,e3.1,e3.2]

/-- Distinct analytic obligations. Both are propositions, with no new axioms. -/
def Truncation : Prop := ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 16 ≤ N → ∀ j : Fin 4,
    |(pref (N/2^j.val) : ℝ) - A N j.val| ≤ K*Real.log (cutoff N)

def EdgeEstimates (ε : ℝ) : Prop := ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 16 ≤ N →
    let b := 1/2 + ε/2
    let budget := B * cutoff N ^ (1/2+ε)
    |V N b| ≤ budget ∧ |H N b (-(cutoff N))| ≤ budget ∧ |H N b (cutoff N)| ≤ budget

theorem minorant_of_analytic_steps (rh : RiemannHypothesis) {ε : ℝ}
    (he : 0 < ε) (he' : ε < 1/2) (tr : Truncation) (edges : EdgeEstimates ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → -C*x^(1/2+ε) ≤ F x := by
  obtain ⟨K,hK,htr⟩ := tr
  obtain ⟨B,hB,hed⟩ := edges
  let a : ℝ := 1/2+ε
  have ha : 0 < a := by dsimp [a]; linarith
  let D : ℝ := 18*K/a+3*B
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let C : ℝ := 64+D*(2:ℝ)^a
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C*4^a, by positivity, fun x hx => transfer_grid_lower ha hC ?_ hx⟩
  intro N hpos
  have hN : (1:ℝ) ≤ N := by exact_mod_cast hpos
  have hpow := Real.one_le_rpow hN ha.le
  by_cases hn : 16 ≤ N
  · have hb : (1/2:ℝ) < 1/2+ε/2 := by linarith
    have hbc : 1/2+ε/2 ≤ rightEdge N := by linarith [right_gt_one N hn]
    obtain ⟨hv,hl,hu⟩ := hed N hn
    have h := local_budget rh N hn _ _ _ _ _ hb hbc (htr N hn) hv hl hu
    have hy : 0 ≤ cutoff N := by unfold cutoff; positivity
    have hlog := Real.log_le_rpow_div hy ha
    have hlog' := mul_le_mul_of_nonneg_left hlog hK
    have hcost : |(grid N : ℝ)| ≤ D*cutoff N^a := by
      dsimp only [D]
      calc
        _ ≤ 18*(K*Real.log (cutoff N))+3*(B*cutoff N^a) := by linarith only [h]
        _ ≤ 18*(K*(cutoff N^a/a))+3*(B*cutoff N^a) := by linarith
        _ = _ := by ring
    have hcomp := Real.rpow_le_rpow hy (show cutoff N ≤ 2*(N:ℝ) by unfold cutoff; linarith) ha.le
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by positivity)] at hcomp
    have ht := mul_le_mul_of_nonneg_left hcomp hD
    have hnneg : 0 ≤ (N:ℝ)^a := by positivity
    dsimp only [C]
    linarith [ (abs_le.mp hcost).1, mul_assoc D ((2:ℝ)^a) ((N:ℝ)^a),
               add_mul (64:ℝ) (D*(2:ℝ)^a) ((N:ℝ)^a)]
  · have hm := (abs_le.mp (abs_grid_le_four_mul N)).1
    have hs : -(4*(N:ℝ)) ≤ (grid N : ℝ) := by exact_mod_cast hm
    have hsmall : (N:ℝ) ≤ 16 := by exact_mod_cast (show N ≤ 16 by omega)
    have hc : 64 ≤ C := le_add_of_nonneg_right (by positivity)
    have h := mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ (N:ℝ)^a)
    linarith

end RHFilter.Perron

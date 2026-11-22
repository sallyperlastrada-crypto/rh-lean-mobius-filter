import LandauAxis
import LandauSource
import AbelEuler

/-! Converse for a one-sided source estimate. The two general facts about
positive Mellin transforms and the nonvanishing on the real axis are
explicit so that the dependency on each external theorem is checkable. -/
namespace RHFilter.OneSided
noncomputable section

open Complex MeasureTheory Set Contour LandauAxis LandauSource

def positiveTransform (H : ℝ → ℝ) (s : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi 1, (H t : ℂ)*(t : ℂ)^(-s-1)

/-- Signature of Formalism.landauEq on its original interval (1, infinity). -/
def PositiveLandau : Prop :=
  ∀ (H : ℝ → ℝ) (a b : ℝ), a < b → AEStronglyMeasurable H (volume.restrict (Ioi 1)) →
    (∀ x : ℝ, 1 < x → 0 ≤ H x) →
    (∀ σ : ℝ, b < σ → IntegrableOn (fun x : ℝ => H x * x ^ (-σ - 1)) (Ioi 1)) →
    ∀ Φ : ℂ → ℂ, (∀ s : ℂ, b < s.re → AnalyticAt ℂ Φ s) →
    (∀ σ : ℝ, a < σ → σ ≤ b → AnalyticAt ℂ Φ σ) →
    (∀ s : ℂ, b < s.re → Φ s = positiveTransform H s) →
    ∀ σ : ℝ, a < σ → IntegrableOn (fun x : ℝ => H x * x ^ (-σ - 1)) (Ioi 1) ∧
      Φ σ = positiveTransform H σ

/-- Signature of Formalism.LandauMellinIdentity.imel_differentiableOn. -/
def PositiveMellin : Prop :=
  ∀ {H : ℝ → ℝ} {a : ℝ}, AEStronglyMeasurable H (volume.restrict (Ioi 1)) →
    (∀ t : ℝ, 1 < t → 0 ≤ H t) →
    (∀ σ : ℝ, a < σ → IntegrableOn (fun x : ℝ => H x * x ^ (-σ - 1)) (Ioi 1)) →
    DifferentiableOn ℂ (positiveTransform H) {s : ℂ | a < s.re}

def RealAxis : Prop := ∀ σ : ℝ, 0 < σ → σ < 1 → riemannZeta (σ : ℂ) ≠ 0

/-- What a single one-sided estimate gives in the open strip to its right. -/
theorem zero_free_of_single_lower (landau : PositiveLandau) (mellin : PositiveMellin)
    (axis : RealAxis) {a C : ℝ} (ha : 1/2 < a) (ha1 : a < 1) (hc : 0 ≤ C)
    (hF : ∀ x : ℝ, 0 < x → -C*x^a ≤ F x)
    {s : ℂ} (hs : a < s.re) (hu : s.re < 1) : riemannZeta s ≠ 0 := by
  have ha0 : 0 < a := by linarith
  let H := shifted a C
  have hm : AEStronglyMeasurable H (volume.restrict (Ioi 1)) :=
    (measurable_shifted a C).aestronglyMeasurable
  have hp : ∀ t : ℝ, 1 < t → 0 ≤ H t := fun _ ht => shifted_nonneg ha0.le hc hF ht
  have hid : ∀ z : ℂ, 1 < z.re → candidate a C z = positiveTransform H z := by
    intro z hz
    rw [candidate_eq_right hz, positiveTransform, transform_shifted C ha1.le hz, Abel.transform_eq_source hz]
    congr 1
    simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
    ring
  have hland := landau H a 1 ha1 hm hp (fun _ hσ => shifted_integrable C ha1.le hσ)
    (candidate a C) (fun _ hz => candidate_on_right ha1 hz)
    (fun _ hσ h1 => candidate_on_real ha0 axis hσ h1) hid
  let G := fun z : ℂ => z * (positiveTransform H z - C/(z-a))
  have hPhi := (mellin hm hp (fun σ hσ => (hland σ hσ).1)).analyticOnNhd
    (isOpen_lt continuous_const Complex.continuous_re)
  have hG : AnalyticOnNhd ℂ G {z : ℂ | a < z.re} := by
    intro z hz
    have hza : z ≠ (a : ℂ) := by rintro rfl; exact (lt_irrefl a) hz
    exact analyticAt_id.mul ((hPhi z hz).sub
      (analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hza)))
  have hsource : ∀ z : ℂ, 1 < z.re → riemannZeta z * G z = poly (phase z) := by
    intro z hz
    have hn : z ≠ 0 := by rintro rfl; norm_num at hz
    dsimp only [G]
    rw [← hid z hz, candidate_eq_right hz, add_sub_cancel_right]
    field_simp [hn, riemannZeta_ne_zero_of_one_lt_re hz] <;> ring
  have hs1 : s ≠ 1 := by rintro rfl; simp at hu
  have hz := Converse.continued_product_above ha1 hG hsource s hs hs1
  intro hzero
  rw [hzero, zero_mul] at hz
  exact Converse.symbol_ne_zero (ha.trans hs) hu hz.symm

/-- RH follows from the one-sided estimate on the authentic F, once the
three generic external statements are supplied. -/
theorem rh_of_filter_lower (landau : PositiveLandau) (mellin : PositiveMellin)
    (axis : RealAxis)
    (lower : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : ℝ, 0 < x → -C*x^(1/2+ε) ≤ F x) : RiemannHypothesis := by
  apply RHReduction.of_zeta_right_nonvanishing
  intro s hs _
  by_cases hu : 1 ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re hu
  · have hright : s.re < 1 := lt_of_not_ge hu
    let ε : ℝ := (s.re-1/2)/2
    have he : 0 < ε := by dsimp [ε]; linarith
    obtain ⟨C,hC,hF⟩ := lower ε he
    apply zero_free_of_single_lower landau mellin axis (a := 1/2+ε) (C := C)
      (by linarith) (by dsimp [ε]; linarith) hC hF _ hright
    dsimp [ε]
    linarith

end
end RHFilter.OneSided

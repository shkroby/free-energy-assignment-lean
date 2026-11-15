import Certificate.OverlapOccupationLimit

/-! The soft overlap integral equals the expectation of the square sum
on the full positive-fugacity cavity tree. -/

open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal Topology

namespace Certificate.CanonicalTree

theorem ae_soft_rootOccupation_spec {β d z : ℝ} (hβ : 0 < β) (hd : 0 < d) (hz : 0 < z) :
    ∀ᵐ ω ∂markedSpacings (softCavityProbability β d z : Measure ℝ),
      (∀ i, 0 < rootOccupation β d z ω i) ∧
      Summable (rootOccupation β d z ω) ∧ ∑' i, rootOccupation β d z ω i ≤ 1 := by
  let H : Measure ℝ := softCavityProbability β d z
  let : IsProbabilityMeasure H := inferInstanceAs
    (IsProbabilityMeasure (softCavityProbability β d z : Measure ℝ))
  have hspec := (softCavityProbability_spec hβ hd hz).1
  have hBound : ∀ᵐ x ∂H, x ∈ Icc (0 : ℝ) z⁻¹ := hspec.mono fun _ h => ⟨h.1.le,h.2⟩
  have hmarks : ∀ᵐ ω ∂markedSpacings H, ∀ i, 0 < ω.2 i :=
    ae_all_iff.mpr fun i =>
      (markedArrival_eval_preserving H i).quasiMeasurePreserving.tendsto_ae.eventually
        (hspec.mono fun _ h => h.1)
  filter_upwards [hmarks, ae_summable_cavityTerm_of_bounded_marks hd hβ H hBound,
    ae_arrivalWeightedSum_eq_ofReal_tsum hd hβ H hBound] with ω hω hs hsum
  have hT : 0 ≤ ∑' i, cavityTerm β d ω i := tsum_nonneg fun i =>
    mul_nonneg (Real.exp_nonneg _) (hω i).le
  have hOutput : 0 < arrivalSoftOutput β d z ω := by
    unfold arrivalSoftOutput
    positivity
  refine ⟨fun i => mul_pos (mul_pos (Real.exp_pos _) (hω i)) hOutput, hs.mul_right _, ?_⟩
  unfold rootOccupation
  rw [tsum_mul_right, arrivalSoftOutput, hsum, ENNReal.toReal_ofReal hT, ← div_eq_mul_inv]
  exact (div_le_one (add_pos_of_pos_of_nonneg hz hT)).mpr (le_add_of_nonneg_left hz.le)

/-- At positive fugacity, the overlap integral is the expected sum of
squared occupations of incident edges on the full tree. -/
theorem cavityOverlap_soft_eq_integral_rootOccupation_sq {β d z : ℝ}
    (hβ : 0 < β) (hd : 0 < d) (hz : 0 < z) :
    let H : Measure ℝ := softCavityProbability β d z
    cavityOverlap β d H = ∫ ω, ∑' i, (rootOccupation β d z ω i)^2 ∂markedSpacings H := by
  let H : Measure ℝ := softCavityProbability β d z
  let : IsProbabilityMeasure H := inferInstanceAs
    (IsProbabilityMeasure (softCavityProbability β d z : Measure ℝ))
  have hs := softCavityProbability_spec hβ hd hz
  have hp : ∀ᵐ x ∂H, x ∈ Icc (0:ℝ) z⁻¹ := hs.1.mono fun _ h => ⟨h.1.le,h.2⟩
  have hf : ∀ᵐ ω ∂markedSpacings H, arrivalWeightedSum β d ω ≠ ∞ :=
    (ae_arrivalWeightedSum_eq_ofReal_tsum hd hβ H hp).mono fun _ h =>
      h.trans_ne ENNReal.ofReal_ne_top
  apply cavityOverlap_eq_integral_rootOccupation_sq_of_fixedPoint hd hz.le
    (hs.1.mono fun _ h => h.1) hf hs.2
  filter_upwards [ae_soft_rootOccupation_spec hβ hd hz] with ω ⟨hpos,hsum,hbudget⟩
  refine hsum.of_nonneg_of_le (fun _ => sq_nonneg _) (fun i => ?_)
  have hi := (hsum.le_tsum i (fun j _ => (hpos j).le)).trans hbudget
  nlinarith [mul_nonneg (hpos i).le (sub_nonneg.mpr hi)]

end Certificate.CanonicalTree

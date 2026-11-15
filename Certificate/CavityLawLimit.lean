import Certificate.ArrivalHardCoupling
import Certificate.WeakReciprocal

/-!
# Passing to a hard law from the full denominator limit

This step keeps inversion after the full sum. It applies any proof of
weak convergence of the marked denominators, including one obtained by
uniform truncation of the outgoing sums.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace Certificate

/-- Fugacity plus the weighted marked sum on the canonical spacings. -/
noncomputable def arrivalDenominator (β d z : ℝ) (ω : ArrivalConfiguration) : ℝ :=
  z + (arrivalWeightedSum β d ω).toReal

theorem measurable_arrivalDenominator (β d z : ℝ) : Measurable (arrivalDenominator β d z) :=
  measurable_const.add (measurable_arrivalWeightedSum β d).ennreal_toReal

/-- Law of the canonical denominator for a probability distribution of marks. -/
noncomputable def arrivalDenominatorLaw (β d z : ℝ) (μ : ProbabilityMeasure ℝ) :
    ProbabilityMeasure ℝ := by
  let : IsProbabilityMeasure (markedSpacings μ) := isProbabilityMeasure_markedArrivalSequenceLaw (μ : Measure ℝ)
  exact ⟨(markedSpacings μ).map (arrivalDenominator β d z),
    Measure.isProbabilityMeasure_map (measurable_arrivalDenominator ..).aemeasurable⟩

/-- If the full marked denominators converge in law to the finite positive
denominator with the limiting marks, the limiting mark law solves the
zero-fugacity recursion. -/
theorem isCavityLaw_of_tendsto_arrivalDenominatorLaws {β d : ℝ}
    (z : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure ℝ) (H : ProbabilityMeasure ℝ)
    (hH : (H : Measure ℝ) (Ioi 0) = 1)
    (hμ : Tendsto μ atTop (𝓝 H))
    (hsoft : ∀ n, (markedSpacings (μ n)).map (arrivalSoftOutput β d (z n)) = (μ n : Measure ℝ))
    (hs : ∀ᵐ ω ∂markedSpacings H, Summable (cavityTerm β d ω) ∧
      0 < ∑' i, cavityTerm β d ω i)
    (hD : Tendsto (fun n ↦ arrivalDenominatorLaw β d (z n) (μ n)) atTop
      (𝓝 (arrivalDenominatorLaw β d 0 H))) :
    IsCavityLaw β d (H : Measure ℝ) := by
  let P (n : ℕ) := markedSpacings (μ n)
  let Q := markedSpacings H
  let : ∀ n, IsProbabilityMeasure (P n) := fun n ↦
    isProbabilityMeasure_markedArrivalSequenceLaw (μ n : Measure ℝ)
  let : IsProbabilityMeasure Q := isProbabilityMeasure_markedArrivalSequenceLaw (H : Measure ℝ)
  have hmarks : ∀ᵐ ω ∂Q, ∀ i, 0 < ω.2 i := by
    apply ae_all_iff.mpr
    intro i
    exact (markedArrival_eval_preserving (H : Measure ℝ) i).quasiMeasurePreserving.tendsto_ae.eventually
      ((mem_ae_iff_prob_eq_one measurableSet_Ioi).mpr hH)
  have he : ∀ᵐ ω ∂Q, arrivalDenominator β d 0 ω = ∑' i, cavityTerm β d ω i := by
    filter_upwards [hs, hmarks] with ω hω hp
    have hnonneg (i : ℕ) : 0 ≤ cavityTerm β d ω i :=
      mul_nonneg (Real.exp_nonneg _) (hp i).le
    rw [arrivalDenominator, arrivalWeightedSum, zero_add,
      ← ENNReal.ofReal_tsum_of_nonneg hnonneg hω.1, ENNReal.toReal_ofReal hω.2.le]
  have hpos : ∀ᵐ ω ∂Q, 0 < arrivalDenominator β d 0 ω := by
    filter_upwards [he, hs] with ω he' hs'
    exact he' ▸ hs'.2
  have hDS : TendstoInDistribution (fun n ↦ arrivalDenominator β d (z n)) atTop
      (arrivalDenominator β d 0) P Q :=
    ⟨fun _ ↦ (measurable_arrivalDenominator ..).aemeasurable,
      (measurable_arrivalDenominator ..).aemeasurable, hD⟩
  have hInv := tendstoInDistribution_inv_of_ae_pos
    (fun n ↦ measurable_arrivalDenominator β d (z n)) (measurable_arrivalDenominator β d 0)
    hDS hpos
  let ν : ProbabilityMeasure ℝ := ⟨Q.map (arrivalSoftOutput β d 0),
    Measure.isProbabilityMeasure_map (measurable_arrivalSoftOutput ..).aemeasurable⟩
  have hh : Tendsto μ atTop (𝓝 ν) := by
    have hEq (n : ℕ) :
        (⟨(P n).map (arrivalSoftOutput β d (z n)),
          Measure.isProbabilityMeasure_map (measurable_arrivalSoftOutput ..).aemeasurable⟩ :
          ProbabilityMeasure ℝ) = μ n := Subtype.ext (hsoft n)
    have ht : Tendsto (β := ProbabilityMeasure ℝ) (fun n ↦
      (⟨(P n).map (arrivalSoftOutput β d (z n)),
        Measure.isProbabilityMeasure_map (measurable_arrivalSoftOutput ..).aemeasurable⟩ :
        ProbabilityMeasure ℝ)) atTop (𝓝 ν) := hInv.tendsto
    simpa only [hEq] using ht
  have heq : Q.map (arrivalSoftOutput β d 0) = (H : Measure ℝ) :=
    congrArg (fun p : ProbabilityMeasure ℝ ↦ (p : Measure ℝ)) (tendsto_nhds_unique hh hμ)
  refine ⟨inferInstance, hH, hs, ?_⟩
  have hAE : cavityMap β d =ᵐ[Q] arrivalSoftOutput β d 0 := by
    filter_upwards [he] with ω hω
    change (∑' i, cavityTerm β d ω i)⁻¹ = (arrivalDenominator β d 0 ω)⁻¹
    rw [hω]
  exact (Measure.map_congr hAE).trans heq

end Certificate

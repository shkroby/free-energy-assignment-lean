import Certificate.ArrivalHardCoupling

/-! The two full marked sums on the paired canonical hard model. -/

open MeasureTheory Set

namespace Certificate

/-- The pair of outgoing sums before inversion at zero fugacity. -/
noncomputable def pairedArrivalDenominator (β d : ℝ) (ω : PairedArrivalConfiguration) : ℝ × ℝ :=
  ((arrivalWeightedSum β d (firstArrivalConfiguration ω)).toReal,
    (arrivalWeightedSum β d (secondArrivalConfiguration ω)).toReal)

theorem measurable_pairedArrivalDenominator (β d : ℝ) :
    Measurable (pairedArrivalDenominator β d) :=
  (((measurable_arrivalWeightedSum ..).comp measurable_firstArrivalConfiguration).ennreal_toReal).prodMk
    (((measurable_arrivalWeightedSum ..).comp measurable_secondArrivalConfiguration).ennreal_toReal)

/-- A projection to a hard marginal is represented by a positive finite
real series, including on the original pair-marked probability space. -/
theorem ae_pairedArrivalDenominator_scalar {β d : ℝ} (ρ : Measure (ℝ × ℝ))
    [IsProbabilityMeasure ρ] {f : ℝ × ℝ → ℝ} (hf : Measurable f)
    (hlaw : IsCavityLaw β d (ρ.map f)) :
    ∀ᵐ ω ∂markedArrivalSequenceLaw ρ,
      let E := (ω.1, fun i ↦ f (ω.2 i))
      Summable (cavityTerm β d E) ∧
        (arrivalWeightedSum β d E).toReal = ∑' i, cavityTerm β d E i ∧
        0 < (arrivalWeightedSum β d E).toReal := by
  let : IsProbabilityMeasure (ρ.map f) := hlaw.1
  have hPos : ∀ᵐ x ∂ρ.map f, 0 < x := by
    exact (mem_ae_iff_prob_eq_one (measurableSet_Ioi (a := (0 : ℝ)))).mpr hlaw.2.1
  let P := markedArrivalSequenceLaw ρ
  let proj (ω : PairedArrivalConfiguration) := (ω.1, fun i ↦ f (ω.2 i))
  have hP := (markedArrival_projection ρ f hf).quasiMeasurePreserving.tendsto_ae
  have hMark : ∀ᵐ ω ∂P, ∀ i, 0 < (proj ω).2 i := by
    apply ae_all_iff.mpr
    intro i
    have hfun : MeasurePreserving f ρ (ρ.map f) := ⟨hf, rfl⟩
    exact (hfun.comp (markedArrival_eval_preserving ρ i)).quasiMeasurePreserving.tendsto_ae.eventually hPos
  filter_upwards [hP.eventually hlaw.2.2.1, hMark] with ω hω hm
  have hnn (i : ℕ) : 0 ≤ cavityTerm β d (proj ω) i :=
    mul_nonneg (Real.exp_nonneg _) (hm i).le
  have he : (arrivalWeightedSum β d (proj ω)).toReal = ∑' i, cavityTerm β d (proj ω) i := by
    unfold arrivalWeightedSum
    rw [← ENNReal.ofReal_tsum_of_nonneg hnn hω.1, ENNReal.toReal_ofReal hω.2.le]
  exact ⟨hω.1, he, he.symm ▸ hω.2⟩

end Certificate

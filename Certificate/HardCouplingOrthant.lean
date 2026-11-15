import Certificate.HardCouplingDenominator
import Certificate.CouplingOrthantSum
import Certificate.CouplingOrthantReciprocal
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-! Concordance is preserved by the canonical hard coupling update. -/

open Filter MeasureTheory Set
open scoped Topology

namespace Certificate

/-- The full two-dimensional denominator law before inversion. -/
noncomputable def pairedArrivalDenominatorLaw (β d : ℝ) (ρ : ProbabilityMeasure (ℝ × ℝ)) :
    ProbabilityMeasure (ℝ × ℝ) := by
  let Q := markedArrivalSequenceLaw (ρ : Measure (ℝ × ℝ))
  let : IsProbabilityMeasure Q := isProbabilityMeasure_markedArrivalSequenceLaw (ρ : Measure (ℝ × ℝ))
  exact ⟨Q.map (pairedArrivalDenominator β d),
    Measure.isProbabilityMeasure_map (measurable_pairedArrivalDenominator ..).aemeasurable⟩

theorem tendsto_canonicalArrivalPairPrefixLaw {β d : ℝ} (ρ : ProbabilityMeasure (ℝ × ℝ))
    (h₁ : IsCavityLaw β d ((ρ : Measure (ℝ × ℝ)).map Prod.fst))
    (h₂ : IsCavityLaw β d ((ρ : Measure (ℝ × ℝ)).map Prod.snd)) :
    Tendsto (fun k ↦ canonicalArrivalPairPrefixLaw β d k ρ) atTop
      (𝓝 (pairedArrivalDenominatorLaw β d ρ)) := by
  let Q := markedArrivalSequenceLaw (ρ : Measure (ℝ × ℝ))
  let : IsProbabilityMeasure Q := isProbabilityMeasure_markedArrivalSequenceLaw (ρ : Measure (ℝ × ℝ))
  have hP₁ := ae_pairedArrivalDenominator_scalar (ρ : Measure (ℝ × ℝ)) measurable_fst h₁
  have hP₂ := ae_pairedArrivalDenominator_scalar (ρ : Measure (ℝ × ℝ)) measurable_snd h₂
  have hS : ∀ᵐ ω ∂Q, Tendsto (fun k ↦ canonicalArrivalPairPrefix β d k ω) atTop
      (𝓝 (pairedArrivalDenominator β d ω)) := by
    filter_upwards [hP₁, hP₂] with ω hω₁ hω₂
    refine Tendsto.prodMk_nhds ?_ ?_
    · have hsum : Tendsto (fun k ↦ ∑ i ∈ Finset.range k,
          cavityTerm β d (firstArrivalConfiguration ω) i) atTop
          (𝓝 (∑' i, cavityTerm β d (firstArrivalConfiguration ω) i)) :=
        hω₁.1.hasSum.tendsto_sum_nat
      have he : (arrivalWeightedSum β d (firstArrivalConfiguration ω)).toReal =
          ∑' i, cavityTerm β d (firstArrivalConfiguration ω) i := hω₁.2.1
      rw [← he] at hsum
      change Tendsto (fun k ↦ (canonicalArrivalPairPrefix β d k ω).1) atTop
        (𝓝 ((arrivalWeightedSum β d (firstArrivalConfiguration ω)).toReal))
      have hEq (k : ℕ) : (canonicalArrivalPairPrefix β d k ω).1 =
          ∑ i ∈ Finset.range k, cavityTerm β d (firstArrivalConfiguration ω) i := by
        unfold canonicalArrivalPairPrefix weightedPairPrefix
        rw [Prod.fst_sum]
        exact Finset.sum_congr rfl fun i _ ↦ rfl
      simpa only [hEq] using hsum
    · have hsum : Tendsto (fun k ↦ ∑ i ∈ Finset.range k,
          cavityTerm β d (secondArrivalConfiguration ω) i) atTop
          (𝓝 (∑' i, cavityTerm β d (secondArrivalConfiguration ω) i)) :=
        hω₂.1.hasSum.tendsto_sum_nat
      have he : (arrivalWeightedSum β d (secondArrivalConfiguration ω)).toReal =
          ∑' i, cavityTerm β d (secondArrivalConfiguration ω) i := hω₂.2.1
      rw [← he] at hsum
      change Tendsto (fun k ↦ (canonicalArrivalPairPrefix β d k ω).2) atTop
        (𝓝 ((arrivalWeightedSum β d (secondArrivalConfiguration ω)).toReal))
      have hEq (k : ℕ) : (canonicalArrivalPairPrefix β d k ω).2 =
          ∑ i ∈ Finset.range k, cavityTerm β d (secondArrivalConfiguration ω) i := by
        unfold canonicalArrivalPairPrefix weightedPairPrefix
        rw [Prod.snd_sum]
        exact Finset.sum_congr rfl fun i _ ↦ rfl
      simpa only [hEq] using hsum
  have hlaw := tendstoInDistribution_of_ae_tendsto
    (fun k ↦ (measurable_canonicalArrivalPairPrefix β d k).aemeasurable)
    (measurable_pairedArrivalDenominator ..).aemeasurable hS
  exact hlaw.tendsto

/-- The update maps two pairs of hard marginals in concordance order to
new coupled messages in the same order. -/
theorem orthantLE_pairedHardRootLaw {β d : ℝ}
    {ρ σ : ProbabilityMeasure (ℝ × ℝ)} (h : orthantLE ρ σ)
    (hρ₁ : IsCavityLaw β d ((ρ : Measure (ℝ × ℝ)).map Prod.fst))
    (hρ₂ : IsCavityLaw β d ((ρ : Measure (ℝ × ℝ)).map Prod.snd))
    (hσ₁ : IsCavityLaw β d ((σ : Measure (ℝ × ℝ)).map Prod.fst))
    (hσ₂ : IsCavityLaw β d ((σ : Measure (ℝ × ℝ)).map Prod.snd))
    (hfst : (ρ : Measure (ℝ × ℝ)).map Prod.fst = (σ : Measure (ℝ × ℝ)).map Prod.fst)
    (hsnd : (ρ : Measure (ℝ × ℝ)).map Prod.snd = (σ : Measure (ℝ × ℝ)).map Prod.snd) :
    orthantLE ((pairedArrivalDenominatorLaw β d ρ).map measurable_pairInverse.aemeasurable)
      ((pairedArrivalDenominatorLaw β d σ).map measurable_pairInverse.aemeasurable) := by
  have hLE := orthantLE_of_tendsto (tendsto_canonicalArrivalPairPrefixLaw ρ hρ₁ hρ₂)
    (tendsto_canonicalArrivalPairPrefixLaw σ hσ₁ hσ₂)
    (fun k ↦ orthantLE_canonicalArrivalPairPrefixLaw h β d k)
  apply orthantLE_map_pairInverse hLE
  · change ((markedArrivalSequenceLaw (ρ : Measure (ℝ × ℝ))).map
      (pairedArrivalDenominator β d)).map Prod.fst =
      ((markedArrivalSequenceLaw (σ : Measure (ℝ × ℝ))).map
        (pairedArrivalDenominator β d)).map Prod.fst
    let D (ω : ArrivalConfiguration) := (arrivalWeightedSum β d ω).toReal
    have hm (q : ProbabilityMeasure (ℝ × ℝ)) :
        ((markedArrivalSequenceLaw (q : Measure (ℝ × ℝ))).map
          (pairedArrivalDenominator β d)).map Prod.fst =
        (markedSpacings ((q : Measure (ℝ × ℝ)).map Prod.fst)).map D := by
      rw [Measure.map_map measurable_fst (measurable_pairedArrivalDenominator ..)]
      change (markedArrivalSequenceLaw (q : Measure (ℝ × ℝ))).map
        (D ∘ firstArrivalConfiguration) = _
      have hm₀ : (markedArrivalSequenceLaw (q : Measure (ℝ × ℝ))).map
          firstArrivalConfiguration = markedSpacings ((q : Measure (ℝ × ℝ)).map Prod.fst) :=
        (markedArrival_projection (q : Measure (ℝ × ℝ)) Prod.fst measurable_fst).map_eq
      have hD : Measurable D := (measurable_arrivalWeightedSum ..).ennreal_toReal
      rw [← Measure.map_map hD measurable_firstArrivalConfiguration, hm₀]
    simp only [hm, hfst]
  · let D (ω : ArrivalConfiguration) := (arrivalWeightedSum β d ω).toReal
    have hm (q : ProbabilityMeasure (ℝ × ℝ)) :
        ((pairedArrivalDenominatorLaw β d q : Measure (ℝ × ℝ)).map Prod.snd) =
        (markedSpacings ((q : Measure (ℝ × ℝ)).map Prod.snd)).map D := by
      change ((markedArrivalSequenceLaw (q : Measure (ℝ × ℝ))).map
        (pairedArrivalDenominator β d)).map Prod.snd = _
      rw [Measure.map_map measurable_snd (measurable_pairedArrivalDenominator ..)]
      change (markedArrivalSequenceLaw (q : Measure (ℝ × ℝ))).map
        (D ∘ secondArrivalConfiguration) = _
      have hm₀ : (markedArrivalSequenceLaw (q : Measure (ℝ × ℝ))).map
          secondArrivalConfiguration = markedSpacings ((q : Measure (ℝ × ℝ)).map Prod.snd) :=
        (markedArrival_projection (q : Measure (ℝ × ℝ)) Prod.snd measurable_snd).map_eq
      have hD : Measurable D := (measurable_arrivalWeightedSum ..).ennreal_toReal
      rw [← Measure.map_map hD measurable_secondArrivalConfiguration, hm₀]
    simp only [hm, hsnd]
  · exact (ae_map_iff (measurable_pairedArrivalDenominator ..).aemeasurable
      (measurableSet_Ioi.prod measurableSet_Ioi)).mpr
      ((ae_pairedArrivalDenominator_scalar (ρ : Measure (ℝ × ℝ)) measurable_fst hρ₁).and
        (ae_pairedArrivalDenominator_scalar (ρ : Measure (ℝ × ℝ)) measurable_snd hρ₂) |>.mono
          fun _ h ↦ ⟨h.1.2.2, h.2.2.2⟩)
  · exact (ae_map_iff (measurable_pairedArrivalDenominator ..).aemeasurable
      (measurableSet_Ioi.prod measurableSet_Ioi)).mpr
      ((ae_pairedArrivalDenominator_scalar (σ : Measure (ℝ × ℝ)) measurable_fst hσ₁).and
        (ae_pairedArrivalDenominator_scalar (σ : Measure (ℝ × ℝ)) measurable_snd hσ₂) |>.mono
          fun _ h ↦ ⟨h.1.2.2, h.2.2.2⟩)

end Certificate

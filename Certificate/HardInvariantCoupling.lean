import Certificate.CompactMonotoneFixedPoint
import Certificate.HardCouplingContinuity
import Certificate.HardCouplingOrthant
import Certificate.CanonicalHardLimit

/-!
# Existence of invariant hard couplings

The common-quantile coupling is greatest in the order defined by its
lower-orthant probabilities. Iteration of the hard update from that
coupling is decreasing, and compactness gives an invariant limit.
-/

open MeasureTheory Set

namespace Certificate

theorem hardCouplingProbability_eq_map_pairInverse (β d : ℝ)
    (ρ : ProbabilityMeasure (ℝ × ℝ)) :
    hardCouplingProbability β d ρ =
      (pairedArrivalDenominatorLaw β d ρ).map measurable_pairInverse.aemeasurable := by
  apply Subtype.ext
  change (markedArrivalSequenceLaw (ρ : Measure (ℝ × ℝ))).map (pairedHardRoot β d) =
    ((markedArrivalSequenceLaw (ρ : Measure (ℝ × ℝ))).map (pairedArrivalDenominator β d)).map pairInverse
  rw [Measure.map_map measurable_pairInverse (measurable_pairedArrivalDenominator ..)]
  rfl

/-- For any two positive finite hard cavity laws, the paired recursive
update has an invariant coupling of those marginals. -/
theorem exists_invariant_hard_coupling {β d : ℝ} (hd : 0 < d)
    (μ ν : Measure ℝ) (hμ : IsCavityLaw β d μ) (hν : IsCavityLaw β d ν) :
    ∃ (ρ : Measure (ℝ × ℝ)) (_ : IsProbabilityMeasure ρ),
      ρ.map Prod.fst = μ ∧ ρ.map Prod.snd = ν ∧
      (markedArrivalSequenceLaw ρ).map (pairedHardRoot β d) = ρ := by
  let P : ProbabilityMeasure ℝ := ⟨μ, hμ.1⟩
  let Q : ProbabilityMeasure ℝ := ⟨ν, hν.1⟩
  have hf (ρ : ProbabilityMeasure (ℝ × ℝ)) (hρ : ρ ∈ couplingLaws P Q) :
      (ρ : Measure (ℝ × ℝ)).map Prod.fst = μ :=
    congrArg (fun p : ProbabilityMeasure ℝ ↦ (p : Measure ℝ)) hρ.1
  have hs (ρ : ProbabilityMeasure (ℝ × ℝ)) (hρ : ρ ∈ couplingLaws P Q) :
      (ρ : Measure (ℝ × ℝ)).map Prod.snd = ν :=
    congrArg (fun p : ProbabilityMeasure ℝ ↦ (p : Measure ℝ)) hρ.2
  have hMono : ∀ ρ ∈ couplingLaws P Q, ∀ σ ∈ couplingLaws P Q,
      orthantLE ρ σ → orthantLE (hardCouplingProbability β d ρ) (hardCouplingProbability β d σ) := by
    intro ρ hρ σ hσ h
    rw [hardCouplingProbability_eq_map_pairInverse, hardCouplingProbability_eq_map_pairInverse]
    exact orthantLE_pairedHardRootLaw h (hf ρ hρ ▸ hμ) (hs ρ hρ ▸ hν)
      (hf σ hσ ▸ hμ) (hs σ hσ ▸ hν) ((hf ρ hρ).trans (hf σ hσ).symm)
      ((hs ρ hρ).trans (hs σ hσ).symm)
  obtain ⟨ρ, hρ, hFixed⟩ := exists_fixedPoint_of_compact_order (couplingLaws P Q)
    (isCompact_couplingLaws P Q) orthantLE isClosed_orthantLE
    (fun _ _ _ ↦ le_rfl) (fun _ _ _ hab hbc x y ↦ (hab x y).trans (hbc x y))
    (fun h h' ↦ orthantLE_antisymm h h') (commonQuantileCoupling P Q)
    (commonQuantileCoupling_mem P Q) (fun _ h ↦ commonQuantileCoupling_greatest h)
    (hardCouplingProbability β d)
    (fun _ h ↦ hardCouplingProbability_mem_couplingLaws hμ hν h)
    (continuousOn_hardCouplingProbability hd hμ hν) hMono
  exact ⟨ρ, inferInstance, hf ρ hρ, hs ρ hρ,
    congrArg (fun p : ProbabilityMeasure (ℝ × ℝ) ↦ (p : Measure (ℝ × ℝ))) hFixed⟩

/-- The hard cavity law exists and is unique for every positive
temperature parameter and pseudo-dimension. -/
theorem existsUnique_hard_cavity_law {β d : ℝ} (hβ : 0 < β) (hd : 0 < d) :
    ∃! H : Measure ℝ, IsCavityLaw β d H :=
  existsUnique_hard_cavity_law_of_invariant_couplings hβ hd
    (exists_invariant_hard_coupling hd)

end Certificate

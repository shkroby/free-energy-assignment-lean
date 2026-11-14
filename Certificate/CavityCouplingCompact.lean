import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Compactness of the coupling set

Fixing both marginal laws makes the coupling set weakly closed and uniformly
tight. This checks the compactness input used for the invariant coupling.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Certificate

/-- Probability measures on two real coordinates with given marginal laws. -/
def couplingLaws (μ ν : ProbabilityMeasure ℝ) : Set (ProbabilityMeasure (ℝ × ℝ)) :=
  {ρ | ρ.map measurable_fst.aemeasurable = μ ∧
    ρ.map measurable_snd.aemeasurable = ν}

theorem couplingLaws_nonempty (μ ν : ProbabilityMeasure ℝ) : (couplingLaws μ ν).Nonempty := by
  let ρ : ProbabilityMeasure (ℝ × ℝ) := ⟨(μ : Measure ℝ).prod (ν : Measure ℝ), inferInstance⟩
  refine ⟨ρ, ?_, ?_⟩
  · apply Subtype.ext
    change ((μ : Measure ℝ).prod (ν : Measure ℝ)).map Prod.fst = (μ : Measure ℝ)
    simp
  · apply Subtype.ext
    change ((μ : Measure ℝ).prod (ν : Measure ℝ)).map Prod.snd = (ν : Measure ℝ)
    simp

theorem isClosed_couplingLaws (μ ν : ProbabilityMeasure ℝ) : IsClosed (couplingLaws μ ν) :=
  (isClosed_singleton.preimage (ProbabilityMeasure.continuous_map continuous_fst)).inter
    (isClosed_singleton.preimage (ProbabilityMeasure.continuous_map continuous_snd))

theorem isTightMeasureSet_couplingLaws (μ ν : ProbabilityMeasure ℝ) :
    IsTightMeasureSet {(ρ : Measure (ℝ × ℝ)) | ∃ q ∈ couplingLaws μ ν, (q : Measure _) = ρ} := by
  apply isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr
  intro ε hε
  have hμ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
    (isTightMeasureSet_singleton (μ := (μ : Measure ℝ)))
  have hν := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
    (isTightMeasureSet_singleton (μ := (ν : Measure ℝ)))
  obtain ⟨A, hA, hAμ⟩ := hμ (ε / 2) (ENNReal.half_pos hε.ne')
  obtain ⟨B, hB, hBν⟩ := hν (ε / 2) (ENNReal.half_pos hε.ne')
  refine ⟨A ×ˢ B, hA.prod hB, ?_⟩
  rintro _ ⟨q, hq, rfl⟩
  have hfst : (q : Measure (ℝ × ℝ)).map Prod.fst = μ :=
    congrArg Subtype.val hq.1
  have hsnd : (q : Measure (ℝ × ℝ)).map Prod.snd = ν :=
    congrArg Subtype.val hq.2
  have hcomp : (A ×ˢ B)ᶜ = (Prod.fst ⁻¹' Aᶜ) ∪ (Prod.snd ⁻¹' Bᶜ) := by
    ext p
    simp only [mem_compl_iff, mem_prod, mem_union, mem_preimage, not_and_or]
  rw [hcomp]
  calc
    _ ≤ (q : Measure (ℝ × ℝ)) (Prod.fst ⁻¹' Aᶜ) + (q : Measure (ℝ × ℝ)) (Prod.snd ⁻¹' Bᶜ) :=
      measure_union_le _ _
    _ = (μ : Measure ℝ) Aᶜ + (ν : Measure ℝ) Bᶜ := by
      rw [← Measure.map_apply measurable_fst hA.isClosed.measurableSet.compl, hfst,
        ← Measure.map_apply measurable_snd hB.isClosed.measurableSet.compl, hsnd]
    _ ≤ ε / 2 + ε / 2 := add_le_add (hAμ _ (mem_singleton _)) (hBν _ (mem_singleton _))
    _ = ε := ENNReal.add_halves ε

/-- Fixed-marginal couplings are compact in the topology of weak convergence. -/
theorem isCompact_couplingLaws (μ ν : ProbabilityMeasure ℝ) : IsCompact (couplingLaws μ ν) := by
  rw [← (isClosed_couplingLaws μ ν).closure_eq]
  exact isCompact_closure_of_isTightMeasureSet (isTightMeasureSet_couplingLaws μ ν)

end Certificate

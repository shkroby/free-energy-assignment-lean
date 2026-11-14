import Certificate.CavityCouplingCompact
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! Weak compactness of log laws under uniform two-sided tail bounds. -/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace Certificate

/-- Uniform absolute tail control on real-valued probability laws gives
weak compactness of their closure. -/
theorem isCompact_closure_of_uniform_real_tail (S : Set (ProbabilityMeasure ℝ))
    (htail : ∀ ε : ℝ≥0∞, 0 < ε → ∃ R : ℝ, ∀ μ ∈ S,
      (μ : Measure ℝ) {x | R < |x|} ≤ ε) :
    IsCompact (closure S) := by
  apply isCompact_closure_of_isTightMeasureSet
  apply isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr
  intro ε hε
  obtain ⟨R, hR⟩ := htail ε hε
  refine ⟨Icc (-R) R, isCompact_Icc, ?_⟩
  rintro _ ⟨μ, hμ, rfl⟩
  have hcomp : (Icc (-R) R)ᶜ = {x | R < |x|} := by
    ext x
    simp only [mem_compl_iff, mem_Icc, mem_ofPred_eq, ← abs_le, not_le]
  rw [hcomp]
  exact hR μ hμ

/-- Apply compactness to the pushforwards by the logarithm. -/
theorem isCompact_closure_of_uniform_log_tail (S : Set (ProbabilityMeasure ℝ))
    (htail : ∀ ε : ℝ≥0∞, 0 < ε → ∃ R : ℝ, ∀ μ ∈ S,
      (μ : Measure ℝ) {h | R < |Real.log h|} ≤ ε) :
    IsCompact (closure ((fun μ : ProbabilityMeasure ℝ ↦
      μ.map Real.measurable_log.aemeasurable) '' S)) := by
  apply isCompact_closure_of_uniform_real_tail
  intro ε hε
  obtain ⟨R, hR⟩ := htail ε hε
  refine ⟨R, ?_⟩
  rintro _ ⟨μ, hμ, rfl⟩
  have hA : MeasurableSet {x : ℝ | R < |x|} := measurableSet_lt measurable_const continuous_abs.measurable
  rw [ProbabilityMeasure.toMeasure_map, Measure.map_apply Real.measurable_log hA]
  exact hR μ hμ

/-- Exponentiation takes weak limits of log laws to weak limits on the
strictly positive finite messages. -/
theorem exp_map_pos_and_tendsto {f : ℕ → ProbabilityMeasure ℝ} {G : ProbabilityMeasure ℝ}
    (h : Tendsto f atTop (𝓝 G)) :
    ((G.map Real.measurable_exp.aemeasurable : ProbabilityMeasure ℝ) : Measure ℝ) (Ioi 0) = 1 ∧
      Tendsto (fun n ↦ (f n).map Real.measurable_exp.aemeasurable) atTop
        (𝓝 (G.map Real.measurable_exp.aemeasurable)) := by
  refine ⟨?_, ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous f G h Real.continuous_exp⟩
  rw [ProbabilityMeasure.toMeasure_map, Measure.map_apply Real.measurable_exp measurableSet_Ioi]
  have hset : Real.exp ⁻¹' Ioi 0 = univ := by
    ext x
    simp [Real.exp_pos]
  rw [hset, measure_univ]

end Certificate

import Certificate.MainReduction
import Certificate.OverlapAssignmentCompatibility
import Certificate.OverlapEmpiricalTreeAssembly

/-! The statement of the quenched overlap corollary and its reduction to the
two marked local-tree occupation tests. -/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

namespace Certificate

open Overlap

/-- The quenched overlap corollary for the iid model of the manuscript. -/
def QuenchedOverlapClaim : Prop :=
  ∀ (μ : Measure ℝ) (_ : IsProbabilityMeasure μ) (κ d β : ℝ),
    0 < κ → 0 < d → 0 < β → SmallCostTail μ κ d →
    ∀ H : Measure ℝ, IsCavityLaw β d H →
      let Q := cavityOverlap β d H
      Q ∈ Ioo 0 1 ∧
        (∀ ε > 0, ∃ c > 0, ∀ᵐ C ∂iidCosts μ, ∀ᶠ n : ℕ in atTop,
          gibbsAssignmentPair β d κ n C {p | ε < |assignmentOverlap p.1 p.2 - Q|} ≤
            ENNReal.ofReal (4 * Real.exp (-c * (n : ℝ)))) ∧
        (∀ᵐ C ∂iidCosts μ, gibbsPairSequence β d κ C
          {ω | Tendsto (fun n => assignmentOverlap (ω n).1 (ω n).2) atTop (𝓝 Q)} = 1)

theorem quenchedOverlapClaim_of_canonicalTests
    (hTests : ∀ β d : ℝ, 0 < β → 0 < d → CanonicalOccupationTests β d) :
    QuenchedOverlapClaim := by
  intro μ hprob κ d β hκ hd hβ hμ H hH
  let : IsProbabilityMeasure μ := hprob
  let H' : ProbabilityMeasure ℝ := ⟨H,hH.1⟩
  have hunique (G : Measure ℝ) (hG : IsCavityLaw β d G) : G = H := by
    obtain ⟨F,_,hf⟩ := cavityUniquenessClaim d β hd hβ
    exact (hf G hG).trans (hf H hH).symm
  apply quenchedOverlap_of_retainedOverlapTests hβ hd hκ hμ hH
  apply retainedOverlapTestInput_of_canonicalTests hβ hd hκ hμ H' hH hunique
  · intro R hR D k
    exact ae_tendsto_trimmedAssignment_badRootFraction hd hκ
      (Nat.cast_pos.mpr hR) hμ D k
  · exact hTests β d hβ hd

end Certificate

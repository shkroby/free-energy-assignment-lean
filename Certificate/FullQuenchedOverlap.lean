import Certificate.QuenchedOverlap
import Certificate.OverlapCanonicalShapeTests

/-! The uniform edge-statistic estimate and the quenched overlap corollary. -/

open MeasureTheory ProbabilityTheory

namespace Certificate

open Overlap

/-- Uniform conditional exponential tails for bounded edge statistics,
with centering occupations whose normalized square sum approaches the hard overlap. -/
theorem uniformEdgeStatisticBound
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {β d κ : ℝ} {H : Measure ℝ}
    (hβ : 0 < β) (hd : 0 < d) (hκ : 0 < κ) (hμ : SmallCostTail μ κ d)
    (hH : IsCavityLaw β d H) :
    UniformEdgeStatisticBound μ β d κ (cavityOverlap β d H) := by
  let H' : ProbabilityMeasure ℝ := ⟨H,hH.1⟩
  have hUnique (G : Measure ℝ) (hG : IsCavityLaw β d G) : G = H := by
    obtain ⟨F,_,hf⟩ := cavityUniquenessClaim d β hd hβ
    exact (hf G hG).trans (hf H hH).symm
  apply uniformEdgeStatisticBound_of_retainedOverlapTests hβ hd hκ hμ
  apply retainedOverlapTestInput_of_canonicalTests hβ hd hκ hμ H' hH hUnique
  · intro R hR D k
    exact ae_tendsto_trimmedAssignment_badRootFraction hd hκ (Nat.cast_pos.mpr hR) hμ D k
  · exact canonicalOccupationTests hβ hd

/-- The quenched overlap corollary for every positive dimension and
inverse temperature in the manuscript's iid model. -/
theorem quenchedOverlapClaim : QuenchedOverlapClaim := by
  intro μ hprob κ d β hκ hd hβ hμ H hH
  let : IsProbabilityMeasure μ := hprob
  exact quenchedOverlap_of_uniformEdgeStatisticBound (cavityOverlap_mem_Ioo hd hH)
    (uniformEdgeStatisticBound hβ hd hκ hμ hH)

end Certificate

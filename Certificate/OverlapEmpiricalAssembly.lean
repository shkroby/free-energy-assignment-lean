import Certificate.OverlapAssembly
import Certificate.OverlapAssignmentTilt

/-! Substituting the actual empirical occupation and compatibility estimates. -/

open Filter MeasureTheory Set
open scoped Topology

namespace Certificate.Overlap

/-- The only local-limit inputs to the retained tilt argument are the
root compatibility fraction and the two empirical occupation tests. -/
theorem retainedOverlapTestInput_of_empirical
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {β d κ Q : ℝ}
    (hβ : 0 ≤ β) (hκ : 0 ≤ κ) (hμ : μ (Iio 0) = 0)
    (hRoots : ∀ R : ℕ, 0 < R → ∀ D k : ℕ, ∀ᵐ C ∂iidCosts μ,
      Tendsto (fun n : ℕ =>
        let G := trimmedAssignmentGraph β d κ R n D C
        (((G.vertices \ trimmedAssignmentGoodRoots β d κ R n D k C).card : ℝ) / (n : ℝ)))
          atTop (𝓝 0))
    (hEmpirical : ∀ δ > 0, ∃ η > 0, ∀ᶠ z : ℝ in 𝓝[>] (0 : ℝ),
      ∃ hz : 0 < z, ∀ᶠ R : ℕ in atTop, ∀ᶠ D : ℕ in atTop,
        (∀ᵐ C ∂iidCosts μ, ∀ᶠ n : ℕ in atTop,
          let γ := trimmedAssignmentCenter β d κ R z n D hβ hκ hz C
          |(∑ e, (γ e)^2) / (n : ℝ) - Q| < δ) ∧
        (∀ᵐ C ∂iidCosts μ, ∀ᶠ n : ℕ in atTop,
          let G := trimmedAssignmentGraph β d κ R n D C
          let γ := trimmedAssignmentCenter β d κ R z n D hβ hκ hz C
          (((assignmentRows n \ goodRows G (assignmentRows n) γ η).card : ℝ) / (n : ℝ)) ≤ δ/16)) :
    RetainedOverlapTestInput μ β d κ Q := by
  intro δ hδ
  obtain ⟨η,hη,hTest⟩ := hEmpirical δ hδ
  refine ⟨η,hη,?_⟩
  filter_upwards [hTest] with z hz
  obtain ⟨hz,hTest⟩ := hz
  filter_upwards [hTest, eventually_gt_atTop (0 : ℕ)] with R hTest hR
  filter_upwards [hTest] with D hA
  obtain ⟨hBias,hRows⟩ := hA
  let γ (n : ℕ) (C : CostArray) := trimmedAssignmentCenter β d κ R z n D hβ hκ hz C
  refine ⟨γ, fun n => measurable_trimmedAssignmentCenter β d κ R z n D hβ hκ hz,
    fun n => trimmedAssignmentCenter_mem β d κ R z n D hβ hκ hz, hBias, ?_⟩
  intro a ha
  exact ae_trimmedAssignment_logPartition_tilt_le hβ hκ hμ hz hη (hRoots R hR D) hRows ha

end Certificate.Overlap

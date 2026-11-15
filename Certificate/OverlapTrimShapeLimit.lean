import Certificate.OverlapTrimShapeTests
import Certificate.OverlapTrimShapeMeasurable
import Certificate.OverlapLocalTests

/-! Expected local occupation tests of the finite assignment graph converge
to the Poisson mixture of the same tests on trimmed marked plane shapes. -/

open Filter Finset Function MeasureTheory ProbabilityTheory Set
open scoped BigOperators BoundedContinuousFunction Topology

namespace Certificate.Overlap

open Certificate.OverlapBelief Certificate.LocalExploration Certificate.CanonicalTree

/-- Expected depth-k square statistics converge for fixed trim and cutoff. -/
theorem tendsto_integral_trimmedIterate_square {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {β d κ R u : ℝ} (hd : 0 < d) (hκ : 0 < κ) (hR : 0 < R) (hu : 0 < u)
    (hμ : SmallCostTail μ κ d) (D k : ℕ) (roots : ∀ n : ℕ, Fin (n+1)) :
    Tendsto (fun n => ∫ C,
      squareRowTest
        (incidentEdges (trimmedAssignmentGraph β d κ R (n+1) D C) (Sum.inl (roots n)))
        (incidentOccupationIterate (trimmedAssignmentGraph β d κ R (n+1) D C)
          u k (Sum.inl (roots n))) ∂iidCosts μ) atTop
      (𝓝 (∑' c : PlaneShapeCode (k+3), cutoffShapeMass d R c *
        (∫ marks, c.shape.squareRowTestBCF D k β hu marks
          ∂Measure.infinitePi (fun _ : c.shape.NonRootSlot => truncatedIntensity d R)))) := by
  refine tendsto_integral_of_planeShapeTests hd hκ hR zero_le_one hμ (k+3) roots _
    (fun n => measurable_trimmedIterate_square β d κ R (n+1) D k hu (roots n))
    (fun _ => Eventually.of_forall fun _ => squareRowTest_mem _ _)
    (fun c => c.shape.squareRowTestBCF D k β hu) ?_
  intro n c p C hC
  exact c.shape.squareRowTest_trimmed_eq_shape (roots n) p hκ hu hC D k (by
    rw [c.shape_depth]
    omega)

/-- Expected depth-k small-third statistics converge for fixed trim and cutoff. -/
theorem tendsto_integral_trimmedIterate_smallThird {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {β d κ R u : ℝ} (hd : 0 < d) (hκ : 0 < κ) (hR : 0 < R) (hu : 0 < u)
    (hμ : SmallCostTail μ κ d) (D k : ℕ) (η : ℝ) (roots : ∀ n : ℕ, Fin (n+1)) :
    Tendsto (fun n => ∫ C,
      smallOccupationTest η (thirdOccupation
        (incidentEdges (trimmedAssignmentGraph β d κ R (n+1) D C) (Sum.inl (roots n)))
        (incidentOccupationIterate (trimmedAssignmentGraph β d κ R (n+1) D C)
          u k (Sum.inl (roots n)))) ∂iidCosts μ) atTop
      (𝓝 (∑' c : PlaneShapeCode (k+3), cutoffShapeMass d R c *
        (∫ marks, c.shape.smallOccupationTestBCF D k β η hu marks
          ∂Measure.infinitePi (fun _ : c.shape.NonRootSlot => truncatedIntensity d R)))) := by
  refine tendsto_integral_of_planeShapeTests hd hκ hR zero_le_one hμ (k+3) roots _
    (fun n => measurable_trimmedIterate_smallThird β d κ R (n+1) D k η hu (roots n))
    (fun _ => Eventually.of_forall fun _ => smallOccupationTest_mem _ _)
    (fun c => c.shape.smallOccupationTestBCF D k β η hu) ?_
  intro n c p C hC
  exact c.shape.smallOccupationTest_trimmed_eq_shape (roots n) p hκ hu hC D k η (by
    rw [c.shape_depth]
    omega)

end Certificate.Overlap

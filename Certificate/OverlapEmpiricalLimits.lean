import Certificate.OverlapEmpiricalApproximation
import Certificate.OverlapTrimShapeLimit
import Certificate.PressureNegative

/-! Approximation by finite-depth row tests transfers their tree limits to
the exact empirical BP occupations on the trimmed graph. -/

open Filter Finset MeasureTheory Set ProbabilityTheory
open scoped Topology

namespace Certificate.Overlap
open OverlapBelief LocalExploration CanonicalTree

/-- Almost-sure convergence of the iterate square statistic at fixed trim,
cutoff, and iteration depth. -/
theorem ae_tendsto_trimmedIterate_squareMean
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {β d κ R u : ℝ}
    (hd : 0 < d) (hκ : 0 < κ) (hR : 0 < R) (hu : 0 < u)
    (hμ : SmallCostTail μ κ d) (D k : ℕ) :
    ∀ᵐ C ∂iidCosts μ,
      Tendsto (fun n => (∑ i, trimmedIterateRowTest β d κ R u n D k squareRowTest C i)/(n:ℝ))
        atTop (𝓝 (∑' c : PlaneShapeCode (k+3), cutoffShapeMass d R c *
          ∫ x, c.shape.squareRowTestBCF D k β hu x
            ∂Measure.infinitePi (fun _ : c.shape.NonRootSlot => truncatedIntensity d R))) := by
  apply ae_tendsto_trimmedIterateRowTest_mean_of_expected hu D k (fun _ => squareRowTest)
    (fun _ => squareRowTest_mem) (fun _ {s a b} h => squareRowTest_congr (s := s) (f := a) (g := b) h) ?_ ?_
  · exact fun n i => measurable_trimmedIterate_square β d κ R n D k hu i
  · exact fun roots => tendsto_integral_trimmedIterate_square hd hκ hR hu hμ D k roots

/-- Almost-sure convergence of the iterate statistic for a small third
occupation at fixed trim, cutoff, and iteration depth. -/
theorem ae_tendsto_trimmedIterate_smallThirdMean
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {β d κ R u : ℝ}
    (hd : 0 < d) (hκ : 0 < κ) (hR : 0 < R) (hu : 0 < u)
    (hμ : SmallCostTail μ κ d) (D k : ℕ) (η : ℝ) :
    let P (n : ℕ) (s : Finset (Fin n × Fin n)) (a : Fin n × Fin n → ℝ) :=
      smallOccupationTest η (thirdOccupation s a)
    ∀ᵐ C ∂iidCosts μ,
      Tendsto (fun n => (∑ i, trimmedIterateRowTest β d κ R u n D k (P n) C i)/(n:ℝ))
        atTop (𝓝 (∑' c : PlaneShapeCode (k+3), cutoffShapeMass d R c *
          ∫ x, c.shape.smallOccupationTestBCF D k β η hu x
            ∂Measure.infinitePi (fun _ : c.shape.NonRootSlot => truncatedIntensity d R))) := by
  apply ae_tendsto_trimmedIterateRowTest_mean_of_expected hu D k
    (fun _ s a => smallOccupationTest η (thirdOccupation s a))
    (fun _ _ _ => smallOccupationTest_mem _ _)
    (fun _ {s a b} h => congrArg (smallOccupationTest η)
      (thirdOccupation_congr (s := s) (f := a) (g := b) h)) ?_ ?_
  · exact fun n i => measurable_trimmedIterate_smallThird β d κ R n D k η hu i
  · exact fun roots => tendsto_integral_trimmedIterate_smallThird hd hκ hR hu hμ D k η roots

/-- Uniform approximation by the squared finite-depth tree tests transfers
their deterministic limit to the empirical sum of the exact centers. -/
theorem ae_tendsto_centerSquare_of_treeTests
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {β d κ R u q : ℝ}
    (hβ : 0 ≤ β) (hd : 0 < d) (hκ : 0 < κ) (hR : 0 < R) (hu : 0 < u)
    (hμ : SmallCostTail μ κ d) (D : ℕ)
    (hTree : Tendsto (fun k => ∑' c : PlaneShapeCode (k+3), cutoffShapeMass d R c *
        ∫ x, c.shape.squareRowTestBCF D k β hu x
          ∂Measure.infinitePi (fun _ : c.shape.NonRootSlot => truncatedIntensity d R))
      atTop (𝓝 q)) :
    ∀ᵐ C ∂iidCosts μ,
      Tendsto (fun n =>
        let γ := trimmedAssignmentCenter β d κ R u n D hβ hκ.le hu C
        (∑ e, (γ e)^2)/(n:ℝ)) atTop (𝓝 q) := by
  filter_upwards [ae_cost_nonneg μ hμ.1,
    ae_all_iff.mpr (fun k => ae_tendsto_trimmedIterate_squareMean
      (β := β) hd hκ hR hu hμ D k)] with C hC hIter
  refine tendsto_of_uniform_pressure_cutoff
    (error := fun k => 2*(D:ℝ)*iterateOccupationError u D k) hIter hTree ?_ (fun k => ?_)
  · simpa only [mul_zero] using (tendsto_iterateOccupationError hu D).const_mul (2*(D:ℝ))
  · exact Eventually.of_forall fun n => by
      rw [abs_sub_comm]
      exact abs_trimmedIterate_squareMean_sub_center_le (n := n) (k := k) hβ hκ.le hu C hC

/-- Convergence of the continuous majorant on the tree yields the final
empirical upper bound for rows with fewer than three large occupations. -/
theorem ae_eventually_badRows_fraction_le_of_treeTests
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {β d κ R u η badLimit bound : ℝ}
    (hβ : 0 ≤ β) (hd : 0 < d) (hκ : 0 < κ) (hR : 0 < R) (hu : 0 < u) (hη : 0 < η)
    (hμ : SmallCostTail μ κ d) (D : ℕ) (hbound : badLimit < bound)
    (hTree : Tendsto (fun k => ∑' c : PlaneShapeCode (k+3), cutoffShapeMass d R c *
        ∫ x, c.shape.smallOccupationTestBCF D k β η hu x
          ∂Measure.infinitePi (fun _ : c.shape.NonRootSlot => truncatedIntensity d R))
      atTop (𝓝 badLimit)) :
    ∀ᵐ C ∂iidCosts μ, ∀ᶠ n in atTop,
      let G := trimmedAssignmentGraph β d κ R n D C
      let γ := trimmedAssignmentCenter β d κ R u n D hβ hκ.le hu C
      (((assignmentRows n \ goodRows G (assignmentRows n) γ η).card:ℝ)/(n:ℝ)) ≤ bound := by
  filter_upwards [ae_cost_nonneg μ hμ.1,
    ae_all_iff.mpr (fun k => ae_tendsto_trimmedIterate_smallThirdMean
      (β := β) hd hκ hR hu hμ D k η)] with C hC hIter
  have hlim : Tendsto (fun n =>
      let G := trimmedAssignmentGraph β d κ R n D C
      let γ := trimmedAssignmentCenter β d κ R u n D hβ hκ.le hu C
      (∑ i, smallOccupationTest η (thirdOccupation (OverlapBelief.incidentEdges G (Sum.inl i)) γ))/(n:ℝ))
      atTop (𝓝 badLimit) := by
    refine tendsto_of_uniform_pressure_cutoff
      (error := fun k => iterateOccupationError u D k / η) hIter hTree ?_ (fun k => ?_)
    · simpa only [zero_div] using (tendsto_iterateOccupationError hu D).div_const η
    · exact Eventually.of_forall fun n => by
        rw [abs_sub_comm]
        exact abs_trimmedIterate_smallMean_sub_center_le (n := n) (k := k) hβ hκ.le hu hη C hC
  filter_upwards [hlim.eventually_lt_const hbound] with n hn
  exact (badRows_fraction_le_smallCenterMean (n := n) (D := D) hβ hκ.le hu hη C).trans hn.le

end Certificate.Overlap

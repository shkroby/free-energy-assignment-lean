import Certificate.FiniteLocalBracketLimit

/-! Convergence of bounded local tests specified on finite marked plane trees. -/

open Filter Function MeasureTheory ProbabilityTheory Set
open scoped BoundedContinuousFunction Topology

namespace Certificate.Overlap

open LocalExploration CanonicalTree

private theorem integral_planeShapeEvent_eq {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {d κ R : ℝ} {n k : ℕ} (root : Fin n) (c : PlaneShapeCode k)
    (f : CostArray → ℝ) (hi : Integrable f (iidCosts μ))
    (g : (c.shape.NonRootSlot → ℝ) →ᵇ ℝ)
    (h : ∀ p : c.shape.OrderedPlacement root, ∀ C ∈ c.shape.placementEvent root p
        (Iic (R / lengthScale d κ n)),
      f C = g (labelledNeighborhoodLengths d κ
        (c.shape.nonRootIndex.trans (c.shape.placementEdgeEquiv root p)) C)) :
    (∫ C in c.shape.shapeEvent root (Iic (R / lengthScale d κ n)), f C ∂iidCosts μ) =
      c.shape.shapeTestContribution root μ d κ R c.shape.nonRootIndex g := by
  classical
  let shape := c.shape
  let A := Iic (R / lengthScale d κ n)
  unfold PlaneShape.shapeEvent PlaneShape.shapeTestContribution
  rw [integral_iUnion (fun p => shape.measurableSet_placementEvent root p measurableSet_Iic)
    (shape.placementEvent_pairwiseDisjoint root A) hi.integrableOn, tsum_fintype]
  exact Finset.sum_congr rfl fun p _ =>
    setIntegral_congr_fun (shape.measurableSet_placementEvent root p measurableSet_Iic) (h p)

/-- A bounded observable whose restriction to every realized shape is a
fixed continuous function of the marks converges in expectation to the
Poisson shape mixture. The exceptional shapes need only have vanishing
total mass. -/
theorem tendsto_integral_of_planeShapeTests {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {d κ R M : ℝ} (hd : 0 < d) (hκ : 0 < κ) (hR : 0 < R) (hM : 0 ≤ M)
    (hμ : SmallCostTail μ κ d) (k : ℕ) (roots : ∀ n : ℕ, Fin (n+1))
    (f : ℕ → CostArray → ℝ) (hf : ∀ n, Measurable (f n))
    (hbound : ∀ n, ∀ᵐ C ∂iidCosts μ, f n C ∈ Icc 0 M)
    (g : ∀ c : PlaneShapeCode k, (c.shape.NonRootSlot → ℝ) →ᵇ ℝ)
    (heq : ∀ (n : ℕ) (c : PlaneShapeCode k) (p : c.shape.OrderedPlacement (roots n)),
      ∀ C ∈ c.shape.placementEvent (roots n) p (Iic (R / lengthScale d κ (n+1))),
      f n C = g c (labelledNeighborhoodLengths d κ
        (c.shape.nonRootIndex.trans (c.shape.placementEdgeEquiv (roots n) p)) C)) :
    Tendsto (fun n => ∫ C, f n C ∂iidCosts μ) atTop
      (𝓝 (∑' c : PlaneShapeCode k, cutoffShapeMass d R c *
        (∫ marks, g c marks
          ∂Measure.infinitePi (fun _ : c.shape.NonRootSlot => truncatedIntensity d R)))) := by
  let : IsProbabilityMeasure (iidCosts μ) := by unfold iidCosts; infer_instance
  let A (n : ℕ) (c : PlaneShapeCode k) :=
    c.shape.shapeEvent (roots n) (Iic (R / lengthScale d κ (n+1)))
  let q := cutoffShapeMass d R (k := k)
  let b (c : PlaneShapeCode k) := ∫ marks, g c marks
    ∂Measure.infinitePi (fun _ : c.shape.NonRootSlot => truncatedIntensity d R)
  have hfi (n : ℕ) : Integrable (f n) (iidCosts μ) :=
    Integrable.of_bound (hf n).aestronglyMeasurable M
      ((hbound n).mono fun C h => by
        rw [Real.norm_eq_abs, abs_of_nonneg h.1]
        exact h.2)
  have hm (c : PlaneShapeCode k) : Tendsto (fun n => (iidCosts μ).real (A n c)) atTop (𝓝 (q c)) := by
    simpa only [A, q, cutoffShapeMass_eq_product hd hR.le] using
      c.shape.tendsto_measureReal_shapeEvent_cutoff hd hκ hR hμ roots
  apply tendsto_integral_of_shape_cells (fun _ => iidCosts μ) A
    (fun n c => c.shape.measurableSet_shapeEvent (roots n) measurableSet_Iic)
    (fun n => shapeEvents_disjoint (roots n) _) f hfi hM hbound q b (summable_cutoffShapeMass d R k)
    (cutoffShapeMass_nonneg d R) (tsum_cutoffShapeMass d R k) hm
  intro c
  have ht := c.shape.tendsto_shapeTestContribution hd hκ hR hμ roots c.shape.nonRootIndex (g c)
  have ht' : Tendsto (fun n => ∫ C in A n c, f n C ∂iidCosts μ) atTop (𝓝 (q c * b c)) := by
    rw [show q c = _ from cutoffShapeMass_eq_product hd hR.le c]
    exact ht.congr fun n =>
      (integral_planeShapeEvent_eq (roots n) c (f n) (hfi n) (g c) (heq n c)).symm
  have hne : q c ≠ 0 := (cutoffShapeMass_pos hd hR c).ne'
  have hdiv := ht'.div (hm c) hne
  have he : q c * b c / q c = b c := by field_simp
  rw [he] at hdiv
  exact hdiv

/-- The probability that the fixed-depth neighborhood is represented by
some tree shape tends to one. -/
theorem tendsto_probability_treeShapeUnion {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {d κ R : ℝ} (hd : 0 < d) (hκ : 0 < κ) (hR : 0 < R)
    (hμ : SmallCostTail μ κ d) (k : ℕ) (roots : ∀ n : ℕ, Fin (n+1)) :
    Tendsto (fun n => (iidCosts μ).real
      (⋃ c : PlaneShapeCode k, c.shape.shapeEvent (roots n) (Iic (R / lengthScale d κ (n+1)))))
      atTop (𝓝 1) := by
  let U (n : ℕ) := ⋃ c : PlaneShapeCode k, c.shape.shapeEvent (roots n) (Iic (R / lengthScale d κ (n+1)))
  let f (n : ℕ) : CostArray → ℝ := (U n).indicator (fun _ => 1)
  have hU (n : ℕ) : MeasurableSet (U n) :=
    MeasurableSet.iUnion fun c => c.shape.measurableSet_shapeEvent (roots n) measurableSet_Iic
  have hF := tendsto_integral_of_planeShapeTests hd hκ hR zero_le_one hμ k roots f
    (fun n => measurable_const.indicator (hU n))
    (fun n => Eventually.of_forall fun C => by
      by_cases h : C ∈ U n
      · rw [show f n C = 1 from indicator_of_mem h _]
        exact ⟨zero_le_one,le_rfl⟩
      · rw [show f n C = 0 from indicator_of_notMem h _]
        exact ⟨le_rfl,zero_le_one⟩)
    (fun c => BoundedContinuousFunction.const (c.shape.NonRootSlot → ℝ) 1)
    (fun n c p C h => by
      have hc : C ∈ U n := mem_iUnion.mpr
        ⟨c, mem_iUnion.mpr ⟨p,h⟩⟩
      exact indicator_of_mem hc _)
  have : IsProbabilityMeasure (truncatedIntensity d R) := isProbabilityMeasure_truncatedIntensity hd hR
  simpa only [f, integral_indicator (hU _), integral_const,
    measureReal_restrict_apply_univ, smul_eq_mul, mul_one,
    BoundedContinuousFunction.const_apply, probReal_univ, tsum_cutoffShapeMass] using hF

end Certificate.Overlap

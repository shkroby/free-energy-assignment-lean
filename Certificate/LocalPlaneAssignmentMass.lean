import Certificate.LocalPlaneAssignmentEvent
import Certificate.LocalTreeShapeMarks

/-!
# Finite graph mass and mark limit on each fixed plane shape

Distinct ordered placements have disjoint events. Their equal
probability and conditional iid marks give the Poisson shape mass
times the limiting bounded continuous mark expectation.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology BigOperators BoundedContinuousFunction

namespace Certificate.LocalExploration.PlaneShape

theorem card_planeNonrootSlot (shape : PlaneShape) :
    Fintype.card (PlaneNonrootSlot shape) = Fintype.card shape.Slot - 1 := by
  classical
  let r : shape.Slot := ⟨[],shape.root_mem⟩
  let e : PlaneNonrootSlot shape ≃ {v : shape.Slot // v ≠ r} :=
    { toFun := fun v => ⟨⟨v.val,v.property.1⟩,fun h => v.property.2 (congrArg Subtype.val h)⟩
      invFun := fun v => ⟨v.val.val,v.val.property,fun h => v.property (Subtype.ext h)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_subtype_compl (· = r), Fintype.card_subtype_eq]

/-- A prescribed shape occurs when any of its ordered placements is
the retained neighborhood at the pinned root. -/
def shapeEvent (shape : PlaneShape) {n : ℕ} (root : Fin n) (A : Set ℝ) : Set CostArray :=
  ⋃ p : shape.OrderedPlacement root, shape.placementEvent root p A

theorem measurableSet_placementEvent (shape : PlaneShape) {n : ℕ} (root : Fin n)
    (p : shape.OrderedPlacement root) {A : Set ℝ} (hA : MeasurableSet A) :
    MeasurableSet (shape.placementEvent root p A) :=
  measurableSet_labelledNeighborhoodEvent _ _ _ hA (fun _ _ => MeasurableSet.univ)

theorem measurableSet_shapeEvent (shape : PlaneShape) {n : ℕ} (root : Fin n)
    {A : Set ℝ} (hA : MeasurableSet A) :
    MeasurableSet (shape.shapeEvent root A) :=
  MeasurableSet.iUnion (fun p => shape.measurableSet_placementEvent root p hA)

private theorem measure_placementEvent_scalar (shape : PlaneShape) {n : ℕ} (root : Fin n)
    (p : shape.OrderedPlacement root) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {A : Set ℝ} (hA : MeasurableSet A) :
    (iidCosts μ) (shape.placementEvent root p A) =
      (μ A)^(Fintype.card shape.Slot - 1) * (μ Aᶜ)^
        ((Fintype.card shape.EvenInterior + Fintype.card shape.OddInterior) * n -
        Fintype.card shape.EvenInterior * Fintype.card shape.OddInterior -
        (Fintype.card shape.Slot - 1)) := by
  rw [placementEvent, measure_labelledNeighborhoodEvent μ _ _ _ (shape.placementEdges_subset_tested root p)
    hA (fun _ _ => MeasurableSet.univ)]
  simp only [Set.inter_univ, Finset.prod_const, shape.card_placementEdges,
    shape.card_planeNonrootSlot, shape.card_placementLeftInterior, shape.card_placementRightInterior]

private theorem measureReal_shapeEvent_eq_sum (shape : PlaneShape) {n : ℕ} (root : Fin n)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {A : Set ℝ} (hA : MeasurableSet A) :
    (iidCosts μ).real (shape.shapeEvent root A) =
      ∑ p : shape.OrderedPlacement root, (iidCosts μ).real (shape.placementEvent root p A) := by
  let : IsProbabilityMeasure (iidCosts μ) := by unfold iidCosts; infer_instance
  exact measureReal_iUnion_fintype (shape.placementEvent_pairwiseDisjoint root A)
    (fun p => shape.measurableSet_placementEvent root p hA)

private theorem measureReal_shapeEvent_cutoff (shape : PlaneShape) {n : ℕ} (root : Fin n)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (d κ R : ℝ) :
    (iidCosts μ).real (shape.shapeEvent root (Iic (R / lengthScale d κ n))) =
      (Fintype.card (shape.OrderedPlacement root) : ℝ) *
        (shortEdgeProbability μ d κ R n)^(Fintype.card shape.Slot - 1) *
        (1 - shortEdgeProbability μ d κ R n)^
          ((Fintype.card shape.EvenInterior + Fintype.card shape.OddInterior) * n -
          Fintype.card shape.EvenInterior * Fintype.card shape.OddInterior -
          (Fintype.card shape.Slot - 1)) := by
  let A := Iic (R / lengthScale d κ n)
  let q := shortEdgeProbability μ d κ R n
  have hq₀ : 0 ≤ q := cdf_nonneg μ _
  have hq₁ : q ≤ 1 := cdf_le_one μ _
  have hA : μ A = ENNReal.ofReal q := (ofReal_cdf μ _).symm
  have hAc : μ Aᶜ = ENNReal.ofReal (1-q) := by
    rw [prob_compl_eq_one_sub (show MeasurableSet A from measurableSet_Iic), hA,
      ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hq₀]
  have hP (p : shape.OrderedPlacement root) :
      (iidCosts μ).real (shape.placementEvent root p A) = q^(Fintype.card shape.Slot - 1) *
        (1-q)^((Fintype.card shape.EvenInterior + Fintype.card shape.OddInterior) * n -
          Fintype.card shape.EvenInterior * Fintype.card shape.OddInterior -
          (Fintype.card shape.Slot - 1)) := by
    rw [measureReal_def, shape.measure_placementEvent_scalar root p μ
      (show MeasurableSet A from measurableSet_Iic), hA, hAc, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_pow, ENNReal.toReal_ofReal hq₀,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hq₁)]
  rw [shape.measureReal_shapeEvent_eq_sum root μ (show MeasurableSet A from measurableSet_Iic)]
  simp only [hP, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- The probability of the full fixed shape converges to the product
of Poisson offspring probabilities on its interior slots. -/
theorem tendsto_measureReal_shapeEvent_cutoff (shape : PlaneShape)
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {d κ R : ℝ}
    (hd : 0 < d) (hκ : 0 < κ) (hR : 0 < R) (hμ : SmallCostTail μ κ d)
    (roots : ∀ n : ℕ, Fin (n+1)) :
    Tendsto (fun n => (iidCosts μ).real
      (shape.shapeEvent (roots n) (Iic (R / lengthScale d κ (n+1))))) atTop
      (𝓝 (∏ u : shape.Interior, Real.exp (-(R^d)) * (R^d)^(shape.childCount u.val) /
        (shape.childCount u.val).factorial)) := by
  let l := Fintype.card shape.EvenInterior
  let r := Fintype.card shape.OddInterior
  let e := Fintype.card shape.Slot - 1
  have h₁ := (tendsto_normalized_shortEdge_shape_mass hd hκ hR hμ l r e).comp
    (tendsto_add_atTop_nat 1)
  have h₂ := shape.tendsto_normalized_card_orderedPlacement roots
  have h := h₁.mul h₂
  have hint : l + r = Fintype.card shape.Interior :=
    (Nat.add_comm _ _).trans shape.card_interior_eq_sum_parities.symm
  have hprod : ((R^d)^e * Real.exp (-((l+r : ℕ) : ℝ) * R^d)) *
      (1 / (shape.placementDivisor : ℝ)) =
      ∏ u : shape.Interior, Real.exp (-(R^d)) * (R^d)^(shape.childCount u.val) /
        (shape.childCount u.val).factorial := by
    rw [hint]
    exact shape.normalizedPlacementCylinderMass_eq_poisson_product (R^d)
  rw [hprod] at h
  refine h.congr' (.of_forall fun n => ?_)
  let N := ((n+1 : ℕ) : ℝ)
  let q := shortEdgeProbability μ d κ R (n+1)
  let M := (Fintype.card (shape.OrderedPlacement (roots n)) : ℝ)
  let y := (1-q)^((l+r)*(n+1)-l*r-e)
  change N^e * q^e * y * (M / N^e) = (iidCosts μ).real
    (shape.shapeEvent (roots n) (Iic (R / lengthScale d κ (n+1))))
  rw [shape.measureReal_shapeEvent_cutoff (roots n) μ d κ R]
  change N^e * q^e * y * (M / N^e) = M * q^e * y
  have hN : N^e ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))
  field_simp [hN]

/-- Sum of the weighted expectations over the ordered placements of
one shape. The mark test is expressed on the same symbolic index at
every size and placement. -/
noncomputable def shapeTestContribution (shape : PlaneShape) {I : Type*} [Fintype I]
    {n : ℕ} (root : Fin n) (μ : Measure ℝ) (d κ R : ℝ) (index : I ≃ PlaneNonrootSlot shape)
    (g : (I → ℝ) → ℝ) : ℝ :=
  ∑ p : shape.OrderedPlacement root,
    ∫ C in shape.placementEvent root p (Iic (R / lengthScale d κ n)),
      g (labelledNeighborhoodLengths d κ (index.trans (shape.placementEdgeEquiv root p)) C) ∂iidCosts μ

theorem shapeTestContribution_eq (shape : PlaneShape) {I : Type*} [Fintype I]
    {n : ℕ} (root : Fin n) (μ : Measure ℝ) [IsProbabilityMeasure μ] {d κ R : ℝ}
    (hκ : 0 < κ) (hR : 0 < R) (hμ : SmallCostTail μ κ d) (index : I ≃ PlaneNonrootSlot shape)
    (g : (I → ℝ) →ᵇ ℝ) :
    shape.shapeTestContribution root μ d κ R index g =
      (iidCosts μ).real (shape.shapeEvent root (Iic (R / lengthScale d κ n))) *
        ∫ x, g x ∂Measure.infinitePi (fun _ : I => retainedLengthLaw μ d κ R n) := by
  let : IsProbabilityMeasure (iidCosts μ) := by unfold iidCosts; infer_instance
  have hn : 0 < n := root.isLt.pos
  let A := Iic (R / lengthScale d κ n)
  have hA : MeasurableSet A := measurableSet_Iic
  have hA₀ : μ A ≠ 0 := by
    change μ (Iic _) ≠ 0
    rw [← ofReal_cdf]
    exact (ENNReal.ofReal_pos.mpr (cdf_pos_of_smallCostTail hκ hμ
      (div_pos hR (Real.rpow_pos_of_pos (mul_pos hκ (Nat.cast_pos.mpr hn)) _)))).ne'
  have hterm (p : shape.OrderedPlacement root) :
      (∫ C in shape.placementEvent root p A,
        g (labelledNeighborhoodLengths d κ (index.trans (shape.placementEdgeEquiv root p)) C) ∂iidCosts μ) =
      (iidCosts μ).real (shape.placementEvent root p A) *
        ∫ x, g x ∂Measure.infinitePi (fun _ : I => retainedLengthLaw μ d κ R n) := by
    let S := shape.placementEvent root p A
    by_cases hS₀ : (iidCosts μ) S = 0
    · rw [show (iidCosts μ).restrict S = 0 from Measure.restrict_eq_zero.mpr hS₀,
        integral_zero_measure, measureReal_def, hS₀, ENNReal.toReal_zero, zero_mul]
    · let e := index.trans (shape.placementEdgeEquiv root p)
      have hmap := map_cond_labelledNeighborhoodLengths μ hκ hn
        (shape.placementLeftInterior root p) (shape.placementRightInterior root p)
        (shape.placementEdges root p) (shape.placementEdges_subset_tested root p) e hA₀ hS₀
      change (ProbabilityTheory.cond (iidCosts μ) S).map (labelledNeighborhoodLengths d κ e) =
        Measure.infinitePi (fun _ : I => retainedLengthLaw μ d κ R n) at hmap
      rw [← hmap, integral_map (measurable_labelledNeighborhoodLengths d κ e).aemeasurable
        g.continuous.measurable.aestronglyMeasurable,
        ProbabilityTheory.cond, integral_smul_measure, smul_eq_mul, measureReal_def,
        ← mul_assoc, ENNReal.toReal_inv, mul_inv_cancel₀ (ENNReal.toReal_ne_zero.mpr
          ⟨hS₀, measure_ne_top _ _⟩), one_mul]
  unfold shapeTestContribution
  rw [shape.measureReal_shapeEvent_eq_sum root μ hA, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun p _ => hterm p)

/-- The finite graph contribution of a fixed shape converges to its
Poisson shape mass times the expected test of independent cutoff
intensity marks. -/
theorem tendsto_shapeTestContribution (shape : PlaneShape) {I : Type*} [Fintype I]
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {d κ R : ℝ}
    (hd : 0 < d) (hκ : 0 < κ) (hR : 0 < R) (hμ : SmallCostTail μ κ d)
    (roots : ∀ n : ℕ, Fin (n+1)) (index : I ≃ PlaneNonrootSlot shape) (g : (I → ℝ) →ᵇ ℝ) :
    Tendsto (fun n => shape.shapeTestContribution (roots n) μ d κ R index g)
      atTop (𝓝 ((∏ u : shape.Interior, Real.exp (-(R^d)) * (R^d)^(shape.childCount u.val) /
        (shape.childCount u.val).factorial) *
        ∫ x, g x ∂Measure.infinitePi (fun _ : I => truncatedIntensity d R))) := by
  have hMass := shape.tendsto_measureReal_shapeEvent_cutoff hd hκ hR hμ roots
  have hMarks := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
    (tendsto_retainedMarkProduct hd hκ hR hμ I) g
  refine (hMass.mul hMarks).congr' (.of_forall fun n => ?_)
  exact (shape.shapeTestContribution_eq (roots n) μ hκ hR hμ index g).symm

end Certificate.LocalExploration.PlaneShape

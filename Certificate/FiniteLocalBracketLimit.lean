import Certificate.CanonicalShapeMass
import Certificate.LocalPlaneAssignmentBrackets
import Certificate.LocalPlaneAssignmentMass
import Certificate.LocalShapeMixture
import Certificate.LocalRootSymmetry

/-! The expected fixed-depth brackets of a row root converge to the marked Poisson shape mixture. -/

open Filter Function MeasureTheory ProbabilityTheory Set
open scoped BoundedContinuousFunction Topology

namespace Certificate.CanonicalTree

open LocalExploration

theorem shapeEvents_disjoint {n k : ℕ} (root : Fin n) (A : Set ℝ) :
    Pairwise (Disjoint on fun c : PlaneShapeCode k => c.shape.shapeEvent root A) := by
  intro a b hab
  apply Set.disjoint_left.mpr
  intro C ha hb
  obtain ⟨p, hp⟩ := mem_iUnion.mp ha
  obtain ⟨q, hq⟩ := mem_iUnion.mp hb
  apply hab
  apply Subtype.ext
  rw [← a.shape_slots, ← b.shape_slots]
  exact matchesPlaneShapes_slots_eq (a.shape_depth.trans b.shape_depth.symm)
    ((a.shape.mem_placementEvent_iff root p A C).mp hp)
    ((b.shape.mem_placementEvent_iff root q A C).mp hq)

private noncomputable def shapeBracketTest (shape : PlaneShape) (β : ℝ) {z : ℝ} (hz : 0 < z)
    (P : ℝ × ℝ → ℝ) (hP : Continuous P) (hB : ∀ x : ℝ × ℝ, 0 ≤ x.1 → x.1 ≤ x.2 →
      x.2 ≤ z⁻¹ → P x ∈ Icc 0 z⁻¹) : (shape.NonRootSlot → ℝ) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨P ∘ shape.shapeBracket β z,
    hP.comp (shape.continuous_shapeBracket β hz)⟩ z⁻¹ fun x y => by
      obtain ⟨hx₀, hx₁, hx₂⟩ := shape.shapeBracket_mem β hz x
      obtain ⟨hy₀, hy₁, hy₂⟩ := shape.shapeBracket_mem β hz y
      obtain ⟨a₀, a₁⟩ := hB _ hx₀ hx₁ hx₂
      obtain ⟨b₀, b₁⟩ := hB _ hy₀ hy₁ hy₂
      change dist (P (shape.shapeBracket β z x)) (P (shape.shapeBracket β z y)) ≤ z⁻¹
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith

private theorem integral_shapeEvent_eq {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {β d κ R z : ℝ} (hκ : 0 < κ) {n k : ℕ} (root : Fin n) (c : PlaneShapeCode k)
    (P : ℝ × ℝ → ℝ) (hi : Integrable (P ∘ cutoffRootBounds β d κ R z n k (Sum.inl root)) (iidCosts μ)) :
    (∫ C in c.shape.shapeEvent root (Iic (R / lengthScale d κ n)),
      P (cutoffRootBounds β d κ R z n k (Sum.inl root) C) ∂iidCosts μ) =
    c.shape.shapeTestContribution root μ d κ R c.shape.nonRootIndex
      (P ∘ c.shape.shapeBracket β z) := by
  classical
  let shape := c.shape
  let A := Iic (R / lengthScale d κ n)
  unfold PlaneShape.shapeEvent PlaneShape.shapeTestContribution
  change (∫ C in ⋃ p, shape.placementEvent root p A,
    (P ∘ cutoffRootBounds β d κ R z n k (Sum.inl root)) C ∂iidCosts μ) = _
  rw [integral_iUnion (fun p => shape.measurableSet_placementEvent root p measurableSet_Iic)
    (shape.placementEvent_pairwiseDisjoint root A) hi.integrableOn, tsum_fintype]
  apply Finset.sum_congr rfl
  intro p _
  apply setIntegral_congr_fun (shape.measurableSet_placementEvent root p measurableSet_Iic)
  intro C hC
  apply congrArg P
  simpa only [cutoffRootBounds, shape, c.shape_depth] using
    shape.cutoffRootBounds_eq_shapeBracket root p β d κ R z hκ hC

/-- Positive-cutoff convergence of the expected finite graph bracket at a
row root. The root may vary with the graph size. -/
theorem tendsto_expected_cutoffRowBracket_mixture
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {β d κ R z : ℝ}
    (hd : 0 < d) (hκ : 0 < κ) (hR : 0 < R) (hz : 0 < z)
    (hμ : SmallCostTail μ κ d) (k : ℕ) (roots : ∀ n : ℕ, Fin (n+1))
    (P : ℝ × ℝ → ℝ) (hP : Continuous P) (hB : ∀ x : ℝ × ℝ, 0 ≤ x.1 → x.1 ≤ x.2 →
      x.2 ≤ z⁻¹ → P x ∈ Icc 0 z⁻¹) :
    Tendsto (fun n => ∫ C, P (cutoffRootBounds β d κ R z (n+1) k (Sum.inl (roots n)) C) ∂iidCosts μ)
      atTop (𝓝 (∑' c : PlaneShapeCode k, cutoffShapeMass d R c *
        ∫ marks, P (c.shape.shapeBracket β z marks)
          ∂Measure.infinitePi (fun _ : c.shape.NonRootSlot => truncatedIntensity d R))) := by
  let : IsProbabilityMeasure (iidCosts μ) := by unfold iidCosts; infer_instance
  let A (n : ℕ) (c : PlaneShapeCode k) :=
    c.shape.shapeEvent (roots n) (Iic (R / lengthScale d κ (n+1)))
  let f (n : ℕ) := P ∘ cutoffRootBounds β d κ R z (n+1) k (Sum.inl (roots n))
  let q := cutoffShapeMass d R (k := k)
  let b (c : PlaneShapeCode k) := ∫ marks, P (c.shape.shapeBracket β z marks)
    ∂Measure.infinitePi (fun _ : c.shape.NonRootSlot => truncatedIntensity d R)
  have hfb (n : ℕ) (C : CostArray) : f n C ∈ Icc 0 z⁻¹ := by
    obtain ⟨h₀,h₁,h₂⟩ := cutoffRootBounds_mem β d κ R hz k (Sum.inl (roots n)) C
    exact hB _ h₀ h₁ h₂
  have hfi (n : ℕ) : Integrable (f n) (iidCosts μ) :=
    Integrable.of_bound (hP.measurable.comp (measurable_cutoffRootBounds β d κ R z (n+1) k _)).aestronglyMeasurable _
      (Eventually.of_forall fun C => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hfb n C).1]
        exact (hfb n C).2)
  have hm (c : PlaneShapeCode k) : Tendsto (fun n => (iidCosts μ).real (A n c)) atTop (𝓝 (q c)) := by
    simpa only [A, q, cutoffShapeMass_eq_product hd hR.le] using
      c.shape.tendsto_measureReal_shapeEvent_cutoff hd hκ hR hμ roots
  apply tendsto_integral_of_shape_cells (fun _ => iidCosts μ) A
    (fun n c => c.shape.measurableSet_shapeEvent (roots n) measurableSet_Iic)
    (fun n => shapeEvents_disjoint (roots n) _) f hfi (inv_nonneg.mpr hz.le)
    (fun n => Eventually.of_forall (hfb n)) q b (summable_cutoffShapeMass d R k)
    (cutoffShapeMass_nonneg d R) (tsum_cutoffShapeMass d R k) hm
  intro c
  let g := shapeBracketTest c.shape β hz P hP hB
  have ht := c.shape.tendsto_shapeTestContribution hd hκ hR hμ roots c.shape.nonRootIndex g
  have ht' : Tendsto (fun n => ∫ C in A n c, f n C ∂iidCosts μ) atTop (𝓝 (q c * b c)) := by
    rw [show q c = _ from cutoffShapeMass_eq_product hd hR.le c]
    apply ht.congr
    intro n
    exact (integral_shapeEvent_eq hκ (roots n) c P (hfi n)).symm
  have hne : q c ≠ 0 := (cutoffShapeMass_pos hd hR c).ne'
  have hdiv := ht'.div (hm c) hne
  have heq : q c * b c / q c = b c := by field_simp
  rw [heq] at hdiv
  exact hdiv

end Certificate.CanonicalTree

import Certificate.CanonicalShapePartition
import Certificate.LocalPlanePlacements

/-! The real shape mass and its Poisson product formula. -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Certificate.CanonicalTree

open LocalExploration

/-- The probability of the canonical length-cutoff shape. -/
noncomputable def cutoffShapeMass (d R : ℝ) {k : ℕ} (c : PlaneShapeCode k) : ℝ :=
  law.real {ω | cutoffShapeCode d R k ω = c}

theorem cutoffShapeMass_nonneg (d R : ℝ) {k : ℕ} (c : PlaneShapeCode k) :
    0 ≤ cutoffShapeMass d R c := measureReal_nonneg

theorem summable_cutoffShapeMass (d R : ℝ) (k : ℕ) :
    Summable (cutoffShapeMass d R (k := k)) :=
  ENNReal.summable_toReal ((tsum_cutoffShapeCode_masses d R k).trans_ne ENNReal.one_ne_top)

theorem tsum_cutoffShapeMass (d R : ℝ) (k : ℕ) : ∑' c : PlaneShapeCode k, cutoffShapeMass d R c = 1 := by
  let : IsProbabilityMeasure law := isProbabilityMeasure_law
  simp only [cutoffShapeMass, measureReal_def]
  rw [← ENNReal.tsum_toReal_eq (fun _ ↦ measure_ne_top _ _), tsum_cutoffShapeCode_masses,
    ENNReal.toReal_one]

theorem cutoffShapeMass_eq_product {d R : ℝ} (hd : 0 < d) (hR : 0 ≤ R)
    {k : ℕ} (c : PlaneShapeCode k) :
    cutoffShapeMass d R c =
      ∏ u : c.shape.Interior, Real.exp (-(R^d)) * (R^d)^(c.shape.childCount u.val) /
        (c.shape.childCount u.val).factorial := by
  classical
  let shape := c.shape
  let s := shape.finite_slots.toFinset.filter (fun v ↦ v.length < shape.depth)
  have hs (v : List ℕ) : v ∈ s ↔ v ∈ shape.slots ∧ v.length < shape.depth := by simp [s]
  have he : {ω | cutoffShapeCode d R k ω = c} =
      {ω | (cutoffPlaneShape d R shape.depth ω).slots = shape.slots} := by
    ext ω
    change cutoffShapeCode d R k ω = c ↔
      (cutoffPlaneShape d R shape.depth ω).slots = shape.slots
    constructor
    · intro h
      have h' := congrArg Subtype.val (show cutoffShapeCode d R k ω = c from h)
      change (cutoffPlaneShape d R k ω).slots = c.val at h'
      simpa only [shape, c.shape_depth, c.shape_slots] using h'
    · intro h
      apply Subtype.ext
      change (cutoffPlaneShape d R k ω).slots = c.val
      simpa only [shape, c.shape_depth, c.shape_slots] using h
  have h := measure_cutoffPlaneShape_slots_eq hd hR shape
  change law {ω | (cutoffPlaneShape d R shape.depth ω).slots = shape.slots} =
    ∏ v ∈ s, poissonMeasure (ENNReal.ofReal (R ^ d)).toNNReal {shape.childCount v} at h
  unfold cutoffShapeMass Measure.real
  rw [he, h, ENNReal.toReal_prod]
  simp only [← measureReal_def, poissonMeasure_real_singleton, ENNReal.coe_toNNReal_eq_toReal,
    ENNReal.toReal_ofReal (Real.rpow_nonneg hR _)]
  let e : s ≃ shape.Interior :=
    { toFun := fun v ↦ ⟨v.val, (hs _).mp v.property⟩
      invFun := fun v ↦ ⟨v.val, (hs _).mpr v.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  rw [← Finset.prod_coe_sort]
  exact Fintype.prod_equiv e _ _ (fun _ ↦ rfl)

theorem cutoffShapeMass_pos {d R : ℝ} (hd : 0 < d) (hR : 0 < R)
    {k : ℕ} (c : PlaneShapeCode k) : 0 < cutoffShapeMass d R c := by
  rw [cutoffShapeMass_eq_product hd hR.le]
  exact Finset.prod_pos (fun _ _ ↦ by positivity)

end Certificate.CanonicalTree

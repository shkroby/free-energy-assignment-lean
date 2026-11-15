import Certificate.LocalPlanePlacements
import Certificate.TreeBracketContinuity

/-! The bounded continuous vacancy bracket test of the marks on a fixed shape. -/

open Filter MeasureTheory Set
open scoped Topology

namespace Certificate.LocalExploration.PlaneShape

/-- Each nonroot slot carries the length of its edge to its parent. -/
abbrev NonRootSlot (shape : PlaneShape) := {v : shape.Slot // v.val ≠ []}

noncomputable instance (shape : PlaneShape) : Fintype shape.NonRootSlot := by
  classical
  infer_instance

/-- Outgoing edge weights with zero weight for every absent child. -/
noncomputable def shapeWeight (shape : PlaneShape) (β : ℝ) (marks : shape.NonRootSlot → ℝ)
    (v : List ℕ) (i : ℕ) : ℝ := by
  classical
  exact if h : v ++ [i] ∈ shape.slots then
    Real.exp (-β * marks ⟨⟨v ++ [i], h⟩, by simp⟩) else 0

theorem shapeWeight_nonneg (shape : PlaneShape) (β : ℝ)
    (marks : shape.NonRootSlot → ℝ) (v : List ℕ) (i : ℕ) : 0 ≤ shape.shapeWeight β marks v i := by
  unfold shapeWeight
  split_ifs <;> positivity

theorem shapeWeight_eq_zero_of_notMem (shape : PlaneShape) (β : ℝ)
    (marks : shape.NonRootSlot → ℝ) (v : List ℕ) (i : ℕ)
    (hi : i ∉ Finset.range (shape.childCount v)) : shape.shapeWeight β marks v i = 0 := by
  have hslot : v ++ [i] ∉ shape.slots := fun h ↦ hi (Finset.mem_range.mpr
    ((shape.child_mem v i).mp h).2.2)
  unfold shapeWeight
  rw [dif_neg hslot]

theorem continuous_shapeWeight (shape : PlaneShape) (β : ℝ) (v : List ℕ) (i : ℕ) :
    Continuous (fun marks : shape.NonRootSlot → ℝ ↦ shape.shapeWeight β marks v i) := by
  classical
  by_cases h : v ++ [i] ∈ shape.slots
  · simp only [shapeWeight, dif_pos h]
    fun_prop
  · simp only [shapeWeight, dif_neg h]
    exact continuous_const

/-- Both root brackets for the depth stored in the shape. -/
noncomputable def shapeBracket (shape : PlaneShape) (β z : ℝ) (marks : shape.NonRootSlot → ℝ) :
    ℝ × ℝ :=
  TreeBoundary.bounds z (fun v i ↦ v ++ [i]) (shape.shapeWeight β marks) shape.depth []

theorem continuous_shapeBracket (shape : PlaneShape) (β : ℝ) {z : ℝ} (hz : 0 < z) :
    Continuous (shape.shapeBracket β z) :=
  TreeBoundary.continuous_bounds_of_finite_support hz (fun v i ↦ v ++ [i])
    (shape.shapeWeight β) (fun v ↦ Finset.range (shape.childCount v))
    (shape.shapeWeight_eq_zero_of_notMem β) (shape.shapeWeight_nonneg β)
    (shape.continuous_shapeWeight β) shape.depth []

theorem shapeBracket_mem (shape : PlaneShape) (β : ℝ) {z : ℝ} (hz : 0 < z)
    (marks : shape.NonRootSlot → ℝ) :
    0 ≤ (shape.shapeBracket β z marks).1 ∧
      (shape.shapeBracket β z marks).1 ≤ (shape.shapeBracket β z marks).2 ∧
      (shape.shapeBracket β z marks).2 ≤ z⁻¹ := by
  have hs (v : List ℕ) : Summable (shape.shapeWeight β marks v) := by
    apply summable_of_hasFiniteSupport
    exact ((Finset.range (shape.childCount v)).finite_toSet).subset fun i hi ↦
      by_contra fun hout ↦ hi (shape.shapeWeight_eq_zero_of_notMem β marks v i hout)
  exact TreeBoundary.bounds_mem z (fun v i ↦ v ++ [i]) (shape.shapeWeight β marks)
    hz hs (shape.shapeWeight_nonneg β marks) shape.depth []

end Certificate.LocalExploration.PlaneShape

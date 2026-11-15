import Certificate.CanonicalPlaneShapeLaw

/-! The canonical finite-depth shape probabilities sum to one. -/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Certificate.LocalExploration

/-- A countable index of depth-truncated shapes, recording only their slots. -/
def PlaneShapeCode (depth : ℕ) :=
  {S : Set (List ℕ) // S.Finite ∧ ∃ shape : PlaneShape, shape.depth = depth ∧ shape.slots = S}

instance (depth : ℕ) : Countable (PlaneShapeCode depth) :=
  (Countable.ofPred_finite.mono (fun _ h ↦ h.1)).to_subtype

/-- A representative of the shape encoded by the finite slot set. -/
noncomputable def PlaneShapeCode.shape {depth : ℕ} (c : PlaneShapeCode depth) : PlaneShape :=
  c.property.2.choose

theorem PlaneShapeCode.shape_depth {depth : ℕ} (c : PlaneShapeCode depth) :
    c.shape.depth = depth := c.property.2.choose_spec.1

theorem PlaneShapeCode.shape_slots {depth : ℕ} (c : PlaneShapeCode depth) :
    c.shape.slots = c.val := c.property.2.choose_spec.2

end Certificate.LocalExploration

namespace Certificate.CanonicalTree

open LocalExploration

theorem measurableSet_cutoffOffspringNat_eq (d R : ℝ) (k : ℕ) :
    MeasurableSet {E | cutoffOffspringNat d R E = k} := by
  classical
  let A (j : ℕ) : Set Spacings := {E | cutoffOffspring d R E = (j : ℝ≥0∞)}
  have hA (j : ℕ) : MeasurableSet (A j) :=
    measurableSet_eq_fun (measurable_cutoffOffspring d R) measurable_const
  have he : {E | cutoffOffspringNat d R E = k} = A k ∪
    (if k = 0 then (⋃ j, A j)ᶜ else ∅) := by
    ext E
    change cutoffOffspringNat d R E = k ↔ E ∈ _
    unfold cutoffOffspringNat
    by_cases h : ∃ j : ℕ, cutoffOffspring d R E = (j : ℝ≥0∞)
    · have hmem : E ∈ ⋃ j, A j := mem_iUnion.mpr h
      have he : h.choose = k ↔ E ∈ A k := by
        change h.choose = k ↔ cutoffOffspring d R E = (k : ℝ≥0∞)
        constructor
        · intro he
          exact h.choose_spec.trans (by rw [he])
        · intro he
          have hcast : (h.choose : ℝ≥0∞) = (k : ℝ≥0∞) := h.choose_spec.symm.trans he
          exact_mod_cast hcast
      rw [dif_pos h, he, mem_union]
      by_cases hk : k = 0
      · simp only [if_pos hk, mem_compl_iff, hmem, not_true_eq_false, or_false]
      · simp only [if_neg hk, mem_empty_iff_false, or_false]
    · have hmem : E ∉ ⋃ j, A j := fun hh ↦ h (mem_iUnion.mp hh)
      have hnk : E ∉ A k := fun hh ↦ h ⟨k, hh⟩
      rw [dif_neg h, mem_union]
      by_cases hk : k = 0
      · rw [if_pos hk, mem_compl_iff]
        exact ⟨fun _ ↦ Or.inr hmem, fun _ ↦ hk.symm⟩
      · rw [if_neg hk, mem_empty_iff_false, or_false]
        exact ⟨fun h' ↦ (hk h'.symm).elim, fun h' ↦ (hnk h').elim⟩
  rw [he]
  apply (hA k).union
  split
  · exact (MeasurableSet.iUnion hA).compl
  · exact MeasurableSet.empty

/-- The canonical cutoff shape is recorded by its slot set. -/
noncomputable def cutoffShapeCode (d R : ℝ) (depth : ℕ) (ω : Environment) : PlaneShapeCode depth :=
  let S := cutoffPlaneShape d R depth ω
  ⟨S.slots, S.finite_slots, S, rfl, rfl⟩

theorem measurableSet_cutoffShapeCode_eq (d R : ℝ) {depth : ℕ} (c : PlaneShapeCode depth) :
    MeasurableSet {ω | cutoffShapeCode d R depth ω = c} := by
  let shape := c.shape
  have hD : shape.depth = depth := c.shape_depth
  have hS : shape.slots = c.val := c.shape_slots
  let I := {v : Vertex // v ∈ shape.slots ∧ v.length < shape.depth}
  have hEq : {ω | cutoffShapeCode d R depth ω = c} =
      ⋂ v : I, {ω | cutoffOffspringNat d R (ω v.val) = shape.childCount v.val} := by
    ext ω
    change cutoffShapeCode d R depth ω = c ↔ _
    have hm : cutoffShapeCode d R depth ω = c ↔ (cutoffShapeCode d R depth ω).val = c.val :=
      ⟨congrArg Subtype.val, Subtype.ext⟩
    rw [hm]
    change (PlaneShape.ofOffspring depth (fun v ↦ cutoffOffspringNat d R (ω v))).slots = c.val ↔ _
    have hdEq := congrArg (fun k ↦ PlaneShape.ofOffspring k
      (fun v ↦ cutoffOffspringNat d R (ω v))) hD.symm
    rw [hdEq, ← hS, shape.ofOffspring_slots_eq_iff]
    rw [mem_iInter]
    exact ⟨fun h v ↦ h v.val v.property.1 v.property.2,
      fun h v hv hd ↦ h ⟨v, hv, hd⟩⟩
  rw [hEq]
  apply MeasurableSet.iInter
  intro v
  change MeasurableSet ((fun ω : Environment ↦ ω v.val) ⁻¹'
    {E | cutoffOffspringNat d R E = shape.childCount v.val})
  exact (measurable_pi_apply v.val) (measurableSet_cutoffOffspringNat_eq d R (shape.childCount v.val))

/-- Exact shape masses computed by the Poisson offspring formula are a
probability distribution on the countable depth-truncated shapes. -/
theorem tsum_cutoffShapeCode_masses (d R : ℝ) (depth : ℕ) :
    (∑' c : PlaneShapeCode depth, law {ω | cutoffShapeCode d R depth ω = c}) = 1 := by
  let : IsProbabilityMeasure law := isProbabilityMeasure_law
  have hd : Pairwise (fun a b : PlaneShapeCode depth ↦
      Disjoint {ω | cutoffShapeCode d R depth ω = a} {ω | cutoffShapeCode d R depth ω = b}) := by
    intro a b hab
    exact Set.disjoint_left.mpr fun _ ha hb ↦ hab (ha.symm.trans hb)
  have hU : (⋃ c : PlaneShapeCode depth, {ω | cutoffShapeCode d R depth ω = c}) = univ := by
    apply eq_univ_of_forall
    intro ω
    exact mem_iUnion.mpr ⟨cutoffShapeCode d R depth ω, rfl⟩
  rw [← measure_iUnion hd (measurableSet_cutoffShapeCode_eq d R), hU, measure_univ]

end Certificate.CanonicalTree

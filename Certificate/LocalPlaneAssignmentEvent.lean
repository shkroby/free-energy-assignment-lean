import Certificate.LocalPlaneEdgeImage
import Certificate.LocalPlanePlacements

/-!
# Concrete events and masks for pinned plane placements

The parity-specific injective placements give the exact array edge
set, its nonroot-slot indexing, and the two tested interior sets.
-/

open Set

namespace Certificate.LocalExploration

namespace PlaneShape

theorem placementLabel_alternates (shape : PlaneShape) {n : ℕ} (root : Fin n)
    (p : shape.OrderedPlacement root) :
    PlanePlacementAlternates shape (shape.placementLabel root p) := by
  intro v
  have hcat := List.dropLast_append_getLast v.property.2
  have hpar : v.val.dropLast ∈ shape.slots :=
    ((shape.child_mem ..).mp (hcat.symm ▸ v.property.1)).1
  have hlen := congrArg List.length hcat
  simp only [List.length_append, List.length_singleton] at hlen
  by_cases he : v.val.length % 2 = 0
  · obtain ⟨i, hi⟩ := shape.placementLabel_even root p v.property.1 he
    obtain ⟨j, hj⟩ := shape.placementLabel_odd root p hpar (by omega)
    exact ⟨(i, j), Or.inl ⟨hi, hj⟩⟩
  · obtain ⟨j, hj⟩ := shape.placementLabel_odd root p v.property.1 (by omega)
    obtain ⟨i, hi⟩ := shape.placementLabel_even root p hpar (by omega)
    exact ⟨(i, j), Or.inr ⟨hj, hi⟩⟩

/-- The tested left labels of a pinned plane placement. -/
noncomputable def placementLeftInterior (shape : PlaneShape) {n : ℕ} (root : Fin n)
    (p : shape.OrderedPlacement root) : Finset (Fin n) :=
  planePlacementLeftInterior shape (shape.placementLabel root p)

/-- The tested right labels of a pinned plane placement. -/
noncomputable def placementRightInterior (shape : PlaneShape) {n : ℕ} (root : Fin n)
    (p : shape.OrderedPlacement root) : Finset (Fin n) :=
  planePlacementRightInterior shape (shape.placementLabel root p)

/-- The retained array entries of a pinned plane placement. -/
noncomputable def placementEdges (shape : PlaneShape) {n : ℕ} (root : Fin n)
    (p : shape.OrderedPlacement root) : Finset (Fin n × Fin n) :=
  planePlacementEdges (shape.placementLabel_alternates root p)

theorem placementEdges_subset_tested (shape : PlaneShape) {n : ℕ} (root : Fin n)
    (p : shape.OrderedPlacement root) :
    shape.placementEdges root p ⊆ neighborhoodTestedEdges
      (shape.placementLeftInterior root p) (shape.placementRightInterior root p) :=
  planePlacementEdges_subset_tested (shape.placementLabel_alternates root p)

/-- The actual retained entries can be indexed by the nonroot symbolic
slots, for transporting their marks to the symbolic shape. -/
noncomputable def placementEdgeEquiv (shape : PlaneShape) {n : ℕ} (root : Fin n)
    (p : shape.OrderedPlacement root) :
    PlaneNonrootSlot shape ≃ ↥(shape.placementEdges root p) := by
  let h := shape.placementLabel_alternates root p
  let F (v : PlaneNonrootSlot shape) : ↥(shape.placementEdges root p) :=
    ⟨planePlacementEdge h v, Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩⟩
  apply Equiv.ofBijective F
  constructor
  · intro v w he
    exact planePlacementEdge_injective h (shape.placementLabel_injOn root p) (congrArg Subtype.val he)
  · intro e
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp e.property
    exact ⟨v, Subtype.ext hv⟩

theorem card_placementEdges (shape : PlaneShape) {n : ℕ} (root : Fin n)
    (p : shape.OrderedPlacement root) :
    (shape.placementEdges root p).card = Fintype.card (PlaneNonrootSlot shape) :=
  card_planePlacementEdges _ (shape.placementLabel_injOn root p)

private theorem card_image_of_side_labels {I V : Type*} [Fintype I] {n : ℕ}
    {S : Finset (Fin n)} (F : I → V) (hF : Function.Injective F)
    (tag : Fin n → V) (hTag : Function.Injective tag)
    (hS : ∀ k, k ∈ S ↔ ∃ i, F i = tag k)
    (hCover : ∀ i, ∃ k, F i = tag k) :
    S.card = Fintype.card I := by
  classical
  let K (i : I) := Classical.choose (hCover i)
  have hK (i : I) : F i = tag (K i) := Classical.choose_spec (hCover i)
  let f (i : I) : S := ⟨K i, (hS _).mpr ⟨i, hK i⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j h
      apply hF
      exact (hK i).trans ((congrArg tag (congrArg Subtype.val h)).trans (hK j).symm)
    · intro k
      obtain ⟨i, hi⟩ := (hS k.val).mp k.property
      exact ⟨i, Subtype.ext (hTag ((hK i).symm.trans hi))⟩
  rw [← Fintype.card_coe S]
  exact Fintype.card_congr (Equiv.ofBijective f hf).symm

theorem card_placementLeftInterior (shape : PlaneShape) {n : ℕ} (root : Fin n)
    (p : shape.OrderedPlacement root) :
    (shape.placementLeftInterior root p).card = Fintype.card shape.EvenInterior := by
  let f (v : shape.EvenInterior) := shape.placementLabel root p v.val
  have hF : Function.Injective f := fun v w he =>
    Subtype.ext (shape.placementLabel_injOn root p v.property.1 w.property.1 he)
  apply card_image_of_side_labels f hF (fun i => toLex (Sum.inl i))
    (fun _ _ he => Sum.inl.inj (congrArg ofLex he))
  · intro i
    rw [placementLeftInterior, mem_planePlacementLeftInterior]
    constructor
    · rintro ⟨v, hv, hd, hl⟩
      have hpar : v.length % 2 = 0 := by
        by_contra h
        obtain ⟨j, hj⟩ := shape.placementLabel_odd root p hv (by omega)
        exact Sum.inl_ne_inr (congrArg ofLex (hl.symm.trans hj))
      exact ⟨⟨v, hv, hd, hpar⟩, hl⟩
    · exact fun ⟨v, h⟩ => ⟨v.val, v.property.1, v.property.2.1, h⟩
  · exact fun v => shape.placementLabel_even root p v.property.1 v.property.2.2

theorem card_placementRightInterior (shape : PlaneShape) {n : ℕ} (root : Fin n)
    (p : shape.OrderedPlacement root) :
    (shape.placementRightInterior root p).card = Fintype.card shape.OddInterior := by
  let f (v : shape.OddInterior) := shape.placementLabel root p v.val
  have hF : Function.Injective f := fun v w he =>
    Subtype.ext (shape.placementLabel_injOn root p v.property.1 w.property.1 he)
  apply card_image_of_side_labels f hF (fun j => toLex (Sum.inr j))
    (fun _ _ he => Sum.inr.inj (congrArg ofLex he))
  · intro j
    rw [placementRightInterior, mem_planePlacementRightInterior]
    constructor
    · rintro ⟨v, hv, hd, hl⟩
      have hpar : v.length % 2 = 1 := by
        by_contra h
        obtain ⟨i, hi⟩ := shape.placementLabel_even root p hv (by omega)
        exact Sum.inl_ne_inr (congrArg ofLex (hi.symm.trans hl))
      exact ⟨⟨v, hv, hd, hpar⟩, hl⟩
    · exact fun ⟨v, h⟩ => ⟨v.val, v.property.1, v.property.2.1, h⟩
  · exact fun v => shape.placementLabel_odd root p v.property.1 v.property.2.2

/-- The cylinder event realizing a particular pinned placement. -/
def placementEvent (shape : PlaneShape) {n : ℕ} (root : Fin n)
    (p : shape.OrderedPlacement root) (A : Set ℝ) : Set CostArray :=
  labelledNeighborhoodEvent (shape.placementLeftInterior root p)
    (shape.placementRightInterior root p) (shape.placementEdges root p) A (fun _ => univ)

theorem mem_placementEvent_iff (shape : PlaneShape) {n : ℕ} (root : Fin n)
    (p : shape.OrderedPlacement root) (A : Set ℝ) (C : CostArray) :
    C ∈ shape.placementEvent root p A ↔
      MatchesPlaneShape shape (toLex (Sum.inl root))
        (planeBipartiteNeighbors (planeRetainedPredicate C A)) (shape.placementLabel root p) :=
  (matchesPlaneShape_iff_planePlacementEvent shape _ _ (shape.placementLabel_alternates root p)
    (shape.placementLabel_root root p) (shape.placementLabel_injOn root p)
    (fun _ => shape.placementLabel_child_strictMono root p) A C).symm

theorem placementEvent_pairwiseDisjoint (shape : PlaneShape) {n : ℕ} (root : Fin n)
    (A : Set ℝ) :
    Pairwise (fun p q : shape.OrderedPlacement root => Disjoint
      (shape.placementEvent root p A) (shape.placementEvent root q A)) := by
  intro p q hneq
  have hne : ¬ EqOn (shape.placementLabel root p) (shape.placementLabel root q) shape.slots :=
    fun h => hneq (shape.eq_of_placementLabel_eqOn root h)
  apply Set.disjoint_left.mpr
  intro C hp hq
  exact hne (matchesPlaneShape_eqOn ((shape.mem_placementEvent_iff root p A C).mp hp)
    ((shape.mem_placementEvent_iff root q A C).mp hq))

end PlaneShape

end Certificate.LocalExploration

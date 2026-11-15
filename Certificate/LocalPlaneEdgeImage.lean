import Certificate.LocalPlaneNeighborhoodEvent

/-!
# The edge and interior masks of a plane placement

Each nonroot slot contributes its edge to its parent. Injectivity of
the placement and decreasing length along parent links imply that
these edges are distinct.
-/

open Set

namespace Certificate.LocalExploration

/-- The nonroot slots index the parent edges of a plane shape. -/
abbrev PlaneNonrootSlot (shape : PlaneShape) := {v : List ℕ // v ∈ shape.slots ∧ v ≠ []}

noncomputable instance (shape : PlaneShape) : Fintype (PlaneNonrootSlot shape) :=
  (shape.finite_slots.subset (show {v | v ∈ shape.slots ∧ v ≠ []} ⊆ shape.slots
    from fun _ h => h.1)).fintype

private theorem planeParent_spec (shape : PlaneShape) (v : PlaneNonrootSlot shape) :
    v.val.dropLast ∈ shape.slots ∧
      v.val.dropLast.length < shape.depth ∧
      v.val.getLast v.property.2 < shape.childCount v.val.dropLast := by
  apply (shape.child_mem ..).mp
  simpa only [List.dropLast_append_getLast] using v.property.1

private theorem planeParent_length_lt (shape : PlaneShape) (v : PlaneNonrootSlot shape) :
    v.val.dropLast.length < v.val.length := by
  have h := congrArg List.length (List.dropLast_append_getLast v.property.2)
  simp only [List.length_append, List.length_cons, List.length_nil, zero_add] at h
  omega

/-- The array edge has the stated two endpoints, in either order. -/
def planeEdgeEndpoints {n : ℕ} (u v : PlaneVertex n) (e : Fin n × Fin n) : Prop :=
  (u = toLex (Sum.inl e.1) ∧ v = toLex (Sum.inr e.2)) ∨
    (u = toLex (Sum.inr e.2) ∧ v = toLex (Sum.inl e.1))

private theorem planeEdgeEndpoints_symm {n : ℕ} {u v : PlaneVertex n} {e : Fin n × Fin n} :
    planeEdgeEndpoints u v e → planeEdgeEndpoints v u e := by
  rintro (⟨hu, hv⟩ | ⟨hu, hv⟩)
  · exact Or.inr ⟨hv, hu⟩
  · exact Or.inl ⟨hv, hu⟩

private theorem planeEdgeEndpoints_compare {n : ℕ} {u v u' v' : PlaneVertex n}
    {e : Fin n × Fin n} (h : planeEdgeEndpoints u v e) (h' : planeEdgeEndpoints u' v' e) :
    (u = u' ∧ v = v') ∨ (u = v' ∧ v = u') := by
  rcases h with ⟨hu, hv⟩ | ⟨hu, hv⟩ <;> rcases h' with ⟨hu', hv'⟩ | ⟨hu', hv'⟩
  · exact Or.inl ⟨hu.trans hu'.symm, hv.trans hv'.symm⟩
  · exact Or.inr ⟨hu.trans hv'.symm, hv.trans hu'.symm⟩
  · exact Or.inr ⟨hu.trans hv'.symm, hv.trans hu'.symm⟩
  · exact Or.inl ⟨hu.trans hu'.symm, hv.trans hv'.symm⟩

/-- The bipartite side condition for a labelled plane placement. -/
def PlanePlacementAlternates {n : ℕ} (shape : PlaneShape) (label : List ℕ → PlaneVertex n) : Prop :=
  ∀ v : PlaneNonrootSlot shape, ∃ e,
    planeEdgeEndpoints (label v.val) (label v.val.dropLast) e

/-- The array edge to the parent of a nonroot slot. -/
noncomputable def planePlacementEdge {n : ℕ} {shape : PlaneShape}
    {label : List ℕ → PlaneVertex n} (halt : PlanePlacementAlternates shape label)
    (v : PlaneNonrootSlot shape) : Fin n × Fin n :=
  Classical.choose (halt v)

theorem planePlacementEdge_endpoints {n : ℕ} {shape : PlaneShape}
    {label : List ℕ → PlaneVertex n} (halt : PlanePlacementAlternates shape label)
    (v : PlaneNonrootSlot shape) :
    planeEdgeEndpoints (label v.val) (label v.val.dropLast) (planePlacementEdge halt v) :=
  Classical.choose_spec (halt v)

theorem planePlacementEdge_injective {n : ℕ} {shape : PlaneShape}
    {label : List ℕ → PlaneVertex n} (halt : PlanePlacementAlternates shape label)
    (hinj : InjOn label shape.slots) :
    Function.Injective (planePlacementEdge halt) := by
  intro u v h
  have hu := planePlacementEdge_endpoints halt u
  have hv := planePlacementEdge_endpoints halt v
  rw [← h] at hv
  rcases planeEdgeEndpoints_compare hu hv with ⟨hchild, _⟩ | ⟨huv, hvu⟩
  · exact Subtype.ext (hinj u.property.1 v.property.1 hchild)
  · have heq₁ := congrArg List.length (hinj u.property.1 (planeParent_spec shape v).1 huv)
    have heq₂ := congrArg List.length (hinj (planeParent_spec shape u).1 v.property.1 hvu)
    exact (by
      have h₁ := planeParent_length_lt shape u
      have h₂ := planeParent_length_lt shape v
      omega : False).elim

/-- The array edges of the placed shape. -/
noncomputable def planePlacementEdges {n : ℕ} {shape : PlaneShape}
    {label : List ℕ → PlaneVertex n} (halt : PlanePlacementAlternates shape label) :
    Finset (Fin n × Fin n) :=
  Finset.univ.image (planePlacementEdge halt)

theorem card_planePlacementEdges {n : ℕ} {shape : PlaneShape}
    {label : List ℕ → PlaneVertex n} (halt : PlanePlacementAlternates shape label)
    (hinj : InjOn label shape.slots) :
    (planePlacementEdges halt).card = Fintype.card (PlaneNonrootSlot shape) := by
  rw [planePlacementEdges, Finset.card_image_of_injective _ (planePlacementEdge_injective halt hinj),
    Finset.card_univ]

/-- Left labels whose neighborhood is tested inside the shape depth. -/
noncomputable def planePlacementLeftInterior {n : ℕ} (shape : PlaneShape)
    (label : List ℕ → PlaneVertex n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => ∃ v ∈ shape.slots, v.length < shape.depth ∧
    label v = toLex (Sum.inl i))

/-- Right labels whose neighborhood is tested inside the shape depth. -/
noncomputable def planePlacementRightInterior {n : ℕ} (shape : PlaneShape)
    (label : List ℕ → PlaneVertex n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun j => ∃ v ∈ shape.slots, v.length < shape.depth ∧
    label v = toLex (Sum.inr j))

@[simp] theorem mem_planePlacementLeftInterior {n : ℕ} (shape : PlaneShape)
    (label : List ℕ → PlaneVertex n) (i : Fin n) :
    i ∈ planePlacementLeftInterior shape label ↔ ∃ v ∈ shape.slots, v.length < shape.depth ∧
      label v = toLex (Sum.inl i) := by
  simp [planePlacementLeftInterior]

@[simp] theorem mem_planePlacementRightInterior {n : ℕ} (shape : PlaneShape)
    (label : List ℕ → PlaneVertex n) (j : Fin n) :
    j ∈ planePlacementRightInterior shape label ↔ ∃ v ∈ shape.slots, v.length < shape.depth ∧
      label v = toLex (Sum.inr j) := by
  simp [planePlacementRightInterior]

theorem planePlacementEdges_subset_tested {n : ℕ} {shape : PlaneShape}
    {label : List ℕ → PlaneVertex n} (halt : PlanePlacementAlternates shape label) :
    planePlacementEdges halt ⊆ neighborhoodTestedEdges
      (planePlacementLeftInterior shape label) (planePlacementRightInterior shape label) := by
  intro e he
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp he
  have hpar := planeParent_spec shape v
  simp only [neighborhoodTestedEdges, Finset.mem_union, Finset.mem_product, Finset.mem_univ,
    and_true, true_and, mem_planePlacementLeftInterior, mem_planePlacementRightInterior]
  rcases planePlacementEdge_endpoints halt v with ⟨_, hp⟩ | ⟨_, hp⟩
  · exact Or.inr ⟨_, hpar.1, hpar.2.1, hp⟩
  · exact Or.inl ⟨_, hpar.1, hpar.2.1, hp⟩

private theorem planePlacementAdj_of_endpoints {n : ℕ} {shape : PlaneShape}
    {label : List ℕ → PlaneVertex n} (halt : PlanePlacementAlternates shape label)
    (p : PlaneNonrootSlot shape) {u v : PlaneVertex n}
    (h : planeEdgeEndpoints u v (planePlacementEdge halt p)) :
    v ∈ planeBipartiteNeighbors (fun e => e ∈ planePlacementEdges halt) u := by
  let e := planePlacementEdge halt p
  refine ⟨e.1, e.2, ?_, h⟩
  exact Finset.mem_image.mpr ⟨p, Finset.mem_univ p, Prod.eta _⟩

/-- On each interior vertex, the induced edge mask has exactly that
vertex's parent and children as neighbors. -/
theorem planePlacementNeighbors_eq {n : ℕ} {shape : PlaneShape}
    {label : List ℕ → PlaneVertex n} (halt : PlanePlacementAlternates shape label)
    (hinj : InjOn label shape.slots) (v : List ℕ)
    (hv : v ∈ shape.slots) (hd : v.length < shape.depth) :
    planeBipartiteNeighbors (fun e => e ∈ planePlacementEdges halt) (label v) =
      planeParentLabels label v ∪ planeChildLabels shape label v := by
  ext w
  constructor
  · rintro ⟨i, j, he, h⟩
    have h' : planeEdgeEndpoints (label v) w (i,j) := h
    obtain ⟨p, _, heq⟩ := Finset.mem_image.mp he
    rw [← heq] at h'
    have hp := planeParent_spec shape p
    rcases planeEdgeEndpoints_compare h' (planePlacementEdge_endpoints halt p) with
      ⟨hv', hw⟩ | ⟨hv', hw⟩
    · have he : v = p.val := hinj hv p.property.1 hv'
      exact Or.inl (by simpa only [he, planeParentLabels, if_neg p.property.2,
        mem_singleton_iff] using hw)
    · have he : v = p.val.dropLast := hinj hv hp.1 hv'
      apply Or.inr
      refine ⟨⟨p.val.getLast p.property.2, he.symm ▸ hp.2.2⟩, ?_⟩
      have he' : v ++ [p.val.getLast p.property.2] = p.val := by
        rw [he, List.dropLast_append_getLast]
      exact (congrArg label he').trans hw.symm
  · rintro (hw | ⟨i, rfl⟩)
    · by_cases hroot : v = []
      · simp [planeParentLabels, hroot] at hw
      · have h : w = label v.dropLast := by
          simpa only [planeParentLabels, if_neg hroot, mem_singleton_iff] using hw
        rw [h]
        let p : PlaneNonrootSlot shape := ⟨v, hv, hroot⟩
        exact planePlacementAdj_of_endpoints halt p (planePlacementEdge_endpoints halt p)
    · let p : PlaneNonrootSlot shape :=
        ⟨v ++ [i.val], (shape.child_mem ..).mpr ⟨hv, hd, i.isLt⟩, by simp⟩
      have hparent : p.val.dropLast = v := by simp [p]
      have he := planeEdgeEndpoints_symm (planePlacementEdge_endpoints halt p)
      rw [hparent] at he
      exact planePlacementAdj_of_endpoints halt p he

/-- The exact event for a plane placement is the cylinder given by its
concrete interior and edge masks. -/
theorem matchesPlaneShape_iff_planePlacementEvent {n : ℕ}
    (shape : PlaneShape) (root : PlaneVertex n) (label : List ℕ → PlaneVertex n)
    (halt : PlanePlacementAlternates shape label) (hroot : label [] = root)
    (hinj : InjOn label shape.slots)
    (hmono : ∀ v ∈ shape.slots, v.length < shape.depth →
      StrictMono (fun i : Fin (shape.childCount v) => label (v ++ [i.val])))
    (A : Set ℝ) (C : CostArray) :
    MatchesPlaneShape shape root (planeBipartiteNeighbors (planeRetainedPredicate C A)) label ↔
      C ∈ labelledNeighborhoodEvent (planePlacementLeftInterior shape label)
        (planePlacementRightInterior shape label) (planePlacementEdges halt) A (fun _ => univ) :=
  matchesPlaneShape_iff_labelledNeighborhoodEvent shape root label _ _ _
    (planePlacementEdges_subset_tested halt) hroot hinj hmono
    (mem_planePlacementLeftInterior shape label) (mem_planePlacementRightInterior shape label)
    (planePlacementNeighbors_eq halt hinj) A C

end Certificate.LocalExploration

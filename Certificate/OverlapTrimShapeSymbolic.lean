import Certificate.OverlapTrimShape
import Certificate.OverlapBeliefIterate
import Certificate.OverlapBeliefOccupations
import Certificate.LocalPlaneAssignmentBrackets

/-! Degree trimming and belief propagation on the symbolic marked plane shape. -/

open Finset Set
open scoped BigOperators

namespace Certificate.LocalExploration.PlaneShape

open Certificate.Overlap Certificate.OverlapBelief

variable (shape : PlaneShape)

private theorem dropLast_mem (e : PlaneNonrootSlot shape) : e.val.dropLast ∈ shape.slots :=
  ((shape.child_mem ..).mp ((List.dropLast_append_getLast e.property.2).symm ▸ e.property.1)).1

private def shapeChild (e : PlaneNonrootSlot shape) : shape.Slot :=
  ⟨e.val, e.property.1⟩

private def shapeParent (e : PlaneNonrootSlot shape) : shape.Slot :=
  ⟨e.val.dropLast, shape.dropLast_mem e⟩

private theorem shapeChild_ne_parent (e : PlaneNonrootSlot shape) :
    shape.shapeChild e ≠ shape.shapeParent e := by
  intro h
  have he := congrArg (fun v : shape.Slot => v.val.length) h
  have hp := List.length_pos_iff.mpr e.property.2
  change e.val.length = e.val.dropLast.length at he
  rw [List.length_dropLast] at he
  omega

/-- The row endpoint of a parent edge is its even-depth slot. -/
def shapeEdgeRow (e : PlaneNonrootSlot shape) : shape.Slot :=
  if e.val.length % 2 = 0 then shape.shapeChild e else shape.shapeParent e

/-- The column endpoint of a parent edge is its odd-depth slot. -/
def shapeEdgeCol (e : PlaneNonrootSlot shape) : shape.Slot :=
  if e.val.length % 2 = 0 then shape.shapeParent e else shape.shapeChild e

theorem shapeEdgeRow_ne_col (e : PlaneNonrootSlot shape) :
    shape.shapeEdgeRow e ≠ shape.shapeEdgeCol e := by
  by_cases h : e.val.length % 2 = 0
  · simpa only [shapeEdgeRow, shapeEdgeCol, if_pos h] using shape.shapeChild_ne_parent e
  · simpa only [shapeEdgeRow, shapeEdgeCol, if_neg h] using (shape.shapeChild_ne_parent e).symm

/-- The first degree trim keeps edges of rows of original degree at most D. -/
noncomputable def shapeTrimRows (D : ℕ) : Finset (PlaneNonrootSlot shape) :=
  Finset.univ.filter (fun e => (Finset.univ.filter
    (fun f => shape.shapeEdgeRow f = shape.shapeEdgeRow e)).card ≤ D)

/-- The second trim keeps columns whose degree after the first trim is at most D. -/
noncomputable def shapeTrimDegrees (D : ℕ) : Finset (PlaneNonrootSlot shape) :=
  (shape.shapeTrimRows D).filter (fun e => ((shape.shapeTrimRows D).filter
    (fun f => shape.shapeEdgeCol f = shape.shapeEdgeCol e)).card ≤ D)

/-- The trimmed marked graph uses slots as vertices and parent edges as edges. -/
noncomputable def symbolicTrimmedGraph (D : ℕ) (β : ℝ) (marks : shape.NonRootSlot → ℝ) :
    WeightedGraph shape.Slot (PlaneNonrootSlot shape) where
  vertices := Finset.univ
  edges := shape.shapeTrimDegrees D
  ends e := {shape.shapeEdgeRow e, shape.shapeEdgeCol e}
  weight e := Real.exp (-β * marks (shape.nonRootIndex.symm e))
  weight_nonneg _ := Real.exp_nonneg _
  ends_card e _ := by simp [shape.shapeEdgeRow_ne_col e]
  ends_subset _ _ := Finset.subset_univ _

variable {n : ℕ} (root : Fin n) (p : shape.OrderedPlacement root)

/-- The injective vertex label map for a placement. -/
noncomputable def shapeVertexLabel (v : shape.Slot) : Fin n ⊕ Fin n :=
  ofLex (shape.placementLabel root p v.val)

theorem shapeVertexLabel_injective : Function.Injective (shape.shapeVertexLabel root p) := by
  intro a b h
  exact Subtype.ext (shape.placementLabel_injOn root p a.property b.property (congrArg toLex h))

/-- The injective edge label map for a placement. -/
noncomputable def shapeEdgeLabel : PlaneNonrootSlot shape → (Fin n × Fin n) :=
  planePlacementEdge (shape.placementLabel_alternates root p)

theorem shapeEdgeLabel_injective : Function.Injective (shape.shapeEdgeLabel root p) :=
  planePlacementEdge_injective _ (shape.placementLabel_injOn root p)

theorem shapeEdgeLabel_endpoints (e : PlaneNonrootSlot shape) :
    shape.shapeVertexLabel root p (shape.shapeEdgeRow e) = Sum.inl (shape.shapeEdgeLabel root p e).1 ∧
      shape.shapeVertexLabel root p (shape.shapeEdgeCol e) = Sum.inr (shape.shapeEdgeLabel root p e).2 := by
  have he := planePlacementEdge_endpoints (shape.placementLabel_alternates root p) e
  change planeEdgeEndpoints (shape.placementLabel root p e.val)
    (shape.placementLabel root p e.val.dropLast) (shape.shapeEdgeLabel root p e) at he
  by_cases h : e.val.length % 2 = 0
  · obtain ⟨i,hi⟩ := shape.placementLabel_even root p e.property.1 h
    rcases he with ⟨hr,hc⟩ | ⟨hc,_⟩
    · exact ⟨by simpa only [shapeEdgeRow, if_pos h, shapeVertexLabel, shapeChild, ofLex_toLex] using congrArg ofLex hr,
        by simpa only [shapeEdgeCol, if_pos h, shapeVertexLabel, shapeParent, ofLex_toLex] using congrArg ofLex hc⟩
    · exact (Sum.inl_ne_inr (congrArg ofLex (hi.symm.trans hc))).elim
  · obtain ⟨i,hi⟩ := shape.placementLabel_odd root p e.property.1 (by omega)
    rcases he with ⟨hr,_⟩ | ⟨hc,hr⟩
    · exact (Sum.inl_ne_inr (congrArg ofLex (hr.symm.trans hi))).elim
    · exact ⟨by simpa only [shapeEdgeRow, if_neg h, shapeVertexLabel, shapeParent, ofLex_toLex] using congrArg ofLex hr,
        by simpa only [shapeEdgeCol, if_neg h, shapeVertexLabel, shapeChild, ofLex_toLex] using congrArg ofLex hc⟩

private theorem shapeEdgeLabel_row_eq_iff (e f : PlaneNonrootSlot shape) :
    (shape.shapeEdgeLabel root p e).1 = (shape.shapeEdgeLabel root p f).1 ↔
      shape.shapeEdgeRow e = shape.shapeEdgeRow f := by
  have hE := (shape.shapeEdgeLabel_endpoints root p e).1
  have hF := (shape.shapeEdgeLabel_endpoints root p f).1
  constructor
  · intro h
    exact (shape.shapeVertexLabel_injective root p)
      (hE.trans ((congrArg Sum.inl h).trans hF.symm))
  · intro h
    exact Sum.inl.inj (hE.symm.trans ((congrArg (shape.shapeVertexLabel root p) h).trans hF))

private theorem shapeEdgeLabel_col_eq_iff (e f : PlaneNonrootSlot shape) :
    (shape.shapeEdgeLabel root p e).2 = (shape.shapeEdgeLabel root p f).2 ↔
      shape.shapeEdgeCol e = shape.shapeEdgeCol f := by
  have hE := (shape.shapeEdgeLabel_endpoints root p e).2
  have hF := (shape.shapeEdgeLabel_endpoints root p f).2
  constructor
  · intro h
    exact (shape.shapeVertexLabel_injective root p)
      (hE.trans ((congrArg Sum.inr h).trans hF.symm))
  · intro h
    exact Sum.inr.inj (hE.symm.trans ((congrArg (shape.shapeVertexLabel root p) h).trans hF))

theorem trimRows_placementEdges_eq_image (D : ℕ) :
    trimRows D (shape.placementEdges root p) =
      (shape.shapeTrimRows D).image (shape.shapeEdgeLabel root p) := by
  let S : Finset (PlaneNonrootSlot shape) := Finset.univ
  let f := shape.shapeEdgeLabel root p
  change ((S.image f).filter (fun a => (rowEdges (S.image f) a.1).card ≤ D)) =
    (S.filter (fun e => (S.filter (fun b => shape.shapeEdgeRow b = shape.shapeEdgeRow e)).card ≤ D)).image f
  rw [Finset.filter_image]
  rw [Finset.image_inj (shape.shapeEdgeLabel_injective root p)]
  ext e
  simp only [Finset.mem_filter]
  apply and_congr_right'
  have hr : rowEdges (S.image f) (f e).1 =
      (S.filter fun b => shape.shapeEdgeRow b = shape.shapeEdgeRow e).image f := by
    unfold rowEdges
    rw [Finset.filter_image]
    rw [Finset.image_inj (shape.shapeEdgeLabel_injective root p)]
    ext b
    simp only [Finset.mem_filter]
    exact and_congr_right' (shape.shapeEdgeLabel_row_eq_iff root p b e)
  rw [hr, Finset.card_image_of_injective _ (shape.shapeEdgeLabel_injective root p)]

theorem trimDegrees_placementEdges_eq_image (D : ℕ) :
    trimDegrees D (shape.placementEdges root p) =
      (shape.shapeTrimDegrees D).image (shape.shapeEdgeLabel root p) := by
  let S := shape.shapeTrimRows D
  let f := shape.shapeEdgeLabel root p
  let U := trimRows D (shape.placementEdges root p)
  have h : U = S.image f := shape.trimRows_placementEdges_eq_image root p D
  change (U.filter (fun a => (colEdges U a.2).card ≤ D)) =
    (S.filter (fun e => (S.filter (fun b => shape.shapeEdgeCol b = shape.shapeEdgeCol e)).card ≤ D)).image f
  calc
    _ = ((S.image f).filter (fun a => (colEdges (S.image f) a.2).card ≤ D)) :=
      congrArg (fun T => T.filter (fun a => (colEdges T a.2).card ≤ D)) h
    _ = _ := by
      rw [Finset.filter_image]
      rw [Finset.image_inj (shape.shapeEdgeLabel_injective root p)]
      ext e
      simp only [Finset.mem_filter]
      apply and_congr_right'
      have hc : colEdges (S.image f) (f e).2 =
          (S.filter fun b => shape.shapeEdgeCol b = shape.shapeEdgeCol e).image f := by
        unfold colEdges
        rw [Finset.filter_image]
        rw [Finset.image_inj (shape.shapeEdgeLabel_injective root p)]
        ext b
        simp only [Finset.mem_filter]
        exact and_congr_right' (shape.shapeEdgeLabel_col_eq_iff root p b e)
      rw [hc, Finset.card_image_of_injective _ (shape.shapeEdgeLabel_injective root p)]

/-- In a placement, the graph endpoints are precisely the two embedded slots. -/
theorem symbolicTrimmedGraph_ends_image {β d κ : ℝ} {C : CostArray} (D : ℕ)
    (e : PlaneNonrootSlot shape) :
    (shape.embeddedTrimmedGraph root p β d κ D C).ends (shape.shapeEdgeLabel root p e) =
      {(shape.shapeVertexLabel root p (shape.shapeEdgeRow e)),
        (shape.shapeVertexLabel root p (shape.shapeEdgeCol e))} := by
  rw [(shape.shapeEdgeLabel_endpoints root p e).1, (shape.shapeEdgeLabel_endpoints root p e).2]
  rfl

/-- The labelled weights are precisely the symbolic marked weights. -/
theorem symbolicTrimmedGraph_weight_image {β d κ : ℝ} (D : ℕ) (C : CostArray)
    (e : PlaneNonrootSlot shape) :
    (shape.embeddedTrimmedGraph root p β d κ D C).weight (shape.shapeEdgeLabel root p e) =
      (shape.symbolicTrimmedGraph D β
        (labelledNeighborhoodLengths d κ (shape.nonRootIndex.trans (shape.placementEdgeEquiv root p)) C)).weight e :=
  rfl

theorem symbolicTrimmedGraph_incoming_image {β d κ : ℝ} (D : ℕ) (C : CostArray)
    (marks : shape.NonRootSlot → ℝ)
    (v : shape.Slot) (previous : Option (PlaneNonrootSlot shape)) :
    incomingEdges (shape.embeddedTrimmedGraph root p β d κ D C)
        (shape.shapeVertexLabel root p v, previous.map (shape.shapeEdgeLabel root p)) =
      (incomingEdges (shape.symbolicTrimmedGraph D β marks) (v, previous)).image
        (shape.shapeEdgeLabel root p) := by
  classical
  let G := shape.embeddedTrimmedGraph root p β d κ D C
  let H := shape.symbolicTrimmedGraph D β marks
  let f := shape.shapeEdgeLabel root p
  let g := shape.shapeVertexLabel root p
  have hInc : incidentEdges G (g v) = (incidentEdges H v).image f := by
    have hS : G.edges = H.edges.image f := shape.trimDegrees_placementEdges_eq_image root p D
    unfold incidentEdges
    rw [hS, Finset.filter_image]
    rw [Finset.image_inj (shape.shapeEdgeLabel_injective root p)]
    ext e
    have hh := shape.symbolicTrimmedGraph_ends_image root p (β := β) (d := d) (κ := κ) (C := C) D e
    change G.ends (f e) = {g (shape.shapeEdgeRow e), g (shape.shapeEdgeCol e)} at hh
    have hgi : Function.Injective g := shape.shapeVertexLabel_injective root p
    simp only [Finset.mem_filter, hh, H, symbolicTrimmedGraph, Finset.mem_insert,
      Finset.mem_singleton, hgi.eq_iff]
  change incomingEdges G (g v, previous.map f) = (incomingEdges H (v, previous)).image f
  cases previous with
  | none => exact hInc
  | some a =>
    change (incidentEdges G (g v)).erase (f a) = ((incidentEdges H v).erase a).image f
    rw [hInc, Finset.image_erase (shape.shapeEdgeLabel_injective root p)]

theorem symbolicTrimmedGraph_otherEnd_image {β d κ : ℝ} (D : ℕ) (C : CostArray)
    (marks : shape.NonRootSlot → ℝ)
    (v : shape.Slot) (e : PlaneNonrootSlot shape)
    (h : v ∈ (shape.symbolicTrimmedGraph D β marks).ends e) :
    Tree.otherEnd (shape.embeddedTrimmedGraph root p β d κ D C).ends
        (shape.shapeEdgeLabel root p e) (shape.shapeVertexLabel root p v) =
      shape.shapeVertexLabel root p (Tree.otherEnd (shape.symbolicTrimmedGraph D β marks).ends e v) := by
  let G := shape.embeddedTrimmedGraph root p β d κ D C
  let H := shape.symbolicTrimmedGraph D β marks
  let f := shape.shapeEdgeLabel root p
  let g := shape.shapeVertexLabel root p
  let a := shape.shapeEdgeRow e
  let b := shape.shapeEdgeCol e
  have hG : G.ends (f e) = {g a, g b} := shape.symbolicTrimmedGraph_ends_image root p D e
  have hH : H.ends e = {a,b} := rfl
  have hn : a ≠ b := shape.shapeEdgeRow_ne_col e
  have hn' : g a ≠ g b := (shape.shapeVertexLabel_injective root p).ne hn
  change Tree.otherEnd G.ends (f e) (g v) = g (Tree.otherEnd H.ends e v)
  change v ∈ H.ends e at h
  rw [hH] at h
  rcases Finset.mem_insert.mp h with rfl | h
  · rw [otherEnd_of_endpoints G hG hn', otherEnd_of_endpoints H hH hn]
  · obtain rfl := Finset.mem_singleton.mp h
    rw [otherEnd_swap_of_endpoints G hG hn', otherEnd_swap_of_endpoints H hH hn]

/-- All iterates on the embedded trimmed shape equal those on its symbolic marked graph. -/
theorem logIterate_embedded_eq_symbolic {β d κ u : ℝ} (hu : 0 < u) (C : CostArray)
    (D k : ℕ) (v : shape.Slot) (previous : Option (PlaneNonrootSlot shape)) :
    logIterate (shape.embeddedTrimmedGraph root p β d κ D C) u k
        (shape.shapeVertexLabel root p v, previous.map (shape.shapeEdgeLabel root p)) =
      logIterate (shape.symbolicTrimmedGraph D β
        (labelledNeighborhoodLengths d κ (shape.nonRootIndex.trans (shape.placementEdgeEquiv root p)) C))
        u k (v, previous) := by
  classical
  let G := shape.embeddedTrimmedGraph root p β d κ D C
  let marks := labelledNeighborhoodLengths d κ (shape.nonRootIndex.trans (shape.placementEdgeEquiv root p)) C
  let H := shape.symbolicTrimmedGraph D β marks
  let f := shape.shapeEdgeLabel root p
  let g := shape.shapeVertexLabel root p
  change logIterate G u k (g v, previous.map f) = logIterate H u k (v, previous)
  induction k generalizing v previous with
  | zero => rfl
  | succ k ih =>
    rw [logIterate_succ G hu, logIterate_succ H hu]
    have hs : incomingEdges G (g v, previous.map f) = (incomingEdges H (v, previous)).image f :=
      shape.symbolicTrimmedGraph_incoming_image root p D C marks v previous
    rw [hs]
    unfold logUpdate
    rw [Finset.sum_image (fun _ _ _ _ h => shape.shapeEdgeLabel_injective root p h)]
    apply congrArg (fun a => -Real.log (u + a))
    apply Finset.sum_congr rfl
    intro e he
    have he' : e ∈ incidentEdges H v := by
      cases previous with
      | none => exact he
      | some a => exact Finset.mem_of_mem_erase he
    have heH := (Finset.mem_filter.mp he').2
    have hEnd : Tree.otherEnd G.ends (f e) (g v) = g (Tree.otherEnd H.ends e v) :=
      shape.symbolicTrimmedGraph_otherEnd_image root p D C marks v e heH
    have hw : G.weight (f e) = H.weight e := shape.symbolicTrimmedGraph_weight_image root p D C e
    rw [hw]
    change H.weight e * Real.exp (logIterate G u k (Tree.otherEnd G.ends (f e) (g v), some (f e))) =
      H.weight e * Real.exp (logIterate H u k (Tree.otherEnd H.ends e v, some e))
    rw [hEnd]
    exact congrArg (fun a => H.weight e * Real.exp a)
      (ih (Tree.otherEnd H.ends e v) (some e))

end Certificate.LocalExploration.PlaneShape

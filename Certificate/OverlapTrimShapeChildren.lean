import Certificate.OverlapTrimShapeSymbolic

/-! Directed BP on the symbolic trimmed graph reduces to recursion over
retained child edges. -/

open Finset Set
open scoped BigOperators

namespace Certificate.LocalExploration.PlaneShape

open Certificate.OverlapBelief

variable (shape : PlaneShape)

private theorem parent_mem (e : PlaneNonrootSlot shape) : e.val.dropLast ∈ shape.slots :=
  ((shape.child_mem ..).mp ((List.dropLast_append_getLast e.property.2).symm ▸ e.property.1)).1

/-- The parent of the nonroot slot indexing an edge. -/
def edgeParent (e : PlaneNonrootSlot shape) : shape.Slot :=
  ⟨e.val.dropLast, shape.parent_mem e⟩

/-- The child of the nonroot slot indexing an edge. -/
def edgeChild (e : PlaneNonrootSlot shape) : shape.Slot :=
  ⟨e.val,e.property.1⟩

theorem edgeParent_ne_child (e : PlaneNonrootSlot shape) : shape.edgeParent e ≠ shape.edgeChild e := by
  intro h
  have hl := congrArg (fun v : shape.Slot => v.val.length) h
  have hpos := List.length_pos_iff.mpr e.property.2
  change e.val.dropLast.length = e.val.length at hl
  rw [List.length_dropLast] at hl
  omega

theorem symbolicTrimmedGraph_ends (D : ℕ) (β : ℝ) (marks : shape.NonRootSlot → ℝ)
    (e : PlaneNonrootSlot shape) :
    (shape.symbolicTrimmedGraph D β marks).ends e = {shape.edgeParent e, shape.edgeChild e} := by
  change {shape.shapeEdgeRow e, shape.shapeEdgeCol e} = _
  by_cases h : e.val.length % 2 = 0
  · rw [shapeEdgeRow, shapeEdgeCol, if_pos h, if_pos h]
    change ({shape.edgeChild e, shape.edgeParent e} : Finset shape.Slot) = _
    exact Finset.pair_comm _ _
  · rw [shapeEdgeRow, shapeEdgeCol, if_neg h, if_neg h]
    rfl

/-- The edge a message toward its parent excludes. -/
def parentEdge (v : shape.Slot) : Option (PlaneNonrootSlot shape) :=
  if h : v.val ≠ [] then some ⟨v.val,v.property,h⟩ else none

theorem parentEdge_eq_some_iff (v : shape.Slot) (e : PlaneNonrootSlot shape) :
    shape.parentEdge v = some e ↔ v = shape.edgeChild e := by
  constructor
  · intro h
    by_cases hn : v.val ≠ []
    · simp only [parentEdge, dif_pos hn, Option.some.injEq] at h
      exact Subtype.ext (congrArg (fun a : PlaneNonrootSlot shape => a.val) h)
    · simp [parentEdge,hn] at h
  · rintro rfl
    simp [parentEdge,edgeChild,e.property.2]

/-- The retained edges to the children of the given slot. -/
noncomputable def retainedChildEdges (D : ℕ) (v : shape.Slot) : Finset (PlaneNonrootSlot shape) :=
  (shape.shapeTrimDegrees D).filter (fun e => shape.edgeParent e = v)

theorem symbolicTrimmedGraph_incoming_parent (D : ℕ) (β : ℝ) (marks : shape.NonRootSlot → ℝ)
    (v : shape.Slot) :
    incomingEdges (shape.symbolicTrimmedGraph D β marks) (v, shape.parentEdge v) =
      shape.retainedChildEdges D v := by
  let G := shape.symbolicTrimmedGraph D β marks
  apply Finset.ext
  intro e
  have h : e ∈ incomingEdges G (v, shape.parentEdge v) ↔
      e ∈ G.edges ∧ v ∈ G.ends e ∧ shape.parentEdge v ≠ some e := by
    cases ho : shape.parentEdge v <;>
      simp [incomingEdges, incidentEdges, and_assoc, and_comm, and_left_comm, ne_comm]
  rw [h, shape.symbolicTrimmedGraph_ends D β marks e]
  change e ∈ G.edges ∧ v ∈ ({shape.edgeParent e,shape.edgeChild e} : Finset shape.Slot) ∧
      shape.parentEdge v ≠ some e ↔ e ∈ G.edges.filter (fun e => shape.edgeParent e = v)
  simp only [Finset.mem_insert,Finset.mem_singleton,Finset.mem_filter]
  apply and_congr_right'
  constructor
  · rintro ⟨h | h, hn⟩
    · exact h.symm
    · exact (hn ((shape.parentEdge_eq_some_iff v e).mpr h)).elim
  · intro h
    subst v
    exact ⟨Or.inl rfl,fun hp => shape.edgeParent_ne_child e
      ((shape.parentEdge_eq_some_iff _ _).mp hp)⟩

/-- Directed log iterates computed only from the retained child edges. -/
noncomputable def childLogIterate (shape : PlaneShape) (D : ℕ) (β u : ℝ) (marks : shape.NonRootSlot → ℝ) :
    ℕ → shape.Slot → ℝ
  | 0, _ => -Real.log u
  | k+1, v => logUpdate u (shape.retainedChildEdges D v) (shape.symbolicTrimmedGraph D β marks).weight
      (fun e => childLogIterate shape D β u marks k (shape.edgeChild e))

theorem symbolicTrimmedGraph_logIterate_parent (D : ℕ) (β : ℝ) {u : ℝ} (hu : 0 < u)
    (marks : shape.NonRootSlot → ℝ) (k : ℕ) (v : shape.Slot) :
    logIterate (shape.symbolicTrimmedGraph D β marks) u k (v,shape.parentEdge v) =
      shape.childLogIterate D β u marks k v := by
  let G := shape.symbolicTrimmedGraph D β marks
  induction k generalizing v with
  | zero => rfl
  | succ k ih =>
    rw [logIterate_succ _ hu, shape.symbolicTrimmedGraph_incoming_parent, childLogIterate]
    unfold logUpdate
    apply congrArg (fun a => -Real.log (u+a))
    apply Finset.sum_congr rfl
    intro e he
    have hv : shape.edgeParent e = v := (Finset.mem_filter.mp he).2
    have hOpp : Tree.otherEnd G.ends e v = shape.edgeChild e := by
      rw [← hv]
      exact otherEnd_of_endpoints G (shape.symbolicTrimmedGraph_ends D β marks e)
        (shape.edgeParent_ne_child e)
    have hPrev : shape.parentEdge (shape.edgeChild e) = some e :=
      (shape.parentEdge_eq_some_iff _ _).mpr rfl
    have hVal : incomingState G v e = (shape.edgeChild e,shape.parentEdge (shape.edgeChild e)) := by
      unfold incomingState
      rw [hOpp,hPrev]
    change G.weight e * Real.exp (logIterate G u k (incomingState G v e)) =
      G.weight e * Real.exp (shape.childLogIterate D β u marks k (shape.edgeChild e))
    rw [hVal]
    exact congrArg (fun x => G.weight e * Real.exp x) (ih (shape.edgeChild e))

end Certificate.LocalExploration.PlaneShape

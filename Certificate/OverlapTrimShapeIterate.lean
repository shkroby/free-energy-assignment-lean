import Certificate.OverlapTrimShape
import Certificate.OverlapBeliefIterate

/-! Finite-depth belief propagation inside a realized trimmed plane neighborhood. -/

open Finset Set
open scoped BigOperators

namespace Certificate.LocalExploration.PlaneShape

open Certificate.Overlap

variable {n : ℕ} (shape : PlaneShape) (root : Fin n) (p : shape.OrderedPlacement root)


private theorem otherEnd_mem_ends {V E : Type*} [DecidableEq V]
    (ends : E → Finset V) (e : E) (v : V) (h : v ∈ ends e) :
    Tree.otherEnd ends e v ∈ ends e := by
  by_cases hn : ((ends e).erase v).Nonempty
  · rw [Tree.otherEnd, dif_pos hn]
    exact (Finset.mem_erase.mp hn.choose_spec).2
  · rw [Tree.otherEnd, dif_neg hn]
    exact h

/-- Following an incident shape edge gives a slot at most one level deeper. -/
theorem exists_slot_of_placementOtherEnd {β d κ : ℝ} {C : CostArray} (D : ℕ)
    {v : List ℕ} (hv : v ∈ shape.slots) (hd : v.length < shape.depth)
    {e : Fin n × Fin n} (he : e ∈ shape.placementEdges root p)
    (hvE : ofLex (shape.placementLabel root p v) ∈ Tree.Bipartite.ends e) :
    ∃ w ∈ shape.slots, w.length ≤ v.length + 1 ∧
      Tree.otherEnd (shape.embeddedTrimmedGraph root p β d κ D C).ends e
        (ofLex (shape.placementLabel root p v)) = ofLex (shape.placementLabel root p w) := by
  let x := Tree.otherEnd Tree.Bipartite.ends e (ofLex (shape.placementLabel root p v))
  change ∃ w ∈ shape.slots, w.length ≤ v.length + 1 ∧ x = ofLex (shape.placementLabel root p w)
  have hx : x ∈ Tree.Bipartite.ends e := otherEnd_mem_ends _ _ _ hvE
  by_cases hV : x = ofLex (shape.placementLabel root p v)
  · exact ⟨v,hv,Nat.le_succ _,hV⟩
  · have hmem : toLex x ∈ planeBipartiteNeighbors (fun a => a ∈ shape.placementEdges root p)
        (shape.placementLabel root p v) := by
      have hSide : ofLex (shape.placementLabel root p v) = Sum.inl e.1 ∨
          ofLex (shape.placementLabel root p v) = Sum.inr e.2 := by
        simpa [Tree.Bipartite.ends] using hvE
      have hxSide : x = Sum.inl e.1 ∨ x = Sum.inr e.2 := by
        simpa [Tree.Bipartite.ends] using hx
      rcases hSide with hl | hr
      · have hLabel : shape.placementLabel root p v = toLex (Sum.inl e.1) := congrArg toLex hl
        have hX : x = Sum.inr e.2 := hxSide.resolve_left (fun h => hV (h.trans hl.symm))
        rw [hLabel,hX,mem_planeBipartiteNeighbors_left_right]
        exact he
      · have hLabel : shape.placementLabel root p v = toLex (Sum.inr e.2) := congrArg toLex hr
        have hX : x = Sum.inl e.1 := hxSide.resolve_right (fun h => hV (h.trans hr.symm))
        rw [hLabel,hX,mem_planeBipartiteNeighbors_right_left]
        exact he
    obtain ⟨w,hw,hW,hLen⟩ := shape.exists_slot_of_placementNeighbor root p hv hd hmem
    exact ⟨w,hw,hLen,congrArg ofLex hW.symm⟩

private theorem logIterate_eq_of_neighborhood {V E : Type*} [DecidableEq V] [DecidableEq E]
    (A B : WeightedGraph V E) (label : List ℕ → V) {u : ℝ} (hu : 0 < u)
    (hWeight : A.weight = B.weight) (hEnds : A.ends = B.ends)
    (hIncident : ∀ v ∈ shape.slots, v.length + 2 < shape.depth →
      OverlapBelief.incidentEdges A (label v) = OverlapBelief.incidentEdges B (label v))
    (hNext : ∀ v ∈ shape.slots, v.length < shape.depth →
      ∀ e ∈ OverlapBelief.incidentEdges B (label v),
        ∃ w ∈ shape.slots, w.length ≤ v.length + 1 ∧
          Tree.otherEnd B.ends e (label v) = label w)
    (k : ℕ) (banned : Option E)
    {v : List ℕ} (hv : v ∈ shape.slots) (hd : v.length + k + 1 < shape.depth) :
    OverlapBelief.logIterate A u k (label v, banned) =
      OverlapBelief.logIterate B u k (label v, banned) := by
  induction k generalizing v banned with
  | zero => rfl
  | succ k ih =>
    have hInc := hIncident v hv (by omega)
    have hIn : OverlapBelief.incomingEdges A (label v, banned) =
        OverlapBelief.incomingEdges B (label v, banned) := by
      cases banned with
      | none => exact hInc
      | some e => exact congrArg (fun s => s.erase e) hInc
    rw [OverlapBelief.logIterate_succ A hu, OverlapBelief.logIterate_succ B hu, hIn, hWeight]
    unfold OverlapBelief.logUpdate
    apply congrArg (fun a => -Real.log (u+a))
    apply Finset.sum_congr rfl
    intro e he
    have hIe : e ∈ OverlapBelief.incidentEdges B (label v) := by
      cases banned with
      | none => exact he
      | some f => exact Finset.mem_of_mem_erase he
    obtain ⟨w,hw,hwDeep,hwEnd⟩ := hNext v hv (by omega) e hIe
    simp only [OverlapBelief.incomingState, hEnds, hwEnd, ih (some e) hw (by omega)]

private theorem activeEmbedded_next_slot {β d κ : ℝ} {C : CostArray} (D : ℕ)
    {v : List ℕ} (hv : v ∈ shape.slots) (hd : v.length < shape.depth)
    (e : Fin n × Fin n)
    (he : e ∈ OverlapBelief.incidentEdges (shape.embeddedTrimmedGraph root p β d κ D C)
      (ofLex (shape.placementLabel root p v))) :
    ∃ w ∈ shape.slots, w.length ≤ v.length + 1 ∧
      Tree.otherEnd (shape.embeddedTrimmedGraph root p β d κ D C).ends e
        (ofLex (shape.placementLabel root p v)) = ofLex (shape.placementLabel root p w) := by
  change e ∈ (trimDegrees D (shape.placementEdges root p)).filter
    (fun e => ofLex (shape.placementLabel root p v) ∈ Tree.Bipartite.ends e) at he
  obtain ⟨hE,hV⟩ := Finset.mem_filter.mp he
  exact shape.exists_slot_of_placementOtherEnd root p (β := β) (d := d) (κ := κ) (C := C)
    D hv hd (trimDegrees_subset D _ hE) hV

private theorem trimmed_incident_eq_embedded {β d κ R : ℝ} (hκ : 0 < κ)
    {C : CostArray} (hC : C ∈ shape.placementEvent root p (Iic (R / lengthScale d κ n)))
    (D : ℕ) (v : List ℕ) (hv : v ∈ shape.slots) (hd : v.length + 2 < shape.depth) :
    OverlapBelief.incidentEdges (trimmedAssignmentGraph β d κ R n D C)
        (ofLex (shape.placementLabel root p v)) =
      OverlapBelief.incidentEdges (shape.embeddedTrimmedGraph root p β d κ D C)
        (ofLex (shape.placementLabel root p v)) := by
  unfold OverlapBelief.incidentEdges
  exact shape.trimDegrees_incident_retained_eq_placement root p hκ hC D hv hd

private theorem trimmed_ends_eq_embedded (β d κ R : ℝ) (D : ℕ) (C : CostArray) :
    (trimmedAssignmentGraph β d κ R n D C).ends = (shape.embeddedTrimmedGraph root p β d κ D C).ends :=
  rfl

private theorem trimmed_weight_eq_embedded (β d κ R : ℝ) (D : ℕ) (C : CostArray) :
    (trimmedAssignmentGraph β d κ R n D C).weight = (shape.embeddedTrimmedGraph root p β d κ D C).weight :=
  rfl

/-- The first k log-BP updates around an interior slot are determined by
the embedded trimmed shape and its length marks. -/
theorem logIterate_trimmed_eq_embedded {β d κ R u : ℝ} (hκ : 0 < κ) (hu : 0 < u)
    {C : CostArray} (hC : C ∈ shape.placementEvent root p (Iic (R / lengthScale d κ n)))
    (D k : ℕ) (banned : Option (Fin n × Fin n))
    {v : List ℕ} (hv : v ∈ shape.slots) (hd : v.length + k + 1 < shape.depth) :
    OverlapBelief.logIterate (trimmedAssignmentGraph β d κ R n D C) u k
        (ofLex (shape.placementLabel root p v), banned) =
      OverlapBelief.logIterate (shape.embeddedTrimmedGraph root p β d κ D C) u k
        (ofLex (shape.placementLabel root p v), banned) := by
  exact shape.logIterate_eq_of_neighborhood
    (trimmedAssignmentGraph β d κ R n D C) (shape.embeddedTrimmedGraph root p β d κ D C)
    (fun w => ofLex (shape.placementLabel root p w)) hu
    (shape.trimmed_weight_eq_embedded root p β d κ R D C)
    (shape.trimmed_ends_eq_embedded root p β d κ R D C)
    (shape.trimmed_incident_eq_embedded root p (β := β) hκ hC D)
    (fun _ hv hd e he =>
      shape.activeEmbedded_next_slot root p (β := β) (d := d) (κ := κ) (C := C) D hv hd e he)
    k banned hv hd

end Certificate.LocalExploration.PlaneShape

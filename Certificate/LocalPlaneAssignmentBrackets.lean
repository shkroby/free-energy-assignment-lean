import Certificate.LocalPlaneAssignmentEvent
import Certificate.LocalTreeShapeMarks
import Certificate.LocalPlaneGraphBounds
import Certificate.LocalAssignmentBracketLimits

/-! A realized plane shape represents the original weighted assignment graph at its pinned root. -/

open Finset Set MeasureTheory
open scoped BoundedContinuousFunction

namespace Certificate.LocalExploration.PlaneShape

/-- The nested and flat representations index exactly the same parent edges. -/
def nonRootIndex (shape : PlaneShape) : shape.NonRootSlot ≃ PlaneNonrootSlot shape where
  toFun v := ⟨v.val.val, v.val.property, v.property⟩
  invFun v := ⟨⟨v.val, v.property.1⟩, v.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem ends_eq_of_endpoints {n : ℕ} {e : Fin n × Fin n} {u v : PlaneVertex n}
    (h : planeEdgeEndpoints u v e) : Tree.Bipartite.ends e = {ofLex u, ofLex v} := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact Finset.pair_comm _ _

private theorem eq_of_ends_eq {n : ℕ} {e f : Fin n × Fin n}
    (h : Tree.Bipartite.ends e = Tree.Bipartite.ends f) : e = f := by
  have hL : Sum.inl e.1 ∈ Tree.Bipartite.ends f :=
    h ▸ (by simp [Tree.Bipartite.ends] : Sum.inl e.1 ∈ Tree.Bipartite.ends e)
  have hR : Sum.inr e.2 ∈ Tree.Bipartite.ends f :=
    h ▸ (by simp [Tree.Bipartite.ends] : Sum.inr e.2 ∈ Tree.Bipartite.ends e)
  exact Prod.ext (by simpa [Tree.Bipartite.ends] using hL)
    (by simpa [Tree.Bipartite.ends] using hR)

private theorem retained_iff {n : ℕ} {κ : ℝ} (e : Fin n × Fin n) (hκ : 0 < κ)
    (root : Fin n) (C : CostArray) (d R : ℝ) :
    e ∈ retainedEdges d κ R n C ↔ planeRetainedPredicate C (Iic (R / lengthScale d κ n)) e := by
  have hs : 0 < lengthScale d κ n :=
    Real.rpow_pos_of_pos (mul_pos hκ (Nat.cast_pos.mpr root.isLt.pos)) _
  simp only [retainedEdges, mem_filter, Finset.mem_univ, true_and]
  change lengthScale d κ n * C (e.1.val, e.2.val) ≤ R ↔
    C (e.1.val, e.2.val) ≤ R / lengthScale d κ n
  rw [mul_comm, le_div_iff₀ hs]

/-- On the cylinder of an ordered graph placement both weighted brackets
are exactly the continuous test of its retained lengths. -/
theorem cutoffRootBounds_eq_shapeBracket (shape : PlaneShape) {n : ℕ} (root : Fin n)
    (p : shape.OrderedPlacement root) (β d κ R z : ℝ) (hκ : 0 < κ) {C : CostArray}
    (hC : C ∈ shape.placementEvent root p (Iic (R / lengthScale d κ n))) :
    let G := cutoffAssignmentGraph β d κ R n C
    Tree.finiteRootBounds G.ends G.edges G.weight z shape.depth G.vertices (Sum.inl root) =
      shape.shapeBracket β z (labelledNeighborhoodLengths d κ
        (shape.nonRootIndex.trans (shape.placementEdgeEquiv root p)) C) := by
  classical
  let A := Iic (R / lengthScale d κ n)
  let label := shape.placementLabel root p
  let halt := shape.placementLabel_alternates root p
  let marks := labelledNeighborhoodLengths d κ
    (shape.nonRootIndex.trans (shape.placementEdgeEquiv root p)) C
  let vLabel (v : List ℕ) : Fin n ⊕ Fin n := ofLex (label v)
  let slot (v : List ℕ) (i : Fin (shape.childCount v))
      (hv : v ∈ shape.slots) (hd : v.length < shape.depth) : PlaneNonrootSlot shape :=
    ⟨v ++ [i.val], (shape.child_mem ..).mpr ⟨hv, hd, i.isLt⟩, by simp⟩
  let edge (v : List ℕ) (i : Fin (shape.childCount v)) : Fin n × Fin n :=
    if h : v ∈ shape.slots ∧ v.length < shape.depth then
      planePlacementEdge halt (slot v i h.1 h.2) else (root, root)
  have hends (v : List ℕ) (hv : v ∈ shape.slots) (hd : v.length < shape.depth)
      (i : Fin (shape.childCount v)) :
      Tree.Bipartite.ends (edge v i) = {vLabel v, vLabel (v ++ [i.val])} := by
    have he := planePlacementEdge_endpoints halt (slot v i hv hd)
    have h := ends_eq_of_endpoints he
    rw [Finset.pair_comm] at h
    simpa only [edge, dif_pos (And.intro hv hd), slot, List.dropLast_concat, vLabel] using h
  have hmatch := (shape.mem_placementEvent_iff root p A C).mp hC
  have H : LocalEdges shape vLabel Tree.Bipartite.ends (retainedEdges d κ R n C)
      (fun e => Real.exp (-β * edgeLength d κ n C e)) β marks := by
    refine ⟨fun _ hv _ hw h => shape.placementLabel_injOn root p hv hw (congrArg toLex h),
      edge, ?_, hends, ?_, ?_⟩
    · intro v hv hd i
      apply (retained_iff (edge v i) hκ root C d R).mpr
      exact (hC.1 _ (Finset.mem_image.mpr ⟨slot v i hv hd, Finset.mem_univ _,
        by simp [edge, hv, hd]⟩)).1
    · intro v hv hd i
      have hs : v ++ [i.val] ∈ shape.slots := (slot v i hv hd).property.1
      simp only [shapeWeight, dif_pos hs, edge, dif_pos (And.intro hv hd)]
      rfl
    · intro v hv hd e he hm hp
      have hret := (retained_iff e hκ root C d R).mp he
      obtain ⟨w, hew, hne⟩ :
          ∃ w : PlaneVertex n, planeEdgeEndpoints (label v) w e ∧
            w ∉ planeParentLabels label v := by
        have hs : vLabel v = Sum.inl e.1 ∨ vLabel v = Sum.inr e.2 := by
          simpa [Tree.Bipartite.ends] using hm
        let noParent (w : PlaneVertex n) (hw : ofLex w ∈ Tree.Bipartite.ends e) :
            w ∉ planeParentLabels label v := by
          intro h
          by_cases hroot : v = []
          · simp [planeParentLabels, hroot] at h
          · have heq : w = label v.dropLast := by simpa [planeParentLabels, hroot] using h
            exact hp hroot (by simpa only [heq] using hw)
        rcases hs with hs | hs
        · exact ⟨toLex (Sum.inr e.2), Or.inl ⟨congrArg toLex hs, rfl⟩,
            noParent _ (by simp [Tree.Bipartite.ends])⟩
        · exact ⟨toLex (Sum.inl e.1), Or.inr ⟨congrArg toLex hs, rfl⟩,
            noParent _ (by simp [Tree.Bipartite.ends])⟩
      have hw : w ∈ planeBipartiteNeighbors (planeRetainedPredicate C A) (label v) \
          planeParentLabels label v := ⟨⟨e.1, e.2, hret, hew⟩, hne⟩
      have hj : planeBipartiteNeighbors (planeRetainedPredicate C A) (label v) \ planeParentLabels label v =
          planeChildLabels shape label v := (hmatch.2 v hv hd).2
      rw [hj] at hw
      obtain ⟨i, hi⟩ := hw
      refine ⟨i, eq_of_ends_eq ((hends v hv hd i).trans ?_)⟩
      rw [show vLabel (v ++ [i.val]) = ofLex w from congrArg ofLex hi]
      exact (ends_eq_of_endpoints hew).symm
  have hvroot : vLabel [] = Sum.inl root := congrArg ofLex (shape.placementLabel_root root p)
  have heq := finiteRootBounds_eq_shapeBracket H z Finset.univ (fun _ _ => Finset.mem_univ _)
  rw [hvroot] at heq
  exact heq

end Certificate.LocalExploration.PlaneShape

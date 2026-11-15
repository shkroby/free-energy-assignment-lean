import Certificate.OverlapTrim
import Certificate.LocalPlaneAssignmentEvent

/-!
# Degree trimming inside a realized plane neighborhood

A column's decision after the row trim needs the original degrees of
all its adjacent rows. Two spare levels beyond a vertex therefore
determine the trimmed edges incident to that vertex.
-/

open Finset Set
open scoped BigOperators

namespace Certificate.LocalExploration.PlaneShape

open Certificate.Overlap

variable {n : ℕ} (shape : PlaneShape) (root : Fin n) (p : shape.OrderedPlacement root)

private theorem retained_iff_cutoffTest {κ : ℝ} (hκ : 0 < κ) (root₀ : Fin n)
    (d R : ℝ) (C : CostArray) (e : Fin n × Fin n) :
    e ∈ retainedEdges d κ R n C ↔ planeRetainedPredicate C (Iic (R / lengthScale d κ n)) e := by
  have hs : 0 < lengthScale d κ n :=
    Real.rpow_pos_of_pos (mul_pos hκ (Nat.cast_pos.mpr root₀.isLt.pos)) _
  simp only [retainedEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  change lengthScale d κ n * C (e.1.val,e.2.val) ≤ R ↔
    C (e.1.val,e.2.val) ≤ R / lengthScale d κ n
  rw [mul_comm, le_div_iff₀ hs]

theorem retained_mem_iff_placementMem_of_tested {d κ R : ℝ} (hκ : 0 < κ)
    {C : CostArray} (hC : C ∈ shape.placementEvent root p (Iic (R / lengthScale d κ n)))
    {e : Fin n × Fin n}
    (he : e ∈ neighborhoodTestedEdges (shape.placementLeftInterior root p)
      (shape.placementRightInterior root p)) :
    e ∈ retainedEdges d κ R n C ↔ e ∈ shape.placementEdges root p := by
  rw [retained_iff_cutoffTest hκ root d R C e]
  constructor
  · intro he'
    by_contra hn
    exact hC.2 e (Finset.mem_sdiff.mpr ⟨he, hn⟩) he'
  · exact fun hm => (hC.1 e hm).1

private theorem retained_mem_iff_of_leftInterior {d κ R : ℝ} (hκ : 0 < κ)
    {C : CostArray} (hC : C ∈ shape.placementEvent root p (Iic (R / lengthScale d κ n)))
    {e : Fin n × Fin n} (he : e.1 ∈ shape.placementLeftInterior root p) :
    e ∈ retainedEdges d κ R n C ↔ e ∈ shape.placementEdges root p :=
  shape.retained_mem_iff_placementMem_of_tested root p hκ hC
    (by simp [neighborhoodTestedEdges, he])

private theorem retained_mem_iff_of_rightInterior {d κ R : ℝ} (hκ : 0 < κ)
    {C : CostArray} (hC : C ∈ shape.placementEvent root p (Iic (R / lengthScale d κ n)))
    {e : Fin n × Fin n} (he : e.2 ∈ shape.placementRightInterior root p) :
    e ∈ retainedEdges d κ R n C ↔ e ∈ shape.placementEdges root p :=
  shape.retained_mem_iff_placementMem_of_tested root p hκ hC
    (by simp [neighborhoodTestedEdges, he])

/-- An interior row has the same full row degree on the actual short-edge
graph and on the embedded untrimmed plane shape. -/
theorem rowEdges_retained_eq_placement {d κ R : ℝ} (hκ : 0 < κ)
    {C : CostArray} (hC : C ∈ shape.placementEvent root p (Iic (R / lengthScale d κ n)))
    {i : Fin n} (hi : i ∈ shape.placementLeftInterior root p) :
    rowEdges (retainedEdges d κ R n C) i = rowEdges (shape.placementEdges root p) i := by
  ext e
  by_cases h : e.1 = i
  · simp only [rowEdges, Finset.mem_filter, h, and_true]
    exact shape.retained_mem_iff_of_leftInterior root p hκ hC (h.symm ▸ hi)
  · simp [rowEdges,h]

/-- An interior column has the same full column degree on the actual
short-edge graph and on the embedded untrimmed plane shape. -/
theorem colEdges_retained_eq_placement {d κ R : ℝ} (hκ : 0 < κ)
    {C : CostArray} (hC : C ∈ shape.placementEvent root p (Iic (R / lengthScale d κ n)))
    {j : Fin n} (hj : j ∈ shape.placementRightInterior root p) :
    colEdges (retainedEdges d κ R n C) j = colEdges (shape.placementEdges root p) j := by
  ext e
  by_cases h : e.2 = j
  · simp only [colEdges, Finset.mem_filter, h, and_true]
    exact shape.retained_mem_iff_of_rightInterior root p hκ hC (h.symm ▸ hj)
  · simp [colEdges,h]

private theorem leftInterior_of_label {v : List ℕ} (hv : v ∈ shape.slots)
    (hd : v.length < shape.depth) {i : Fin n}
    (h : shape.placementLabel root p v = toLex (Sum.inl i)) :
    i ∈ shape.placementLeftInterior root p := by
  unfold placementLeftInterior
  exact (mem_planePlacementLeftInterior _ _ _).mpr ⟨v,hv,hd,h⟩

private theorem rightInterior_of_label {v : List ℕ} (hv : v ∈ shape.slots)
    (hd : v.length < shape.depth) {j : Fin n}
    (h : shape.placementLabel root p v = toLex (Sum.inr j)) :
    j ∈ shape.placementRightInterior root p := by
  unfold placementRightInterior
  exact (mem_planePlacementRightInterior _ _ _).mpr ⟨v,hv,hd,h⟩

/-- Each neighbor of an interior slot lies at its parent or a child slot. -/
theorem exists_slot_of_placementNeighbor {v : List ℕ} (hv : v ∈ shape.slots)
    (hd : v.length < shape.depth) {x : PlaneVertex n}
    (hx : x ∈ planeBipartiteNeighbors (fun e => e ∈ shape.placementEdges root p)
      (shape.placementLabel root p v)) :
    ∃ w ∈ shape.slots, shape.placementLabel root p w = x ∧ w.length ≤ v.length + 1 := by
  have heq : planeBipartiteNeighbors (fun e => e ∈ shape.placementEdges root p)
      (shape.placementLabel root p v) =
        planeParentLabels (shape.placementLabel root p) v ∪ planeChildLabels shape (shape.placementLabel root p) v :=
    planePlacementNeighbors_eq (shape.placementLabel_alternates root p)
      (shape.placementLabel_injOn root p) v hv hd
  rw [heq] at hx
  rcases hx with hp | hc
  · by_cases hnil : v = []
    · simp [planeParentLabels, hnil] at hp
    · have hlast := List.dropLast_append_getLast hnil
      have hP : v.dropLast ∈ shape.slots :=
        ((shape.child_mem ..).mp (hlast.symm ▸ hv)).1
      refine ⟨v.dropLast, hP, ?_, ?_⟩
      · exact (show x = shape.placementLabel root p v.dropLast by
          simpa only [planeParentLabels, if_neg hnil, mem_singleton_iff] using hp).symm
      · simp only [List.length_dropLast]
        omega
  · obtain ⟨i,hi⟩ := hc
    exact ⟨v ++ [i.val], (shape.child_mem ..).mpr ⟨hv,hd,i.isLt⟩, hi, by simp⟩

/-- For an interior column with one spare level, the entire post-row-trim
column agrees with the embedded shape, including its degree. -/
theorem colEdges_trimRows_retained_eq_placement {d κ R : ℝ} (hκ : 0 < κ)
    {C : CostArray} (hC : C ∈ shape.placementEvent root p (Iic (R / lengthScale d κ n)))
    (D : ℕ) {v : List ℕ} (hv : v ∈ shape.slots) (hd : v.length + 1 < shape.depth)
    {j : Fin n} (hj : shape.placementLabel root p v = toLex (Sum.inr j)) :
    colEdges (trimRows D (retainedEdges d κ R n C)) j =
      colEdges (trimRows D (shape.placementEdges root p)) j := by
  let S := retainedEdges d κ R n C
  let T := shape.placementEdges root p
  have hjI := shape.rightInterior_of_label root p hv (by omega) hj
  ext e
  by_cases he : e.2 = j
  · have hST : e ∈ S ↔ e ∈ T :=
      shape.retained_mem_iff_of_rightInterior root p hκ hC (he.symm ▸ hjI)
    by_cases hT : e ∈ T
    · have hx : toLex (Sum.inl e.1) ∈ planeBipartiteNeighbors (fun e => e ∈ T)
          (shape.placementLabel root p v) := by
        rw [hj, ← he, mem_planeBipartiteNeighbors_right_left]
        exact hT
      obtain ⟨w,hw, hwl, hdep⟩ := shape.exists_slot_of_placementNeighbor root p hv (by omega) hx
      have hrow := shape.rowEdges_retained_eq_placement root p hκ hC
        (shape.leftInterior_of_label root p hw (hdep.trans_lt hd) hwl)
      change e ∈ colEdges (trimRows D S) j ↔ e ∈ colEdges (trimRows D T) j
      simp only [colEdges, trimRows, Finset.mem_filter, he, and_true]
      exact and_congr hST (Iff.of_eq (congrArg (fun a : Finset (Fin n × Fin n) => a.card ≤ D) hrow))
    · have hS : e ∉ S := fun hs => hT (hST.mp hs)
      change e ∈ colEdges (trimRows D S) j ↔ e ∈ colEdges (trimRows D T) j
      simp [colEdges,trimRows,hT,hS]
  · simp [colEdges,he]

/-- Interior endpoints with the required spare levels decide whether the
edge survives both passes of degree trimming. -/
theorem mem_trimDegrees_retained_iff_placement_of_slots {d κ R : ℝ} (hκ : 0 < κ)
    {C : CostArray} (hC : C ∈ shape.placementEvent root p (Iic (R / lengthScale d κ n)))
    (D : ℕ) {v w : List ℕ} (hv : v ∈ shape.slots) (hw : w ∈ shape.slots)
    (hdv : v.length < shape.depth) (hdw : w.length + 1 < shape.depth)
    {e : Fin n × Fin n}
    (hrow : shape.placementLabel root p v = toLex (Sum.inl e.1))
    (hcol : shape.placementLabel root p w = toLex (Sum.inr e.2)) :
    e ∈ trimDegrees D (retainedEdges d κ R n C) ↔
      e ∈ trimDegrees D (shape.placementEdges root p) := by
  have hvI := shape.leftInterior_of_label root p hv hdv hrow
  simp only [trimDegrees, Finset.mem_filter]
  have hRows (S : Finset (Fin n × Fin n)) :
      e ∈ trimRows D S ↔ e ∈ S ∧ (rowEdges S e.1).card ≤ D := Finset.mem_filter
  simp only [hRows]
  rw [shape.retained_mem_iff_of_leftInterior root p hκ hC hvI,
    shape.rowEdges_retained_eq_placement root p hκ hC hvI,
    shape.colEdges_trimRows_retained_eq_placement root p hκ hC D hw hdw hcol]

private theorem tested_of_incident_label {v : List ℕ} (hv : v ∈ shape.slots)
    (hd : v.length < shape.depth) {e : Fin n × Fin n}
    (he : ofLex (shape.placementLabel root p v) ∈ Tree.Bipartite.ends e) :
    e ∈ neighborhoodTestedEdges (shape.placementLeftInterior root p)
      (shape.placementRightInterior root p) := by
  have h : ofLex (shape.placementLabel root p v) = Sum.inl e.1 ∨
      ofLex (shape.placementLabel root p v) = Sum.inr e.2 := by
    simpa [Tree.Bipartite.ends] using he
  rcases h with h | h
  · have hl := shape.leftInterior_of_label root p hv hd (congrArg toLex h)
    simp [neighborhoodTestedEdges,hl]
  · have hr := shape.rightInterior_of_label root p hv hd (congrArg toLex h)
    simp [neighborhoodTestedEdges,hr]

/-- The actual degree-trimmed graph and the embedded degree-trimmed
shape have equal incident edge sets at any slot with two spare levels. -/
theorem trimDegrees_incident_retained_eq_placement {d κ R : ℝ} (hκ : 0 < κ)
    {C : CostArray} (hC : C ∈ shape.placementEvent root p (Iic (R / lengthScale d κ n)))
    (D : ℕ) {v : List ℕ} (hv : v ∈ shape.slots) (hd : v.length + 2 < shape.depth) :
    (trimDegrees D (retainedEdges d κ R n C)).filter
        (fun e => ofLex (shape.placementLabel root p v) ∈ Tree.Bipartite.ends e) =
      (trimDegrees D (shape.placementEdges root p)).filter
        (fun e => ofLex (shape.placementLabel root p v) ∈ Tree.Bipartite.ends e) := by
  ext e
  simp only [Finset.mem_filter]
  by_cases hvE : ofLex (shape.placementLabel root p v) ∈ Tree.Bipartite.ends e
  · simp only [hvE, and_true]
    have ht := shape.tested_of_incident_label root p hv (by omega) hvE
    have hST := shape.retained_mem_iff_placementMem_of_tested root p hκ hC ht
    by_cases hT : e ∈ shape.placementEdges root p
    · have hSide : ofLex (shape.placementLabel root p v) = Sum.inl e.1 ∨
          ofLex (shape.placementLabel root p v) = Sum.inr e.2 := by
        simpa [Tree.Bipartite.ends] using hvE
      rcases hSide with hSide | hSide
      · have hL : shape.placementLabel root p v = toLex (Sum.inl e.1) := congrArg toLex hSide
        have hup : toLex (Sum.inr e.2) ∈ planeBipartiteNeighbors
            (fun a => a ∈ shape.placementEdges root p) (shape.placementLabel root p v) := by
          rwa [hL, mem_planeBipartiteNeighbors_left_right]
        obtain ⟨w,hw,hR,hdeep⟩ := shape.exists_slot_of_placementNeighbor root p hv (by omega) hup
        exact shape.mem_trimDegrees_retained_iff_placement_of_slots root p hκ hC D
          hv hw (by omega) (by omega) hL hR
      · have hR : shape.placementLabel root p v = toLex (Sum.inr e.2) := congrArg toLex hSide
        have hup : toLex (Sum.inl e.1) ∈ planeBipartiteNeighbors
            (fun a => a ∈ shape.placementEdges root p) (shape.placementLabel root p v) := by
          rwa [hR, mem_planeBipartiteNeighbors_right_left]
        obtain ⟨w,hw,hL,hdeep⟩ := shape.exists_slot_of_placementNeighbor root p hv (by omega) hup
        exact shape.mem_trimDegrees_retained_iff_placement_of_slots root p hκ hC D
          hw hv (by omega) (by omega) hL hR
    · exact ⟨fun h => (hT (hST.mp (trimDegrees_subset _ _ h))).elim,
        fun h => (hT (trimDegrees_subset _ _ h)).elim⟩
  · simp [hvE]

/-- The reference trimmed graph, using only the edges of the embedded
plane shape and retaining the original assignment weights. -/
noncomputable def embeddedTrimmedGraph (β d κ : ℝ) (D : ℕ) (C : CostArray) :
    WeightedGraph (Fin n ⊕ Fin n) (Fin n × Fin n) :=
  (assignmentGraph β d κ n C).retain (trimDegrees D (shape.placementEdges root p)) (Finset.subset_univ _)


end Certificate.LocalExploration.PlaneShape

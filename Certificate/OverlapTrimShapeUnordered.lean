import Certificate.OverlapTrimShapeChildMasks
import Certificate.OverlapUnorderedShape
import Certificate.OverlapUnorderedThird
import Certificate.OverlapTrimShapeTests

/-! The upward messages on the symbolic trimmed shape agree with the
messages on its unordered marked encoding. -/

open Finset Set
open scoped BigOperators

namespace Certificate.LocalExploration.PlaneShape

open Certificate.OverlapBelief Certificate.UnorderedTree

variable (shape : PlaneShape)

private noncomputable def below (marks : shape.NonRootSlot → ℝ) (k : ℕ) (v : List ℕ) : Depth k :=
  ofChildren shape.childCount (shape.childLength marks) k v

private theorem below_succ (marks : shape.NonRootSlot → ℝ) (k : ℕ) (v : List ℕ) :
    shape.below marks (k+1) v = node (shape.childCount v)
      (fun i => (shape.childLength marks v i.val, shape.below marks k (v ++ [i.val]))) := rfl

private theorem rowDegree_below (marks : shape.NonRootSlot → ℝ) (k : ℕ) (hk : 0 < k) (v : List ℕ) :
    rowDegree k (shape.below marks k v) = 1 + shape.childCount v := by
  cases k with
  | zero => omega
  | succ k => simp only [below_succ,rowDegree,childCount_node]

private theorem reachedColumnDegree_below (D : ℕ) (marks : shape.NonRootSlot → ℝ)
    (k : ℕ) (hk : 2 ≤ k) (v : List ℕ) :
    reachedColumnDegree D k (shape.below marks k v) = 1 +
      (Finset.univ.filter (fun i : Fin (shape.childCount v) => 1 + shape.childCount (v ++ [i.val]) ≤ D)).card := by
  classical
  cases k with
  | zero => omega
  | succ k =>
    have hk' : 0 < k := by omega
    simp only [below_succ,reachedColumnDegree,countChildrenWhere,sumChildren_node,
      shape.rowDegree_below marks k hk']
    rw [← Finset.sum_filter]
    simp

private theorem shapeChild_admitted_iff (D : ℕ) (marks : shape.NonRootSlot → ℝ)
    (k : ℕ) (hk : 2 ≤ k) (v : shape.Slot) (hv : v.val.length + 2 < shape.depth)
    (hReach : shape.TrimReached D v) (i : Fin (shape.childCount v.val)) :
    shape.childEdgeOf v (by omega) i ∈ shape.shapeTrimDegrees D ↔
      childAdmitted D (decide (v.val.length % 2 = 0)) k
        (shape.below marks k (v.val ++ [i.val])) := by
  rw [shape.childEdge_mem_trim_of_reached D v hv hReach i]
  unfold childAdmitted
  by_cases h : v.val.length % 2 = 0
  · have hb : decide (v.val.length % 2 = 0) = true := decide_eq_true h
    rw [if_pos h,hb]
    change _ ↔ reachedColumnDegree D k (shape.below marks k (v.val ++ [i.val])) ≤ D
    rw [shape.reachedColumnDegree_below D marks k hk]
  · have hb : decide (v.val.length % 2 = 0) = false := decide_eq_false_iff_not.mpr h
    rw [if_neg h,hb]
    change _ ↔ rowDegree k (shape.below marks k (v.val ++ [i.val])) ≤ D
    rw [shape.rowDegree_below marks k (by omega)]

/-- An upward message on the trimmed finite graph is the corresponding
unordered recurrence at all interior slots reached by retained edges. -/
theorem exp_childLogIterate_eq_unordered (D : ℕ) (β : ℝ) {u : ℝ} (hu : 0 < u)
    (marks : shape.NonRootSlot → ℝ) (s k : ℕ) (v : shape.Slot)
    (hks : s + 2 ≤ k) (hdep : k + v.val.length ≤ shape.depth)
    (hReach : shape.TrimReached D v) :
    Real.exp (shape.childLogIterate D β u marks s v) =
      upwardIterate D β u k s (decide (v.val.length % 2 = 0)) (shape.below marks k v.val) := by
  classical
  induction s generalizing k v with
  | zero =>
    cases k with
    | zero => omega
    | succ k => simp [childLogIterate,upwardIterate,Real.exp_neg,Real.exp_log hu]
  | succ s ih =>
    cases k with
    | zero => omega
    | succ k =>
      have hk : s + 2 ≤ k := by omega
      have hd : v.val.length + 2 < shape.depth := by omega
      have hv : v.val.length < shape.depth := by omega
      let G := shape.symbolicTrimmedGraph D β marks
      let e := shape.childEdgeOf v hv
      let χ (i : Fin (shape.childCount v.val)) :=
        (shape.childLength marks v.val i.val, shape.below marks k (v.val ++ [i.val]))
      let A (j : PlaneNonrootSlot shape) :=
        G.weight j * Real.exp (shape.childLogIterate D β u marks s (shape.edgeChild j))
      have hsum :
          ∑ j ∈ shape.retainedChildEdges D v, A j =
            ∑ i : Fin (shape.childCount v.val), if e i ∈ shape.shapeTrimDegrees D then A (e i) else 0 := by
        unfold retainedChildEdges
        rw [shape.filter_edgeParent_eq_image _ v hv, Finset.sum_image
          (fun _ _ _ _ h => shape.childEdgeOf_injective v hv h), Finset.sum_filter]
      have hpos :
          0 < u + ∑ j ∈ shape.retainedChildEdges D v, A j :=
        lt_of_lt_of_le hu (le_add_of_nonneg_right (Finset.sum_nonneg fun j _ =>
          mul_nonneg (G.weight_nonneg j) (Real.exp_nonneg _)))
      rw [childLogIterate, logUpdate, Real.exp_neg, Real.exp_log hpos]
      simp only [upwardIterate, shape.below_succ marks k v.val, sumChildren_node]
      change (u + ∑ j ∈ shape.retainedChildEdges D v, A j)⁻¹ = _
      rw [hsum]
      apply congrArg (fun z : ℝ => (u+z)⁻¹)
      apply Finset.sum_congr rfl
      intro i _
      have hAdmit := shape.shapeChild_admitted_iff D marks k (by omega) v hd hReach i
      change e i ∈ shape.shapeTrimDegrees D ↔
        childAdmitted D (decide (v.val.length % 2 = 0)) k (χ i).2 at hAdmit
      change (if e i ∈ shape.shapeTrimDegrees D then A (e i) else 0) =
        (if childAdmitted D (decide (v.val.length % 2 = 0)) k (χ i).2 then
          Real.exp (-β * (χ i).1) *
            upwardIterate D β u k s (!(decide (v.val.length % 2 = 0))) (χ i).2 else 0)
      by_cases he : e i ∈ shape.shapeTrimDegrees D
      · have he' := hAdmit.mp he
        simp only [if_pos he, if_pos he']
        have hW : G.weight (e i) = Real.exp (-β * (χ i).1) := by
          have hslot : v.val ++ [i.val] ∈ shape.slots := (e i).property.1
          change Real.exp (-β * marks (shape.nonRootIndex.symm (e i))) =
            Real.exp (-β * shape.childLength marks v.val i.val)
          rw [childLength, dif_pos hslot]
          rfl
        have hchild : (shape.edgeChild (e i)).val = v.val ++ [i.val] := rfl
        have hlen : (shape.edgeChild (e i)).val.length = v.val.length + 1 := by simp [hchild]
        have hSide : decide ((shape.edgeChild (e i)).val.length % 2 = 0) =
            !(decide (v.val.length % 2 = 0)) := by
          by_cases hvp : v.val.length % 2 = 0
          · have hwp : (shape.edgeChild (e i)).val.length % 2 ≠ 0 := by omega
            simp [hvp,hwp]
          · have hwp : (shape.edgeChild (e i)).val.length % 2 = 0 := by omega
            simp [hvp,hwp]
        have hm := ih k (shape.edgeChild (e i)) hk (by omega) (shape.trimReached_of_kept D _ he)
        rw [hSide,hchild] at hm
        exact congrArg₂ (· * ·) hW hm
      · have he' : ¬childAdmitted D (decide (v.val.length % 2 = 0)) k (χ i).2 :=
          fun h => he (hAdmit.mpr h)
        simp only [if_neg he, if_neg he']

private def rootVertex : shape.Slot := ⟨[],shape.root_mem⟩

private noncomputable def rootEntries (marks : shape.NonRootSlot → ℝ) (k : ℕ)
    (i : Fin (shape.childCount [])) : ℝ × Depth k :=
  (shape.childLength marks [] i.val, shape.below marks k [i.val])

private theorem rootNode_eq_encodeUnorderedAt (marks : shape.NonRootSlot → ℝ)
    (k : ℕ) (hk : shape.depth = k+1) :
    node (shape.childCount []) (shape.rootEntries marks k) = shape.encodeUnorderedAt hk marks := by
  change shape.below marks (k+1) [] = _
  unfold encodeUnorderedAt encodeUnordered
  have h (j l : ℕ) (e : j = l) : (e ▸ shape.below marks j []) = shape.below marks l [] := by
    subst l
    rfl
  exact (h _ _ hk).symm

private theorem rootChildTerm_eq_trimmed (D : ℕ) (β : ℝ) {u : ℝ} (hu : 0 < u)
    (marks : shape.NonRootSlot → ℝ) (s k : ℕ) (hk : s+2 ≤ k) (hdepth : shape.depth = k+1)
    (hRoot : shape.childCount [] ≤ D) (i : Fin (shape.childCount [])) :
    let v := shape.rootVertex
    let e := shape.childEdgeOf v (by change 0 < shape.depth; omega) i
    let G := shape.symbolicTrimmedGraph D β marks
    rootChildTerm D β u k s (shape.rootEntries marks k i) =
      if e ∈ shape.shapeTrimDegrees D then
        G.weight e * Real.exp (shape.childLogIterate D β u marks s (shape.edgeChild e)) else 0 := by
  classical
  dsimp only
  let v := shape.rootVertex
  let e := shape.childEdgeOf v (by change 0 < shape.depth; omega) i
  let G := shape.symbolicTrimmedGraph D β marks
  have hV : v.val = [] := rfl
  have hdep : v.val.length + 2 < shape.depth := by simp only [hV,List.length_nil,zero_add]; omega
  have hReach : shape.TrimReached D v := Or.inl ⟨hV,hRoot⟩
  have hA := shape.shapeChild_admitted_iff D marks k (by omega) v hdep hReach i
  change e ∈ shape.shapeTrimDegrees D ↔ childAdmitted D true k (shape.rootEntries marks k i).2 at hA
  change rootChildTerm D β u k s (shape.rootEntries marks k i) =
    (if e ∈ shape.shapeTrimDegrees D then
      G.weight e * Real.exp (shape.childLogIterate D β u marks s (shape.edgeChild e)) else 0)
  by_cases he : e ∈ shape.shapeTrimDegrees D
  · have he' := hA.mp he
    simp only [rootChildTerm, if_pos he, if_pos he']
    let c := shape.edgeChild e
    have hC : c.val = [i.val] := rfl
    have hlen : c.val.length = 1 := by rw [hC]; simp
    have hM := shape.exp_childLogIterate_eq_unordered D β hu marks s k c hk
      (by omega) (shape.trimReached_of_kept D e he)
    have hfalse : decide (c.val.length % 2 = 0) = false := by simp [hlen]
    rw [hfalse,hC] at hM
    have hW : G.weight e = Real.exp (-β*(shape.rootEntries marks k i).1) := by
      change Real.exp (-β*marks (shape.nonRootIndex.symm e)) =
        Real.exp (-β*shape.childLength marks [] i.val)
      have hslot : [] ++ [i.val] ∈ shape.slots := e.property.1
      rw [childLength, dif_pos hslot]
      rfl
    exact congrArg₂ (· * ·) hW.symm hM.symm
  · have he' : ¬childAdmitted D true k (shape.rootEntries marks k i).2 := fun h => he (hA.mpr h)
    simp only [rootChildTerm, if_neg he, if_neg he']

private theorem retainedChildEdges_root_eq_incident (D : ℕ) (β : ℝ) (marks : shape.NonRootSlot → ℝ) :
    shape.retainedChildEdges D shape.rootVertex =
      incidentEdges (shape.symbolicTrimmedGraph D β marks) shape.rootVertex := by
  have he : shape.parentEdge shape.rootVertex = none := by simp [parentEdge,rootVertex]
  exact (shape.symbolicTrimmedGraph_incoming_parent D β marks shape.rootVertex ▸
    (by rw [he]; rfl :
      incomingEdges (shape.symbolicTrimmedGraph D β marks) (shape.rootVertex, shape.parentEdge shape.rootVertex) =
        incidentEdges (shape.symbolicTrimmedGraph D β marks) shape.rootVertex))

private theorem rootChild_exclusion_eq_symbolic (D : ℕ) (β : ℝ) {u : ℝ} (hu : 0 < u)
    (marks : shape.NonRootSlot → ℝ) (s k : ℕ) (hk : s+2 ≤ k) (hdepth : shape.depth = k+1)
    (hRoot : shape.childCount [] ≤ D) (i : Fin (shape.childCount []))
    (he : shape.childEdgeOf shape.rootVertex (by change 0 < shape.depth; omega) i ∈
      shape.shapeTrimDegrees D) :
    rootExcluding D β u k s (node (shape.childCount []) (shape.rootEntries marks k))
        (shape.rootEntries marks k i) =
      Real.exp (logIterate (shape.symbolicTrimmedGraph D β marks) u s
        (shape.rootVertex, some (shape.childEdgeOf shape.rootVertex (by change 0 < shape.depth; omega) i))) := by
  classical
  cases s with
  | zero => simp [rootExcluding,logIterate,Real.exp_neg,Real.exp_log hu]
  | succ s =>
    let G := shape.symbolicTrimmedGraph D β marks
    let v := shape.rootVertex
    have hv : v.val.length < shape.depth := by change 0 < shape.depth; omega
    let e := shape.childEdgeOf v hv
    let S := shape.retainedChildEdges D v
    let A (j : PlaneNonrootSlot shape) :=
      G.weight j * Real.exp (shape.childLogIterate D β u marks s (shape.edgeChild j))
    have heS : e i ∈ S := Finset.mem_filter.mpr ⟨he,shape.edgeParent_childEdgeOf v hv i⟩
    have hsum :
        ∑ j ∈ S,A j = sumChildren (rootChildTerm D β u k s)
          (node (shape.childCount []) (shape.rootEntries marks k)) := by
      rw [sumChildren_node]
      change ∑ j ∈ (shape.shapeTrimDegrees D).filter (fun j => shape.edgeParent j = v), A j = _
      rw [shape.filter_edgeParent_eq_image _ v hv, Finset.sum_image
        (fun _ _ _ _ h => shape.childEdgeOf_injective v hv h), Finset.sum_filter]
      exact Finset.sum_congr rfl fun j _ =>
        (shape.rootChildTerm_eq_trimmed D β hu marks s k (by omega) hdepth hRoot j).symm
    have hTerm := shape.rootChildTerm_eq_trimmed D β hu marks s k (by omega) hdepth hRoot i
    change rootChildTerm D β u k s (shape.rootEntries marks k i) =
      (if e i ∈ shape.shapeTrimDegrees D then A (e i) else 0) at hTerm
    rw [if_pos he] at hTerm
    have hErase : (∑ j ∈ S.erase (e i), A j) + A (e i) = ∑ j ∈ S,A j :=
      Finset.sum_erase_add _ _ heS
    have hInc : incomingEdges G (v,some (e i)) = S.erase (e i) :=
      congrArg (fun T => T.erase (e i))
        (shape.retainedChildEdges_root_eq_incident D β marks).symm
    have hMsg :
        ∑ j ∈ S.erase (e i), G.weight j * Real.exp (logIterate G u s (incomingState G v j)) =
          ∑ j ∈ S.erase (e i), A j := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjv : shape.edgeParent j = v :=
        (Finset.mem_filter.mp (Finset.mem_of_mem_erase hj)).2
      have hOther : Tree.otherEnd G.ends j v = shape.edgeChild j := by
        rw [← hjv]
        exact otherEnd_of_endpoints G (shape.symbolicTrimmedGraph_ends D β marks j)
          (shape.edgeParent_ne_child j)
      have hPrev : shape.parentEdge (shape.edgeChild j) = some j :=
        (shape.parentEdge_eq_some_iff _ _).mpr rfl
      have hm : logIterate G u s (shape.edgeChild j,shape.parentEdge (shape.edgeChild j)) =
          shape.childLogIterate D β u marks s (shape.edgeChild j) :=
        shape.symbolicTrimmedGraph_logIterate_parent D β hu marks s (shape.edgeChild j)
      simp only [A,incomingState,hOther,← hPrev,hm]
    have hPos : 0 < u + ∑ j ∈ S.erase (e i), A j :=
      lt_of_lt_of_le hu (le_add_of_nonneg_right (Finset.sum_nonneg fun j _ =>
        mul_nonneg (G.weight_nonneg j) (Real.exp_nonneg _)))
    change rootExcluding D β u k (s+1) _ _ = Real.exp (logIterate G u (s+1) (v,some (e i)))
    rw [logIterate_succ G hu, hInc, logUpdate, hMsg, Real.exp_neg,Real.exp_log hPos,rootExcluding,
      hTerm,← hsum,← hErase]
    congr 1
    ring

private theorem rootChildOccupation_eq_symbolic (D : ℕ) (β : ℝ) {u : ℝ} (hu : 0 < u)
    (marks : shape.NonRootSlot → ℝ) (s k : ℕ) (hk : s+2 ≤ k) (hdepth : shape.depth = k+1)
    (i : Fin (shape.childCount [])) :
    let v := shape.rootVertex
    let G := shape.symbolicTrimmedGraph D β marks
    let e := shape.childEdgeOf v (by change 0 < shape.depth; omega) i
    rootChildOccupation D β u k s (node (shape.childCount []) (shape.rootEntries marks k))
        (shape.rootEntries marks k i) =
      if e ∈ shape.shapeTrimDegrees D then incidentOccupationIterate G u s v e else 0 := by
  classical
  dsimp only
  let v := shape.rootVertex
  let G := shape.symbolicTrimmedGraph D β marks
  have hv : v.val.length < shape.depth := by change 0 < shape.depth; omega
  let e := shape.childEdgeOf v hv i
  let c := shape.edgeChild e
  let x := shape.rootEntries marks k
  let t := node (shape.childCount []) x
  have hV : v.val = [] := rfl
  have hdep : v.val.length + 2 < shape.depth := by simp only [hV,List.length_nil,zero_add]; omega
  have hC : c.val = [i.val] := rfl
  have hlen : c.val.length = 1 := by simp [hC]
  have hT : UnorderedTree.childCount t = shape.childCount [] := childCount_node x
  change rootChildOccupation D β u k s t (x i) =
    (if e ∈ shape.shapeTrimDegrees D then incidentOccupationIterate G u s v e else 0)
  by_cases hR : shape.childCount [] ≤ D
  · have hReach : shape.TrimReached D v := Or.inl ⟨hV,hR⟩
    have hA := shape.shapeChild_admitted_iff D marks k (by omega) v hdep hReach i
    change e ∈ shape.shapeTrimDegrees D ↔ childAdmitted D true k (x i).2 at hA
    by_cases he : e ∈ shape.shapeTrimDegrees D
    · have he' := hA.mp he
      simp only [rootChildOccupation,hT,hR,he,he',and_self,if_true]
      have hRmsg := shape.rootChild_exclusion_eq_symbolic D β hu marks s k hk hdepth hR i he
      change rootExcluding D β u k s t (x i) =
        Real.exp (logIterate G u s (v,some e)) at hRmsg
      have hM := shape.exp_childLogIterate_eq_unordered D β hu marks s k c hk
        (by omega) (shape.trimReached_of_kept D e he)
      have hfalse : decide (c.val.length % 2 = 0) = false := by simp [hlen]
      rw [hfalse,hC] at hM
      change Real.exp (shape.childLogIterate D β u marks s c) =
        upwardIterate D β u k s false (x i).2 at hM
      have hP : shape.edgeParent e = v := shape.edgeParent_childEdgeOf v hv i
      have hOpp : Tree.otherEnd G.ends e v = c := by
        rw [← hP]
        exact otherEnd_of_endpoints G (shape.symbolicTrimmedGraph_ends D β marks e)
          (shape.edgeParent_ne_child e)
      have hPrev : shape.parentEdge c = some e := (shape.parentEdge_eq_some_iff _ _).mpr rfl
      have hMsg : logIterate G u s (incomingState G v e) = shape.childLogIterate D β u marks s c := by
        unfold incomingState
        rw [hOpp,← hPrev]
        exact shape.symbolicTrimmedGraph_logIterate_parent D β hu marks s c
      have hW : G.weight e = Real.exp (-β*(x i).1) := by
        change Real.exp (-β*marks (shape.nonRootIndex.symm e)) =
          Real.exp (-β*shape.childLength marks [] i.val)
        have hslot : [] ++ [i.val] ∈ shape.slots := e.property.1
        rw [childLength, dif_pos hslot]
        rfl
      rw [incidentOccupationIterate, hW, hMsg, hM, hRmsg]
    · have hn : ¬childAdmitted D true k (x i).2 := fun h => he (hA.mpr h)
      simp [rootChildOccupation,hT,he,hn]
  · have he : e ∉ shape.shapeTrimDegrees D := by
      intro he
      have hEL : e.val.length = 1 := hlen
      have hOdd : e.val.length % 2 = 1 := by omega
      have hRow := (shape.shapeEdgeRow_eq_of_odd_child hOdd).trans (shape.edgeParent_childEdgeOf v hv i)
      have hm := (shape.mem_shapeTrimRows D e).mp ((shape.mem_shapeTrimDegrees D e).mp he).1
      have hvEven : v.val.length % 2 = 0 := by simp [hV]
      rw [hRow,shape.rawRowDegree_eq_childCount v hv hvEven,if_pos hV,Nat.add_zero,hV] at hm
      exact hR hm
    simp [rootChildOccupation,hT,hR,he]

/-- The finite symbolic trimmed square statistic is the corresponding
symmetric statistic of its unordered marked encoding. -/
theorem squareRowTest_symbolic_eq_unordered (D : ℕ) (β : ℝ) {u : ℝ} (hu : 0 < u)
    (marks : shape.NonRootSlot → ℝ) (s : ℕ) (hdepth : shape.depth = s+3) :
    let v : shape.Slot := ⟨[],shape.root_mem⟩
    let G := shape.symbolicTrimmedGraph D β marks
    Overlap.squareRowTest (incidentEdges G v) (incidentOccupationIterate G u s v) =
      rootSquare D β u (s+2) s (shape.encodeUnorderedAt hdepth marks) := by
  classical
  let k := s+2
  let G := shape.symbolicTrimmedGraph D β marks
  let v := shape.rootVertex
  have hv : v.val.length < shape.depth := by change 0 < shape.depth; omega
  let e := shape.childEdgeOf v hv
  let x := shape.rootEntries marks k
  change Overlap.squareRowTest (incidentEdges G v) (incidentOccupationIterate G u s v) =
    rootSquare D β u k s (shape.encodeUnorderedAt hdepth marks)
  rw [← shape.rootNode_eq_encodeUnorderedAt marks k hdepth]
  unfold Overlap.squareRowTest rootSquare
  simp only [sumChildren_node]
  apply congrArg (min (1:ℝ))
  rw [← shape.retainedChildEdges_root_eq_incident D β marks]
  change ∑ a ∈ (shape.shapeTrimDegrees D).filter (fun a => shape.edgeParent a = v),
      (incidentOccupationIterate G u s v a)^2 =
    ∑ i : Fin (shape.childCount []), (rootChildOccupation D β u k s (node (shape.childCount []) x) (x i))^2
  rw [shape.filter_edgeParent_eq_image _ v hv, Finset.sum_image
    (fun _ _ _ _ h => shape.childEdgeOf_injective v hv h), Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  rw [shape.rootChildOccupation_eq_symbolic D β hu marks s k le_rfl hdepth i]
  change (if e i ∈ shape.shapeTrimDegrees D then (incidentOccupationIterate G u s v (e i))^2 else 0) =
    (if e i ∈ shape.shapeTrimDegrees D then incidentOccupationIterate G u s v (e i) else 0)^2
  by_cases he : e i ∈ shape.shapeTrimDegrees D
  · simp only [if_pos he]
  · simp only [if_neg he,zero_pow (by decide : (2:ℕ) ≠ 0)]

private theorem thirdOccupation_filter_eq_of_nonpos {E : Type*} [DecidableEq E]
    (a : E → ℝ) (S : Finset E) (q : E → Prop) [DecidablePred q] (hq : ∀ e ∈ S, ¬q e → a e ≤ 0) :
    Overlap.thirdOccupation (S.filter q) a = Overlap.thirdOccupation S a := by
  have h (η : ℝ) (hη : 0 < η) :
      η ≤ Overlap.thirdOccupation (S.filter q) a ↔ η ≤ Overlap.thirdOccupation S a := by
    rw [← Overlap.threeLargeOn_iff_le_thirdOccupation hη, ← Overlap.threeLargeOn_iff_le_thirdOccupation hη]
    constructor
    · rintro ⟨i,hi,j,hj,k,hk,hij,hik,hjk,hai,haj,hak⟩
      exact ⟨i,(Finset.mem_filter.mp hi).1,j,(Finset.mem_filter.mp hj).1,k,(Finset.mem_filter.mp hk).1,
        hij,hik,hjk,hai,haj,hak⟩
    · rintro ⟨i,hi,j,hj,k,hk,hij,hik,hjk,hai,haj,hak⟩
      have hk' (e) (he : e ∈ S) (ha : η ≤ a e) : e ∈ S.filter q := by
        refine Finset.mem_filter.mpr ⟨he,?_⟩
        by_contra hn
        exact (not_le_of_gt hη) (ha.trans (hq e he hn))
      exact ⟨i,hk' i hi hai,j,hk' j hj haj,k,hk' k hk hak,hij,hik,hjk,hai,haj,hak⟩
  have hA : 0 ≤ Overlap.thirdOccupation (S.filter q) a := NNReal.coe_nonneg _
  have hB : 0 ≤ Overlap.thirdOccupation S a := NNReal.coe_nonneg _
  by_contra hn
  rcases lt_or_gt_of_ne hn with hlt | hgt
  · have hη := h _ (hA.trans_lt hlt)
    exact (not_le_of_gt hlt) (hη.mpr le_rfl)
  · have hη := h _ (hB.trans_lt hgt)
    exact (not_le_of_gt hgt) (hη.mp le_rfl)

/-- The symbolic finite third occupation is the corresponding rational
threshold statistic of its unordered marks. -/
theorem thirdOccupation_symbolic_eq_unordered (D : ℕ) (β : ℝ) {u : ℝ} (hu : 0 < u)
    (marks : shape.NonRootSlot → ℝ) (s : ℕ) (hdepth : shape.depth = s+3) :
    let v : shape.Slot := ⟨[],shape.root_mem⟩
    let G := shape.symbolicTrimmedGraph D β marks
    Overlap.thirdOccupation (incidentEdges G v) (incidentOccupationIterate G u s v) =
      rootThird D β u (s+2) s (shape.encodeUnorderedAt hdepth marks) := by
  classical
  let k := s+2
  let G := shape.symbolicTrimmedGraph D β marks
  let v := shape.rootVertex
  have hv : v.val.length < shape.depth := by change 0 < shape.depth; omega
  let e := shape.childEdgeOf v hv
  let x := shape.rootEntries marks k
  let F (i : Fin (shape.childCount v.val)) := rootChildOccupation D β u k s (node (shape.childCount []) x) (x i)
  let A := incidentOccupationIterate G u s v
  let S : Finset (Fin (shape.childCount v.val)) :=
    Finset.univ.filter (fun i => shape.childEdgeOf v hv i ∈ shape.shapeTrimDegrees D)
  have hF (i : Fin (shape.childCount v.val)) : F i =
      if e i ∈ shape.shapeTrimDegrees D then A (e i) else 0 :=
    shape.rootChildOccupation_eq_symbolic D β hu marks s k le_rfl hdepth i
  have hOcc (i : Fin (shape.childCount v.val)) : F i ∈ Icc (0:ℝ) 1 := by
    rw [hF]
    split_ifs
    · have hpw : 0 < G.weight (e i) := Real.exp_pos _
      exact ⟨(edgeOccupation_pos hpw (Real.exp_pos _) (Real.exp_pos _)).le,
        (edgeOccupation_lt_one hpw (Real.exp_pos _) (Real.exp_pos _)).le⟩
    · exact ⟨le_rfl,zero_le_one⟩
  change Overlap.thirdOccupation (incidentEdges G v) A =
    rootThird D β u k s (shape.encodeUnorderedAt hdepth marks)
  rw [← shape.rootNode_eq_encodeUnorderedAt marks k hdepth, rootThird_node D β u s x hOcc,
    ← shape.retainedChildEdges_root_eq_incident D β marks]
  have he : shape.retainedChildEdges D v = S.image e :=
    shape.filter_edgeParent_eq_image (shape.shapeTrimDegrees D) v hv
  change Overlap.thirdOccupation (shape.retainedChildEdges D v) A =
    Overlap.thirdOccupation Finset.univ F
  have himage : Overlap.thirdOccupation (S.image e) A = Overlap.thirdOccupation S (A ∘ e) :=
    Overlap.thirdOccupation_image S e (shape.childEdgeOf_injective v hv) A
  rw [he,himage]
  have hEq : Overlap.thirdOccupation S (A ∘ e) = Overlap.thirdOccupation S F := by
    apply sub_eq_zero.mp
    apply abs_eq_zero.mp
    refine le_antisymm (Overlap.abs_thirdOccupation_sub_le le_rfl ?_) (abs_nonneg _)
    intro i hi
    change |A (e i) - F i| ≤ 0
    have hm : e i ∈ shape.shapeTrimDegrees D := (Finset.mem_filter.mp hi).2
    rw [hF, if_pos hm, sub_self, abs_zero]
  rw [hEq]
  exact thirdOccupation_filter_eq_of_nonpos F Finset.univ
    (fun i => shape.childEdgeOf v hv i ∈ shape.shapeTrimDegrees D)
    (fun i _ hi => by rw [hF,if_neg hi])

/-- The bounded continuous square statistic factors through the unordered marked tree. -/
theorem squareRowTestBCF_eq_unordered (D : ℕ) (β : ℝ) {u : ℝ} (hu : 0 < u)
    (marks : shape.NonRootSlot → ℝ) (s : ℕ) (hdepth : shape.depth = s+3) :
    shape.squareRowTestBCF D s β hu marks =
      rootSquare D β u (s+2) s (shape.encodeUnorderedAt hdepth marks) :=
  shape.squareRowTest_symbolic_eq_unordered D β hu marks s hdepth

/-- The bounded continuous small-third statistic factors through the unordered marked tree. -/
theorem smallOccupationTestBCF_eq_unordered (D : ℕ) (β η : ℝ) {u : ℝ} (hu : 0 < u)
    (marks : shape.NonRootSlot → ℝ) (s : ℕ) (hdepth : shape.depth = s+3) :
    shape.smallOccupationTestBCF D s β η hu marks =
      Overlap.smallOccupationTest η (rootThird D β u (s+2) s (shape.encodeUnorderedAt hdepth marks)) :=
  congrArg (Overlap.smallOccupationTest η)
    (shape.thirdOccupation_symbolic_eq_unordered D β hu marks s hdepth)

end Certificate.LocalExploration.PlaneShape

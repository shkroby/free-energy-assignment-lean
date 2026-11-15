import Certificate.OverlapTrimShapeSymbolic
import Certificate.OverlapTrimShapeIterate
import Certificate.OverlapBeliefIterateOccupations
import Certificate.OverlapRowTests

/-! Bounded continuous occupation tests on a trimmed marked plane shape. -/

open Finset Set
open scoped BigOperators BoundedContinuousFunction

namespace Certificate.LocalExploration.PlaneShape

open Certificate.Overlap Certificate.OverlapBelief

variable (shape : PlaneShape)

theorem continuous_symbolic_logIterate (D : ℕ) (β : ℝ) {u : ℝ} (hu : 0 < u)
    (k : ℕ) (q : State shape.Slot (PlaneNonrootSlot shape)) :
    Continuous (fun marks : shape.NonRootSlot → ℝ =>
      logIterate (shape.symbolicTrimmedGraph D β marks) u k q) := by
  induction k generalizing q with
  | zero => exact continuous_const
  | succ k ih =>
    let G (marks : shape.NonRootSlot → ℝ) := shape.symbolicTrimmedGraph D β marks
    let G₀ := G (fun _ => 0)
    let F (marks : shape.NonRootSlot → ℝ) :=
      u + ∑ e ∈ incomingEdges G₀ q, (G marks).weight e *
        Real.exp (logIterate (G marks) u k (incomingState G₀ q.1 e))
    have hf : Continuous F := continuous_const.add (continuous_finsetSum _ fun e _ => by
      exact (Real.continuous_exp.comp (continuous_const.mul (continuous_apply (shape.nonRootIndex.symm e)))).mul
        (Real.continuous_exp.comp (ih (incomingState G₀ q.1 e))))
    have hpos (marks) : 0 < F marks := by
      refine lt_of_lt_of_le hu (le_add_of_nonneg_right (Finset.sum_nonneg fun e _ => ?_))
      exact mul_nonneg ((G marks).weight_nonneg e) (Real.exp_nonneg _)
    have hc : Continuous (fun marks => -Real.log (F marks)) :=
      (continuous_iff_continuousAt.mpr fun marks =>
        (Real.continuousAt_log (hpos marks).ne').comp hf.continuousAt).neg
    exact hc.congr fun marks => (logIterate_succ (G marks) hu k q).symm

theorem continuous_symbolic_incidentOccupationIterate (D k : ℕ) (β : ℝ) {u : ℝ} (hu : 0 < u)
    (v : shape.Slot) (e : PlaneNonrootSlot shape) :
    Continuous (fun marks : shape.NonRootSlot → ℝ =>
      incidentOccupationIterate (shape.symbolicTrimmedGraph D β marks) u k v e) := by
  let G (marks : shape.NonRootSlot → ℝ) := shape.symbolicTrimmedGraph D β marks
  let G₀ := G (fun _ => 0)
  have he (marks) : 0 < (G marks).weight e := Real.exp_pos _
  have hw : Continuous (fun marks => Real.log ((G marks).weight e)) := by
    simp only [G, symbolicTrimmedGraph, Real.log_exp]
    exact continuous_const.mul (continuous_apply (shape.nonRootIndex.symm e))
  apply (((hw.add (shape.continuous_symbolic_logIterate D β hu k (v, some e))).add
    (shape.continuous_symbolic_logIterate D β hu k (incomingState G₀ v e))).sigmoid).congr
  intro marks
  exact (edgeOccupation_exp_eq_sigmoid (he marks) _ _).symm

/-- The root of a symbolic plane shape. -/
def rootSlot : shape.Slot := ⟨[], shape.root_mem⟩

/-- The square-sum test in the first k updates on a trimmed marked shape. -/
noncomputable def squareRowTestBCF (D k : ℕ) (β : ℝ) {u : ℝ} (hu : 0 < u) :
    (shape.NonRootSlot → ℝ) →ᵇ ℝ := by
  let G (marks : shape.NonRootSlot → ℝ) := shape.symbolicTrimmedGraph D β marks
  let G₀ := G (fun _ => 0)
  let s := incidentEdges G₀ shape.rootSlot
  let a := fun marks => incidentOccupationIterate (G marks) u k shape.rootSlot
  exact BoundedContinuousFunction.mkOfBound
    ⟨fun marks => squareRowTest s (a marks),
      continuous_squareRowTest s a (fun e _ =>
        shape.continuous_symbolic_incidentOccupationIterate D k β hu _ e)⟩ 1 fun x y => by
      change dist (squareRowTest s (a x)) (squareRowTest s (a y)) ≤ 1
      rw [Real.dist_eq, abs_le]
      have hx := squareRowTest_mem s (a x)
      have hy := squareRowTest_mem s (a y)
      exact ⟨by linarith only [hx.1, hy.2], by linarith only [hx.2, hy.1]⟩

/-- The test for small third occupation in the first k updates on a trimmed marked shape. -/
noncomputable def smallOccupationTestBCF (D k : ℕ) (β η : ℝ) {u : ℝ} (hu : 0 < u) :
    (shape.NonRootSlot → ℝ) →ᵇ ℝ := by
  let G (marks : shape.NonRootSlot → ℝ) := shape.symbolicTrimmedGraph D β marks
  let G₀ := G (fun _ => 0)
  let s := incidentEdges G₀ shape.rootSlot
  let a := fun marks => incidentOccupationIterate (G marks) u k shape.rootSlot
  exact BoundedContinuousFunction.mkOfBound
    ⟨fun marks => smallOccupationTest η (thirdOccupation s (a marks)),
      (continuous_smallOccupationTest η).comp (continuous_thirdOccupation s a (fun e _ =>
        shape.continuous_symbolic_incidentOccupationIterate D k β hu _ e))⟩ 1 fun x y => by
      change dist (smallOccupationTest η (thirdOccupation s (a x)))
        (smallOccupationTest η (thirdOccupation s (a y))) ≤ 1
      rw [Real.dist_eq, abs_le]
      have hx := smallOccupationTest_mem η (thirdOccupation s (a x))
      have hy := smallOccupationTest_mem η (thirdOccupation s (a y))
      exact ⟨by linarith only [hx.1, hy.2], by linarith only [hx.2, hy.1]⟩

variable {n : ℕ} (root : Fin n) (p : shape.OrderedPlacement root)

/-- The root's actual trimmed edge set is the image of the symbolic root's edges. -/
theorem trimmedRoot_incidentEdges_eq_image {β d κ R : ℝ} (hκ : 0 < κ)
    {C : CostArray} (hC : C ∈ shape.placementEvent root p (Iic (R / lengthScale d κ n)))
    (D : ℕ) (hd : 2 < shape.depth) (marks : shape.NonRootSlot → ℝ) :
    incidentEdges (trimmedAssignmentGraph β d κ R n D C) (Sum.inl root) =
      (incidentEdges (shape.symbolicTrimmedGraph D β marks) shape.rootSlot).image
        (shape.shapeEdgeLabel root p) := by
  have hr : shape.shapeVertexLabel root p shape.rootSlot = Sum.inl root :=
    congrArg ofLex (shape.placementLabel_root root p)
  have ht : incidentEdges (trimmedAssignmentGraph β d κ R n D C) (Sum.inl root) =
      incidentEdges (shape.embeddedTrimmedGraph root p β d κ D C) (Sum.inl root) := by
    rw [← hr]
    exact shape.trimDegrees_incident_retained_eq_placement root p hκ hC D shape.root_mem
      (by simpa [rootSlot] using hd)
  rw [ht, ← hr]
  exact shape.symbolicTrimmedGraph_incoming_image root p D C marks shape.rootSlot none

/-- If a symbolic edge is incident to the root, its finite-depth
occupation is the actual occupation test on the placed short-edge graph. -/
theorem incidentOccupationIterate_trimmed_eq_symbolic {β d κ R u : ℝ}
    (hκ : 0 < κ) (hu : 0 < u) {C : CostArray}
    (hC : C ∈ shape.placementEvent root p (Iic (R / lengthScale d κ n))) (D k : ℕ)
    (hd : k + 2 < shape.depth) (e : PlaneNonrootSlot shape)
    (he : e ∈ incidentEdges (shape.symbolicTrimmedGraph D β (fun _ => 0)) shape.rootSlot) :
    incidentOccupationIterate (trimmedAssignmentGraph β d κ R n D C) u k (Sum.inl root)
        (shape.shapeEdgeLabel root p e) =
      incidentOccupationIterate (shape.symbolicTrimmedGraph D β
        (labelledNeighborhoodLengths d κ (shape.nonRootIndex.trans (shape.placementEdgeEquiv root p)) C))
        u k shape.rootSlot e := by
  let G := trimmedAssignmentGraph β d κ R n D C
  let H := shape.embeddedTrimmedGraph root p β d κ D C
  let marks := labelledNeighborhoodLengths d κ (shape.nonRootIndex.trans (shape.placementEdgeEquiv root p)) C
  let K := shape.symbolicTrimmedGraph D β marks
  let g := shape.shapeVertexLabel root p
  let f := shape.shapeEdgeLabel root p
  let v := shape.rootSlot
  let w := Tree.otherEnd K.ends e v
  have hV : v.val = [] := rfl
  have hR : g v = Sum.inl root := congrArg ofLex (shape.placementLabel_root root p)
  obtain ⟨heK, hvK⟩ : e ∈ K.edges ∧ v ∈ K.ends e := Finset.mem_filter.mp he
  have hEnds := shape.symbolicTrimmedGraph_ends_image root p (β := β) (d := d) (κ := κ) (C := C) D e
  have hvH : g v ∈ H.ends (f e) := by
    rw [hEnds]
    have heq : K.ends e = {shape.shapeEdgeRow e, shape.shapeEdgeCol e} := rfl
    have hside : v = shape.shapeEdgeRow e ∨ v = shape.shapeEdgeCol e := by
      simpa only [heq, Finset.mem_insert, Finset.mem_singleton] using hvK
    change g v ∈ ({g (shape.shapeEdgeRow e),g (shape.shapeEdgeCol e)} : Finset (Fin n ⊕ Fin n))
    rcases hside with hs | hs
    · exact Finset.mem_insert.mpr (Or.inl (congrArg g hs))
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (congrArg g hs)))
  have hfE : f e ∈ shape.placementEdges root p :=
    Finset.mem_image.mpr ⟨e, Finset.mem_univ e, rfl⟩
  have hwLabel : Tree.otherEnd H.ends (f e) (g v) = g w :=
    shape.symbolicTrimmedGraph_otherEnd_image root p D C marks v e hvK
  have hvLen : v.val.length + k + 1 < shape.depth := by simp only [hV,List.length_nil,zero_add]; omega
  obtain ⟨w', hw', hLen', hOther⟩ := shape.exists_slot_of_placementOtherEnd root p
    (β := β) (d := d) (κ := κ) (C := C) D v.property (by rw [hV]; simpa using (show 0 < shape.depth by omega))
    hfE hvH
  have hId : g w = g ⟨w',hw'⟩ := hwLabel.symm.trans hOther
  have hw'Eq : w.val = w' :=
    congrArg (fun a : shape.Slot => a.val) (shape.shapeVertexLabel_injective root p hId)
  have hwLen : w.val.length + k + 1 < shape.depth := by
    rw [hw'Eq]
    rw [hV,List.length_nil,zero_add] at hLen'
    omega
  have hComp (a : shape.Slot) (hA : a.val.length + k + 1 < shape.depth) :
      logIterate G u k (g a, some (f e)) = logIterate K u k (a, some e) :=
    (shape.logIterate_trimmed_eq_embedded root p hκ hu hC D k (some (f e)) a.property hA).trans
      (shape.logIterate_embedded_eq_symbolic root p hu C D k a (some e))
  have hWeights : G.weight (f e) = K.weight e :=
    shape.symbolicTrimmedGraph_weight_image root p D C e
  have hState : incomingState G (g v) (f e) = (g w, some (f e)) :=
    congrArg (fun a => (a, some (f e))) hwLabel
  rw [← hR]
  change edgeOccupation (G.weight (f e)) (Real.exp (logIterate G u k (g v, some (f e))))
      (Real.exp (logIterate G u k (incomingState G (g v) (f e)))) =
    edgeOccupation (K.weight e) (Real.exp (logIterate K u k (v, some e)))
      (Real.exp (logIterate K u k (w, some e)))
  rw [hWeights, hComp v hvLen, hState, hComp w hwLen]

/-- On a realized shape, the actual square-row observable equals the
bounded continuous test on the symbolic marks. -/
theorem squareRowTest_trimmed_eq_shape {β d κ R u : ℝ} (hκ : 0 < κ) (hu : 0 < u)
    {C : CostArray} (hC : C ∈ shape.placementEvent root p (Iic (R / lengthScale d κ n)))
    (D k : ℕ) (hd : k + 2 < shape.depth) :
    squareRowTest (incidentEdges (trimmedAssignmentGraph β d κ R n D C) (Sum.inl root))
      (incidentOccupationIterate (trimmedAssignmentGraph β d κ R n D C) u k (Sum.inl root)) =
      shape.squareRowTestBCF D k β hu
        (labelledNeighborhoodLengths d κ (shape.nonRootIndex.trans (shape.placementEdgeEquiv root p)) C) := by
  let G := trimmedAssignmentGraph β d κ R n D C
  let marks := labelledNeighborhoodLengths d κ (shape.nonRootIndex.trans (shape.placementEdgeEquiv root p)) C
  let H := shape.symbolicTrimmedGraph D β marks
  let f := shape.shapeEdgeLabel root p
  let S := incidentEdges H shape.rootSlot
  have hS : incidentEdges G (Sum.inl root) = S.image f :=
    shape.trimmedRoot_incidentEdges_eq_image root p hκ hC D (by omega) marks
  change squareRowTest (incidentEdges G (Sum.inl root))
        (incidentOccupationIterate G u k (Sum.inl root)) =
    squareRowTest S (incidentOccupationIterate H u k shape.rootSlot)
  rw [hS]
  unfold squareRowTest
  rw [Finset.sum_image (fun _ _ _ _ h => shape.shapeEdgeLabel_injective root p h)]
  apply congrArg (min (1:ℝ))
  exact Finset.sum_congr rfl fun e he => congrArg (fun a : ℝ => a^2)
    (shape.incidentOccupationIterate_trimmed_eq_symbolic root p hκ hu hC D k hd e he)


/-- On a realized shape, the third-occupation test equals its bounded
continuous counterpart on symbolic marks. -/
theorem smallOccupationTest_trimmed_eq_shape {β d κ R u : ℝ} (hκ : 0 < κ) (hu : 0 < u)
    {C : CostArray} (hC : C ∈ shape.placementEvent root p (Iic (R / lengthScale d κ n)))
    (D k : ℕ) (η : ℝ) (hd : k + 2 < shape.depth) :
    smallOccupationTest η
      (thirdOccupation (incidentEdges (trimmedAssignmentGraph β d κ R n D C) (Sum.inl root))
        (incidentOccupationIterate (trimmedAssignmentGraph β d κ R n D C) u k (Sum.inl root))) =
      shape.smallOccupationTestBCF D k β η hu
        (labelledNeighborhoodLengths d κ (shape.nonRootIndex.trans (shape.placementEdgeEquiv root p)) C) := by
  let G := trimmedAssignmentGraph β d κ R n D C
  let marks := labelledNeighborhoodLengths d κ (shape.nonRootIndex.trans (shape.placementEdgeEquiv root p)) C
  let H := shape.symbolicTrimmedGraph D β marks
  let f := shape.shapeEdgeLabel root p
  let S := incidentEdges H shape.rootSlot
  have hS : incidentEdges G (Sum.inl root) = S.image f :=
    shape.trimmedRoot_incidentEdges_eq_image root p hκ hC D (by omega) marks
  change smallOccupationTest η
      (thirdOccupation (incidentEdges G (Sum.inl root))
        (incidentOccupationIterate G u k (Sum.inl root))) =
    smallOccupationTest η (thirdOccupation S (incidentOccupationIterate H u k shape.rootSlot))
  rw [hS, thirdOccupation_image S f (shape.shapeEdgeLabel_injective root p)]
  apply congrArg (smallOccupationTest η)
  apply sub_eq_zero.mp
  apply abs_eq_zero.mp
  refine le_antisymm (abs_thirdOccupation_sub_le le_rfl ?_) (abs_nonneg _)
  intro e he
  change |incidentOccupationIterate G u k (Sum.inl root) (f e) -
    incidentOccupationIterate H u k shape.rootSlot e| ≤ 0
  rw [shape.incidentOccupationIterate_trimmed_eq_symbolic root p hκ hu hC D k hd e he, sub_self, abs_zero]

end Certificate.LocalExploration.PlaneShape

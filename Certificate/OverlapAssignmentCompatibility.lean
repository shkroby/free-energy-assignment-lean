import Certificate.OverlapAssignmentTilt
import Certificate.OverlapDegreeTail
import Certificate.OverlapLocalGoodRoots
import Certificate.OverlapLocalTests
import Certificate.OverlapTrimGeometry

/-! Almost-sure compatibility of almost all roots in the retained graph. -/

open Finset Filter MeasureTheory Set
open scoped Topology

namespace Certificate.Overlap
open OverlapBelief LocalExploration

private theorem retainedEdge_swap_iff {d κ R : ℝ} {n : ℕ} (C : CostArray) (e : Fin n × Fin n) :
    e ∈ retainedEdges d κ R n (transposeCosts C) ↔ e.swap ∈ retainedEdges d κ R n C := by
  have hmem (B : CostArray) (f : Fin n × Fin n) :
      f ∈ retainedEdges d κ R n B ↔ edgeLength d κ n B f ≤ R := by
    unfold retainedEdges
    exact Finset.mem_filter.trans (and_iff_right (Finset.mem_univ f))
  rcases e with ⟨i,j⟩
  rw [hmem, hmem]
  rfl

private theorem ends_swap_map {n : ℕ} (e : Fin n × Fin n) :
    Tree.Bipartite.ends e.swap =
      (Tree.Bipartite.ends e).map (Equiv.sumComm (Fin n) (Fin n)).toEmbedding := by
  rcases e with ⟨i,j⟩
  change ({Sum.inl j, Sum.inr i} : Finset (Fin n ⊕ Fin n)) =
    ({Sum.inl i, Sum.inr j} : Finset (Fin n ⊕ Fin n)).map
      (Equiv.sumComm (Fin n) (Fin n)).toEmbedding
  rw [Finset.map_insert, Finset.map_singleton]
  exact Finset.pair_comm _ _

set_option maxHeartbeats 1000000 in
private theorem goodRoot_retained_of_transposedPlacement (shape : PlaneShape)
    {n : ℕ} (root : Fin n) (p : shape.OrderedPlacement root) (β d κ R : ℝ)
    (hκ : 0 < κ) {C : CostArray}
    (hC : transposeCosts C ∈ shape.placementEvent root p (Iic (R / lengthScale d κ n)))
    (kept : Finset (Fin n × Fin n)) (hkept : kept ⊆ retainedEdges d κ R n C)
    (k : ℕ) (hk : k ≤ shape.depth) :
    goodRoot ((assignmentGraph β d κ n C).retain kept (Finset.subset_univ _)) k (Sum.inr root) := by
  let G := (assignmentGraph β d κ n C).retain kept (Finset.subset_univ _)
  let H := shape.cutoffPlacementLocalEdges root p β d κ R hκ hC
  let σ := Equiv.sumComm (Fin n) (Fin n)
  let label (v : List ℕ) := σ (ofLex (shape.placementLabel root p v))
  have hroot : label [] = Sum.inr root := by
    have h := congrArg ofLex (shape.placementLabel_root root p)
    change σ (ofLex (shape.placementLabel root p [])) = _
    rw [h]
    rfl
  have hLocal : PlaneShape.LocalEdges shape label G.ends (retainedEdges d κ R n C) G.weight β
      (labelledNeighborhoodLengths d κ (shape.nonRootIndex.trans (shape.placementEdgeEquiv root p))
        (transposeCosts C)) := by
    refine ⟨fun _ ha _ hb hab => H.injective ha hb (σ.injective hab),
      fun v i => (H.edge v i).swap, ?_, ?_, ?_, ?_⟩
    · intro v hv hd i
      exact (retainedEdge_swap_iff C _).mp (H.child_mem v hv hd i)
    · intro v hv hd i
      change Tree.Bipartite.ends (H.edge v i).swap = _
      rw [ends_swap_map, H.child_ends v hv hd i]
      simp only [Finset.map_insert, Finset.map_singleton, Equiv.coe_toEmbedding, σ, label]
    · intro v hv hd i
      have h := H.child_weight v hv hd i
      change Real.exp (-β * edgeLength d κ n C (H.edge v i).swap) = _
      change Real.exp (-β * edgeLength d κ n (transposeCosts C) (H.edge v i)) = _ at h
      simpa only [edgeLength, transposeCosts, Function.comp_apply, Prod.swap_prod_mk,
        Prod.fst_swap, Prod.snd_swap] using h
    · intro v hv hd e he hl hp
      have he' : e.swap ∈ retainedEdges d κ R n (transposeCosts C) :=
        (retainedEdge_swap_iff C e.swap).mpr (by simpa only [Prod.swap_swap] using he)
      have hends : (Tree.Bipartite.ends e.swap).map σ.toEmbedding = G.ends e := by
        rw [← ends_swap_map, Prod.swap_swap]
        rfl
      have hl' : ofLex (shape.placementLabel root p v) ∈ Tree.Bipartite.ends e.swap := by
        rw [← hends] at hl
        exact (Finset.mem_map' σ.toEmbedding).mp hl
      have hp' (hvne : v ≠ []) :
          ofLex (shape.placementLabel root p v.dropLast) ∉ Tree.Bipartite.ends e.swap := by
        intro hh
        apply hp hvne
        rw [← hends]
        exact (Finset.mem_map' σ.toEmbedding).mpr hh
      obtain ⟨i, hi⟩ := H.exhaustive v hv hd e.swap he' hl' hp'
      exact ⟨i, (congrArg Prod.swap hi).trans (Prod.swap_swap e)⟩
  have h := walkCompatible_of_localEdges (G := G) hLocal hkept
    (fun _ _ he => PlaneShape.eq_of_ends_eq he)
    k G.vertices [] none shape.root_mem (by simpa using hk)
    (fun _ _ => Finset.mem_univ _) (fun _ => rfl) (fun h => (h rfl).elim)
  change walkCompatible G k G.vertices (label [], none) at h
  rw [hroot] at h
  exact h

private def rootSide (n : ℕ) (left : Bool) : Fin n ↪ Fin n ⊕ Fin n :=
  if left then ⟨Sum.inl, Sum.inl_injective⟩ else ⟨Sum.inr, Sum.inr_injective⟩

private noncomputable def compatibilityTest (β d κ R : ℝ) (D k n : ℕ) (left : Bool)
    (x : Fin n → Fin n → ℝ) (i : Fin n) : ℝ := by
  classical
  exact if goodRoot (trimmedGraphOfRows β d κ R n D x) k (rootSide n left i) then 1 else 0

private theorem measurable_compatibilityTest (β d κ R : ℝ) (D k n : ℕ) (left : Bool)
    (i : Fin n) : Measurable (fun x => compatibilityTest β d κ R D k n left x i) := by
  classical
  let G := trimmedGraphOfRows β d κ R n D
  let H (s : Finset (Fin n × Fin n)) :=
    (squareWeightedGraph (fun _ _ => 1) (fun _ _ => zero_le_one)).retain s (Finset.subset_univ _)
  let f (s : Finset (Fin n × Fin n)) :=
    if goodRoot (H s) k (rootSide n left i) then (1 : ℝ) else 0
  have hm : Measurable (fun x => (G x).edges) :=
    measurable_to_countable fun x => measurableSet_trimmedGraphOfRows_edges_eq β d κ R n D (G x).edges
  have heq : (fun x => compatibilityTest β d κ R D k n left x i) = f ∘ fun x => (G x).edges := by
    funext x
    have hh : goodRoot (G x) k (rootSide n left i) ↔ goodRoot (H (G x).edges) k (rootSide n left i) :=
      ⟨goodRoot_of_edges_subset (G x) (H (G x).edges) rfl rfl (subset_refl _),
        goodRoot_of_edges_subset (H (G x).edges) (G x) rfl rfl (subset_refl _)⟩
    change (if goodRoot (G x) k (rootSide n left i) then (1 : ℝ) else 0) =
      (if goodRoot (H (G x).edges) k (rootSide n left i) then 1 else 0)
    rw [hh]
  rw [heq]
  exact (measurable_of_countable f).comp hm

private theorem compatibilityTest_mem (β d κ R : ℝ) (D k n : ℕ) (left : Bool)
    (x : Fin n → Fin n → ℝ) (i : Fin n) :
    compatibilityTest β d κ R D k n left x i ∈ Set.Icc (0:ℝ) 1 := by
  unfold compatibilityTest
  split_ifs <;> constructor <;> norm_num

set_option maxHeartbeats 1000000 in
private theorem compatibilityTest_changed_le (β d κ R : ℝ) (D k : ℕ) (left : Bool)
    (n : ℕ) (x y : Fin n → Fin n → ℝ) (r : Fin n) (h : ∀ i ≠ r, x i = y i) :
    (Finset.univ.filter (fun i => compatibilityTest β d κ R D k n left x i ≠
      compatibilityTest β d κ R D k n left y i)).card ≤
      2 * (4*D^2 + 2*D) * (1+2*(2*D))^k := by
  classical
  obtain ⟨bad,hagree,hcard⟩ :=
    exists_trimmedGraphOfRows_affectedVertices (β := β) (d := d) (κ := κ) (R := R) D k x y r h
  let G := trimmedGraphOfRows β d κ R n D x
  let H := trimmedGraphOfRows β d κ R n D y
  let affected := affectedVertices G.ends (G.edges ∪ H.edges) bad k
  let changed := Finset.univ.filter (fun i => compatibilityTest β d κ R D k n left x i ≠
    compatibilityTest β d κ R D k n left y i)
  have hsubset : changed.map (rootSide n left) ⊆ affected := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hv
    have hdifferent := (Finset.mem_filter.mp hi).2
    by_contra hout
    have hsame : goodRoot G k (rootSide n left i) ↔ goodRoot H k (rootSide n left i) :=
      walkCompatible_iff_of_notMem_affectedVertices (G := G) (H := H) rfl bad hagree k
        G.vertices (rootSide n left i) none hout
    apply hdifferent
    change (if goodRoot G k (rootSide n left i) then (1 : ℝ) else 0) =
      (if goodRoot H k (rootSide n left i) then 1 else 0)
    rw [hsame]
  have hb := Finset.card_le_card hsubset
  rw [Finset.card_map] at hb
  exact hb.trans hcard

private theorem integral_compatibilityTest_le_one
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (β d κ R : ℝ) (D k n : ℕ) (left : Bool) (i : Fin n) :
    (∫ C, compatibilityTest β d κ R D k n left (costRows n C) i ∂iidCosts μ) ≤ 1 := by
  let : IsProbabilityMeasure (iidCosts μ) := by unfold iidCosts; infer_instance
  let f (C : CostArray) := compatibilityTest β d κ R D k n left (costRows n C) i
  have hm : Measurable f := (measurable_compatibilityTest β d κ R D k n left i).comp
    (measurePreserving_costRows μ n).measurable
  have hB (C : CostArray) : f C ∈ Set.Icc (0:ℝ) 1 :=
    compatibilityTest_mem β d κ R D k n left (costRows n C) i
  have hI : Integrable f (iidCosts μ) := Integrable.of_bound hm.aestronglyMeasurable 1
    (Eventually.of_forall fun C => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hB C).1]
      exact (hB C).2)
  calc
    _ ≤ ∫ _ : CostArray, (1 : ℝ) ∂iidCosts μ :=
      integral_mono hI (integrable_const _) (fun C => (hB C).2)
    _ = 1 := by simp

set_option maxHeartbeats 1000000 in
private theorem tendsto_pinned_compatibilityTest {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {β d κ R : ℝ} (hd : 0 < d) (hκ : 0 < κ) (hR : 0 < R) (hμ : SmallCostTail μ κ d)
    (D k : ℕ) (left : Bool) (roots : ∀ n : ℕ, Fin (n+1)) :
    Tendsto (fun n => ∫ C, compatibilityTest β d κ R D k (n+1) left (costRows (n+1) C)
      (roots n) ∂iidCosts μ) atTop (𝓝 1) := by
  let : IsProbabilityMeasure (iidCosts μ) := by unfold iidCosts; infer_instance
  let U (n : ℕ) := ⋃ c : PlaneShapeCode k,
    c.shape.shapeEvent (roots n) (Iic (R / lengthScale d κ (n+1)))
  let rowSide : CostArray → CostArray := if left then id else transposeCosts
  have hTransform : MeasurePreserving rowSide (iidCosts μ) (iidCosts μ) := by
    cases left
    · exact measurePreserving_transposeCosts μ
    · exact MeasurePreserving.id _
  have hU (n : ℕ) : MeasurableSet (U n) :=
    MeasurableSet.iUnion fun c => c.shape.measurableSet_shapeEvent (roots n) measurableSet_Iic
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (tendsto_probability_treeShapeUnion hd hκ hR hμ k roots) tendsto_const_nhds _ _
  · intro n
    let N := n+1
    let f (C : CostArray) := compatibilityTest β d κ R D k N left (costRows N C) (roots n)
    let V := rowSide ⁻¹' U n
    have hV : MeasurableSet V := (hU n).preimage hTransform.measurable
    have hEq : (iidCosts μ).real (U n) = (iidCosts μ).real V := by
      change ((iidCosts μ) (U n)).toReal = ((iidCosts μ) V).toReal
      apply congrArg ENNReal.toReal
      calc
        _ = ((iidCosts μ).map rowSide) (U n) := by rw [hTransform.map_eq]
        _ = _ := Measure.map_apply hTransform.measurable (hU n)
    have hm : Measurable f :=
      (measurable_compatibilityTest β d κ R D k N left (roots n)).comp
        (measurePreserving_costRows μ N).measurable
    have hI : Integrable f (iidCosts μ) := Integrable.of_bound hm.aestronglyMeasurable 1
      (Eventually.of_forall fun C => by
        have hb := compatibilityTest_mem β d κ R D k N left (costRows N C) (roots n)
        simpa only [f, Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2)
    change (iidCosts μ).real (U n) ≤ ∫ C, f C ∂iidCosts μ
    rw [hEq, ← integral_indicator_one hV]
    apply integral_mono ((integrable_const _).indicator hV) hI
    intro C
    by_cases hmem : C ∈ V
    · rw [Set.indicator_of_mem hmem]
      have hshape : rowSide C ∈ U n := hmem
      obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hshape
      obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hc
      let kept := trimDegrees D (retainedEdges d κ R N C)
      have hkept : kept ⊆ retainedEdges d κ R N C := trimDegrees_subset _ _
      have hgood : goodRoot (trimmedAssignmentGraph β d κ R N D C) k
          (rootSide N left (roots n)) := by
        cases left
        · exact goodRoot_retained_of_transposedPlacement c.shape (roots n) p β d κ R hκ hp
            kept hkept k c.shape_depth.ge
        · exact goodRoot_retained_of_placement c.shape (roots n) p β d κ R hκ hp
            kept hkept k c.shape_depth.ge
      change (1 : ℝ) ≤ f C
      unfold f compatibilityTest
      rw [trimmedGraphOfRows_costRows, if_pos hgood]
    · rw [Set.indicator_of_notMem hmem]
      exact (compatibilityTest_mem β d κ R D k N left (costRows N C) (roots n)).1
  · intro n
    exact integral_compatibilityTest_le_one β d κ R D k (n+1) left (roots n)

private theorem ae_tendsto_compatibleRowMean {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {β d κ R : ℝ} (hd : 0 < d) (hκ : 0 < κ) (hR : 0 < R) (hμ : SmallCostTail μ κ d)
    (D k : ℕ) (left : Bool) :
    ∀ᵐ C ∂iidCosts μ, Tendsto (fun n => rowObservableMean n
      (compatibilityTest β d κ R D k n left) (costRows n C)) atTop (𝓝 1) :=
  ae_tendsto_rowObservableMean_of_expected_roots
    (fun n => compatibilityTest β d κ R D k n left)
    (fun n => measurable_compatibilityTest β d κ R D k n left)
    (fun n => compatibilityTest_mem β d κ R D k n left)
    (Nat.succ_pos (2 * (4*D^2 + 2*D) * (1+2*(2*D))^k))
    (fun n x y r h => (compatibilityTest_changed_le β d κ R D k left n x y r h).trans
      (Nat.le_succ _))
    (tendsto_pinned_compatibilityTest hd hκ hR hμ D k left)

/-- At fixed depth, the number of incompatible roots divided by the
assignment size tends to zero almost surely. -/
theorem ae_tendsto_trimmedAssignment_badRootFraction {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {β d κ R : ℝ} (hd : 0 < d) (hκ : 0 < κ) (hR : 0 < R) (hμ : SmallCostTail μ κ d)
    (D k : ℕ) :
    ∀ᵐ C ∂iidCosts μ, Tendsto (fun n : ℕ =>
      let G := trimmedAssignmentGraph β d κ R n D C
      (((G.vertices \ trimmedAssignmentGoodRoots β d κ R n D k C).card : ℝ) / (n : ℝ)))
        atTop (𝓝 0) := by
  classical
  filter_upwards [ae_tendsto_compatibleRowMean hd hκ hR hμ D k true,
    ae_tendsto_compatibleRowMean hd hκ hR hμ D k false] with C hL hR
  have h := (hL.add hR).const_sub 2
  norm_num at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  let G := trimmedAssignmentGraph β d κ R n D C
  let good := trimmedAssignmentGoodRoots β d κ R n D k C
  let F (l : Bool) := ∑ i : Fin n, compatibilityTest β d κ R D k n l (costRows n C) i
  have hv : G.vertices = Finset.univ := rfl
  have hGood : good = Finset.univ.filter (goodRoot G k) := by
    simp only [good, trimmedAssignmentGoodRoots, hv, G]
  have hg : (good.card : ℝ) = F true + F false := by
    rw [hGood, natCast_card_filter, Fintype.sum_sum_type]
    simp only [F, compatibilityTest, trimmedGraphOfRows_costRows, rootSide, Bool.false_eq_true,
      if_false, if_true, Function.Embedding.coeFn_mk, G]
  change 2 - (F true / (n : ℝ) + F false / (n : ℝ)) =
    ((G.vertices \ good).card : ℝ) / n
  rw [Finset.card_sdiff_of_subset (by rw [hv]; exact Finset.subset_univ _),
    Nat.cast_sub (by rw [hv]; exact card_le_card (Finset.subset_univ _)), hv,
    Finset.card_univ, Fintype.card_sum, Fintype.card_fin, Nat.cast_add, hg]
  field_simp [Nat.cast_ne_zero.mpr hn.ne']
  ring

end Certificate.Overlap

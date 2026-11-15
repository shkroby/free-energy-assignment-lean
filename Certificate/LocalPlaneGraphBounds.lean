import Certificate.LocalPlaneBrackets
import Certificate.TreeBracketIsomorphism

/-! Exact preservation of the vacancy brackets by a labelled tree neighborhood. -/

open Set Finset

namespace Certificate.LocalExploration.PlaneShape

variable {V E : Type*} [DecidableEq V]

/-- The successive child edges in a labelled neighborhood describe every
incident edge other than the parent edge. -/
structure LocalEdges (shape : PlaneShape) (label : List ℕ → V)
    (ends : E → Finset V) (edges : Finset E) (w : E → ℝ)
    (β : ℝ) (marks : shape.NonRootSlot → ℝ) where
  injective : InjOn label shape.slots
  edge : (v : List ℕ) → Fin (shape.childCount v) → E
  child_mem : ∀ v ∈ shape.slots, v.length < shape.depth → ∀ i : Fin (shape.childCount v),
    edge v i ∈ edges
  child_ends : ∀ v ∈ shape.slots, v.length < shape.depth → ∀ i : Fin (shape.childCount v),
    ends (edge v i) = {label v, label (v ++ [i.val])}
  child_weight : ∀ v ∈ shape.slots, v.length < shape.depth → ∀ i : Fin (shape.childCount v),
    w (edge v i) = shape.shapeWeight β marks v i.val
  exhaustive : ∀ v ∈ shape.slots, v.length < shape.depth → ∀ e ∈ edges, label v ∈ ends e →
    (v ≠ [] → label v.dropLast ∉ ends e) → ∃ i, edge v i = e

private theorem otherEnd_pair_eq (ends : E → Finset V) (e : E) {v u : V} (hne : u ≠ v)
    (h : ends e = {v, u}) : Tree.otherEnd ends e v = u := by
  have he : (ends e).erase v = {u} := by rw [h]; simp [hne.symm]
  have hN : ((ends e).erase v).Nonempty := by rw [he]; simp
  unfold Tree.otherEnd
  rw [dif_pos hN]
  have hInc : ∀ a : V, a ∈ (ends e).erase v → a ∈ ({u} : Finset V) := by
    intro a ha
    rw [← he]
    exact ha
  exact mem_singleton.mp (hInc _ hN.choose_spec)

omit [DecidableEq V] in
private theorem child_label_ne {shape : PlaneShape} {label : List ℕ → V}
    (hf : InjOn label shape.slots) {v : List ℕ} (hv : v ∈ shape.slots)
    {i : ℕ} (hi : v ++ [i] ∈ shape.slots) : label (v ++ [i]) ≠ label v := by
  intro he
  have h := congrArg List.length (hf hi hv he)
  simp at h

private theorem matchesTree_aux {shape : PlaneShape} {label : List ℕ → V}
    {ends : E → Finset V} {edges : Finset E} {w : E → ℝ}
    {β : ℝ} {marks : shape.NonRootSlot → ℝ} (H : LocalEdges shape label ends edges w β marks)
    (k : ℕ) (vertices : Finset V) (v : List ℕ) (hv : v ∈ shape.slots)
    (hdepth : k + v.length ≤ shape.depth)
    (hkeep : ∀ s : List ℕ, v ++ s ∈ shape.slots → label (v ++ s) ∈ vertices)
    (hparent : v ≠ [] → label v.dropLast ∉ vertices) :
    Tree.matchesTreeToDepth ends edges w (fun u i ↦ u ++ [i]) (shape.shapeWeight β marks)
      k vertices (label v) v := by
  induction k generalizing vertices v with
  | zero => trivial
  | succ k ih =>
    have hd : v.length < shape.depth := by omega
    have hv' : label v ∈ vertices := by simpa only [List.append_nil] using hkeep [] (by simpa)
    let I := Fin (shape.childCount v)
    let S := Finset.range (shape.childCount v)
    have hc (i : I) : v ++ [i.val] ∈ shape.slots := (shape.child_mem v i.val).mpr ⟨hv, hd, i.isLt⟩
    let B := Tree.incident ends vertices edges (label v)
    let f (i : I) : ↥B := ⟨H.edge v i, Finset.mem_filter.mpr ⟨H.child_mem v hv hd i, by
      rw [H.child_ends v hv hd i]
      exact ⟨mem_insert_self _ _, Finset.insert_subset_iff.mpr
        ⟨hv', singleton_subset_iff.mpr (hkeep [i.val] (hc i))⟩⟩⟩⟩
    have hf : Function.Bijective f := by
      constructor
      · intro i j he
        have h : ends (H.edge v i) = ends (H.edge v j) := congrArg (fun r : ↥B ↦ ends r.val) he
        rw [H.child_ends v hv hd i, H.child_ends v hv hd j] at h
        have hm : label (v ++ [i.val]) ∈ ({label v, label (v ++ [j.val])} : Finset V) :=
          h ▸ mem_insert_of_mem (mem_singleton_self _)
        have heq := H.injective (hc i) (hc j)
          ((Finset.mem_insert.mp hm).resolve_left (child_label_ne H.injective hv (hc i)) |> mem_singleton.mp)
        apply Fin.ext
        simpa only [List.append_cancel_left_eq, List.singleton_inj] using heq
      · rintro ⟨e, he⟩
        obtain ⟨heE, hvE, hsub⟩ := Finset.mem_filter.mp he
        obtain ⟨i, hi⟩ := H.exhaustive v hv hd e heE hvE
          (fun hne hmem ↦ hparent hne (hsub hmem))
        exact ⟨i, Subtype.ext hi⟩
    let ef := Equiv.ofBijective f hf
    let ix : I ≃ ↥S :=
      { toFun := fun i ↦ ⟨i, Finset.mem_range.mpr i.isLt⟩
        invFun := fun i ↦ ⟨i, Finset.mem_range.mp i.property⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    refine ⟨S, ef.symm.trans ix, shape.shapeWeight_eq_zero_of_notMem β marks v, ?_, ?_⟩
    · intro e
      let i := ef.symm e
      have hie : H.edge v i = e.val := congrArg Subtype.val (ef.apply_symm_apply e)
      change w e.val = shape.shapeWeight β marks v i.val
      rw [← hie]
      exact H.child_weight v hv hd i
    · intro e
      let i := ef.symm e
      have hie : H.edge v i = e.val := congrArg Subtype.val (ef.apply_symm_apply e)
      have he : ends e.val = {label v, label (v ++ [i.val])} :=
        hie ▸ H.child_ends v hv hd i
      change Tree.matchesTreeToDepth ends edges w (fun u i ↦ u ++ [i])
        (shape.shapeWeight β marks) k (vertices.erase (label v)) (Tree.otherEnd ends e (label v))
        (v ++ [i.val])
      rw [otherEnd_pair_eq ends e (child_label_ne H.injective hv (hc i)) he]
      apply ih _ _ (hc i)
      · simp only [List.length_append, List.length_cons, List.length_nil, zero_add]
        omega
      · intro s hs
        apply Finset.mem_erase.mpr
        constructor
        · intro h
          have hEq := congrArg List.length (H.injective hs hv h)
          simp at hEq
        · simpa only [List.append_assoc] using hkeep ([i.val] ++ s)
            (by simpa only [List.append_assoc] using hs)
      · intro _
        rw [List.dropLast_concat]
        exact Finset.notMem_erase _ _

/-- The two graph brackets at the labelled root equal the bounded continuous
shape test when the interior neighbor and mark identifications hold. -/
theorem finiteRootBounds_eq_shapeBracket {shape : PlaneShape} {label : List ℕ → V}
    {ends : E → Finset V} {edges : Finset E} {w : E → ℝ}
    {β : ℝ} {marks : shape.NonRootSlot → ℝ} (H : LocalEdges shape label ends edges w β marks)
    (z : ℝ) (vertices : Finset V) (hV : ∀ v ∈ shape.slots, label v ∈ vertices) :
    Tree.finiteRootBounds ends edges w z shape.depth vertices (label []) = shape.shapeBracket β z marks := by
  apply Tree.finiteRootBounds_eq_treeBounds_of_matchesTreeToDepth
  apply matchesTree_aux H shape.depth vertices [] shape.root_mem
  · simp
  · intro s hs
    exact hV _ hs
  · intro h
    exact (h rfl).elim

end Certificate.LocalExploration.PlaneShape

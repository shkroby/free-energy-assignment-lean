import Certificate.OverlapBeliefLocal
import Certificate.OverlapTrim
import Certificate.LocalPlaneAssignmentBrackets

/-! A realized plane tree is locally compatible with vertex deletion
after retaining any subset of its graph's edges. -/

open Finset Set

namespace Certificate.Overlap

open OverlapBelief LocalExploration

private theorem mem_incomingEdges_iff {V E : Type*} [DecidableEq V] [DecidableEq E]
    (G : WeightedGraph V E) (v : V) (e : E) (previous : Option E) :
    e ∈ incomingEdges G (v, previous) ↔
      e ∈ G.edges ∧ v ∈ G.ends e ∧ previous ≠ some e := by
  cases previous <;> simp [incomingEdges, incidentEdges, and_comm, and_left_comm, ne_comm]

set_option maxHeartbeats 800000 in
/-- A labelled tree neighborhood remains compatible with the deletion
recursion after restricting it to any subset of its edges. -/
theorem walkCompatible_of_localEdges {V E : Type*} [DecidableEq V] [DecidableEq E]
    {G : WeightedGraph V E} {allEdges : Finset E} {shape : PlaneShape}
    {label : List ℕ → V} {β : ℝ} {marks : shape.NonRootSlot → ℝ}
    (H : PlaneShape.LocalEdges shape label G.ends allEdges G.weight β marks)
    (hsub : G.edges ⊆ allEdges) (hinj : Function.Injective G.ends)
    (k : ℕ) (remain : Finset V) (v : List ℕ) (prev : Option E)
    (hv : v ∈ shape.slots) (hd : k + v.length ≤ shape.depth)
    (hkeep : ∀ s : List ℕ, v ++ s ∈ shape.slots → label (v ++ s) ∈ remain)
    (hroot : v = [] → prev = none)
    (hparent : v ≠ [] → ∃ e, prev = some e ∧ G.ends e = {label v, label v.dropLast} ∧
      label v.dropLast ∉ remain) :
    walkCompatible G k remain (label v, prev) := by
  induction k generalizing v remain prev with
  | zero => trivial
  | succ k ih =>
    have hd' : v.length < shape.depth := by omega
    have hvR : label v ∈ remain := by
      simpa only [List.append_nil] using hkeep [] (by simpa)
    have hc (i : Fin (shape.childCount v)) : v ++ [i.val] ∈ shape.slots :=
      (shape.child_mem _ _).mpr ⟨hv,hd',i.isLt⟩
    have noParent {e : E} (he : e ∈ G.edges) (hve : label v ∈ G.ends e)
        (hp : prev ≠ some e) :
        v ≠ [] → label v.dropLast ∉ G.ends e := by
      intro hne hmem
      obtain ⟨e', he', hEnds, hNotR⟩ := hparent hne
      have hdiff : label v ≠ label v.dropLast := fun h => hNotR (h ▸ hvR)
      have hs : ({label v, label v.dropLast} : Finset V) ⊆ G.ends e := by
        intro a ha
        rcases mem_insert.mp ha with rfl | ha
        · exact hve
        · exact mem_singleton.mp ha ▸ hmem
      have heq := eq_of_subset_of_card_le hs (by rw [G.ends_card e he]; simp [hdiff])
      exact hp (he'.trans (congrArg some (hinj (hEnds.trans heq))))
    have hchild (e : E) (he : e ∈ incomingEdges G (label v, prev)) :
        ∃ i : Fin (shape.childCount v), H.edge v i = e := by
      obtain ⟨he,hve,hp⟩ := (mem_incomingEdges_iff G _ _ _).mp he
      exact H.exhaustive v hv hd' e (hsub he) hve (noParent he hve hp)
    change incomingEdges G (label v, prev) = Tree.incident G.ends remain G.edges (label v) ∧ _
    constructor
    · ext e
      constructor
      · intro he
        obtain ⟨i, hi⟩ := hchild e he
        have hEnds : G.ends e = {label v, label (v ++ [i.val])} :=
          hi ▸ H.child_ends v hv hd' i
        obtain ⟨he,hve,_⟩ := (mem_incomingEdges_iff G _ _ _).mp he
        have hs : G.ends e ⊆ remain := by
          rw [hEnds, Finset.insert_subset_iff]
          exact ⟨hvR,singleton_subset_iff.mpr (hkeep [i.val] (hc i))⟩
        exact mem_filter.mpr ⟨he,hve,hs⟩
      · intro he
        obtain ⟨he,hve,hs⟩ := mem_filter.mp he
        apply (mem_incomingEdges_iff G _ _ _).mpr ⟨he,hve,?_⟩
        intro hePrev
        by_cases h : v = []
        · rw [hroot h] at hePrev
          cases hePrev
        · obtain ⟨e', hp, hEnds, hNotR⟩ := hparent h
          have heq := Option.some.inj (hp.symm.trans hePrev)
          rw [heq] at hEnds
          exact hNotR (hs (by rw [hEnds]; simp))
    · intro e he
      obtain ⟨i, hi⟩ := hchild e he
      have hEnds : G.ends e = {label v, label (v ++ [i.val])} :=
        hi ▸ H.child_ends v hv hd' i
      have hdiff : label (v ++ [i.val]) ≠ label v := by
        intro h
        have heq := congrArg List.length (H.injective (hc i) hv h)
        simp at heq
      change walkCompatible G k (remain.erase (label v)) (Tree.otherEnd G.ends e (label v), some e)
      rw [otherEnd_of_endpoints G hEnds hdiff.symm]
      apply ih _ _ _ (hc i)
      · simp only [List.length_append, List.length_singleton]
        omega
      · intro s hs
        apply mem_erase.mpr
        constructor
        · intro he
          have h := congrArg List.length (H.injective hs hv he)
          simp at h
        · simpa only [List.append_assoc] using
            hkeep ([i.val] ++ s) (by simpa only [List.append_assoc] using hs)
      · intro h
        simp at h
      · intro _
        rw [List.dropLast_concat]
        exact ⟨e,rfl,hEnds.trans (Finset.pair_comm _ _),Finset.notMem_erase _ _⟩

/-- A placed plane tree yields a compatible deletion recursion on every
subgraph obtained by deleting edges, including the degree-trimmed graph. -/
theorem goodRoot_retained_of_placement (shape : PlaneShape) {n : ℕ} (root : Fin n)
    (p : shape.OrderedPlacement root) (β d κ R : ℝ) (hκ : 0 < κ) {C : CostArray}
    (hC : C ∈ shape.placementEvent root p (Iic (R / lengthScale d κ n)))
    (kept : Finset (Fin n × Fin n)) (hkept : kept ⊆ retainedEdges d κ R n C)
    (k : ℕ) (hk : k ≤ shape.depth) :
    goodRoot ((assignmentGraph β d κ n C).retain kept (Finset.subset_univ _)) k (Sum.inl root) := by
  let G := (assignmentGraph β d κ n C).retain kept (Finset.subset_univ _)
  let H := shape.cutoffPlacementLocalEdges root p β d κ R hκ hC
  have hr : ofLex (shape.placementLabel root p []) = Sum.inl root := congrArg ofLex (shape.placementLabel_root root p)
  have h := walkCompatible_of_localEdges (G := G) H hkept
    (fun _ _ he => PlaneShape.eq_of_ends_eq he)
    k G.vertices [] none shape.root_mem (by simpa using hk)
    (fun _ _ => Finset.mem_univ _) (fun _ => rfl) (fun h => (h rfl).elim)
  rw [hr] at h
  exact h

end Certificate.Overlap

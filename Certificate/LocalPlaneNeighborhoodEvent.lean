import Certificate.LocalPlaneEmbedding
import Certificate.LocalTreeShapeMass
import Mathlib.Data.Sum.Order

/-!
# Exact finite graph event for an ordered tree placement

The neighbors of every interior shape vertex determine precisely the
tested array positions. Their equality to the parent and children lists
is equivalent to the marked cylinder with all other tested edges absent.
-/

open Set

namespace Certificate.LocalExploration

/-- Ordered bipartite labels for the two classes of the finite graph. -/
abbrev PlaneVertex (n : ℕ) := Lex (Fin n ⊕ Fin n)

/-- The neighbors induced by any predicate on the bipartite array. -/
def planeBipartiteNeighbors {n : ℕ} (P : Fin n × Fin n → Prop)
    (v : PlaneVertex n) : Set (PlaneVertex n) :=
  {w | ∃ i j, P (i,j) ∧
    ((v = toLex (Sum.inl i) ∧ w = toLex (Sum.inr j)) ∨
     (v = toLex (Sum.inr j) ∧ w = toLex (Sum.inl i)))}

private theorem left_ne_right {n : ℕ} (i j : Fin n) :
    (toLex (Sum.inl i) : PlaneVertex n) ≠ toLex (Sum.inr j) :=
  fun h => Sum.inl_ne_inr (congrArg ofLex h)

private theorem planeBipartiteNeighbors_symm {n : ℕ} {P : Fin n × Fin n → Prop}
    {v w : PlaneVertex n} (h : w ∈ planeBipartiteNeighbors P v) :
    v ∈ planeBipartiteNeighbors P w := by
  rcases h with ⟨i, j, hp, ⟨hv, hw⟩ | ⟨hv, hw⟩⟩
  · exact ⟨i, j, hp, Or.inr ⟨hw, hv⟩⟩
  · exact ⟨i, j, hp, Or.inl ⟨hw, hv⟩⟩

@[simp] theorem mem_planeBipartiteNeighbors_left_right {n : ℕ} {P : Fin n × Fin n → Prop}
    (i j : Fin n) :
    toLex (Sum.inr j) ∈ planeBipartiteNeighbors P (toLex (Sum.inl i)) ↔ P (i,j) := by
  constructor
  · rintro ⟨i', j', hp, ⟨hi, hj⟩ | ⟨hne, _⟩⟩
    · have hi' := Sum.inl.inj (congrArg ofLex hi)
      have hj' := Sum.inr.inj (congrArg ofLex hj)
      rwa [hi', hj']
    · exact (left_ne_right _ _ hne).elim
  · exact fun hp => ⟨i, j, hp, Or.inl ⟨rfl, rfl⟩⟩

@[simp] theorem mem_planeBipartiteNeighbors_right_left {n : ℕ} {P : Fin n × Fin n → Prop}
    (i j : Fin n) :
    toLex (Sum.inl i) ∈ planeBipartiteNeighbors P (toLex (Sum.inr j)) ↔ P (i,j) :=
  ⟨fun h => (mem_planeBipartiteNeighbors_left_right i j).mp (planeBipartiteNeighbors_symm h),
    fun h => planeBipartiteNeighbors_symm ((mem_planeBipartiteNeighbors_left_right i j).mpr h)⟩

/-- Evaluate an array edge using the original iid law's coordinates. -/
def planeRetainedPredicate {n : ℕ} (C : CostArray) (A : Set ℝ) (e : Fin n × Fin n) : Prop :=
  C (e.1.val, e.2.val) ∈ A

private theorem mem_labelledNeighborhoodEvent_iff {n : ℕ} (L R : Finset (Fin n))
    (E : Finset (Fin n × Fin n)) (hE : E ⊆ neighborhoodTestedEdges L R)
    (A : Set ℝ) (C : CostArray) :
    C ∈ labelledNeighborhoodEvent L R E A (fun _ => univ) ↔
      ∀ e ∈ neighborhoodTestedEdges L R, planeRetainedPredicate C A e ↔ e ∈ E := by
  constructor
  · intro h e he
    constructor
    · intro hp
      by_contra hn
      exact h.2 e (Finset.mem_sdiff.mpr ⟨he, hn⟩) hp
    · exact fun hE' => (h.1 e hE').1
  · intro h
    exact ⟨fun e he => ⟨(h e (hE he)).mpr he, mem_univ _⟩, fun e he hp =>
      (Finset.mem_sdiff.mp he).2 ((h e (Finset.mem_sdiff.mp he).1).mp hp)⟩

private theorem tested_iff_interior {n : ℕ} (L R : Finset (Fin n)) (i j : Fin n) :
    (i,j) ∈ neighborhoodTestedEdges L R ↔ i ∈ L ∨ j ∈ R := by
  simp [neighborhoodTestedEdges]

private theorem tested_agreement_iff_neighborAgreement {n : ℕ}
    (shape : PlaneShape) (label : List ℕ → PlaneVertex n) (L R : Finset (Fin n))
    (hL : ∀ i, i ∈ L ↔ ∃ v ∈ shape.slots, v.length < shape.depth ∧ label v = toLex (Sum.inl i))
    (hR : ∀ j, j ∈ R ↔ ∃ v ∈ shape.slots, v.length < shape.depth ∧ label v = toLex (Sum.inr j))
    (P Q : Fin n × Fin n → Prop) :
    (∀ e ∈ neighborhoodTestedEdges L R, P e ↔ Q e) ↔
      ∀ v ∈ shape.slots, v.length < shape.depth →
        planeBipartiteNeighbors P (label v) = planeBipartiteNeighbors Q (label v) := by
  constructor
  · intro h v hv hd
    have htest (i j : Fin n)
        (hside : label v = toLex (Sum.inl i) ∨ label v = toLex (Sum.inr j)) :
        (i,j) ∈ neighborhoodTestedEdges L R := by
      apply (tested_iff_interior L R i j).mpr
      exact hside.elim (fun hi => Or.inl ((hL i).mpr ⟨v, hv, hd, hi⟩))
        (fun hj => Or.inr ((hR j).mpr ⟨v, hv, hd, hj⟩))
    ext w
    constructor
    · rintro ⟨i, j, hp, hw⟩
      exact ⟨i, j, (h _ (htest i j (hw.imp And.left And.left))).mp hp, hw⟩
    · rintro ⟨i, j, hq, hw⟩
      exact ⟨i, j, (h _ (htest i j (hw.imp And.left And.left))).mpr hq, hw⟩
  · rintro h ⟨i, j⟩ ht
    rcases (tested_iff_interior L R i j).mp ht with hi | hj
    · obtain ⟨v, hv, hd, he⟩ := (hL i).mp hi
      have heq := h v hv hd
      rw [he] at heq
      rw [← mem_planeBipartiteNeighbors_left_right (P := P) i j,
        ← mem_planeBipartiteNeighbors_left_right (P := Q) i j,
        heq]
    · obtain ⟨v, hv, hd, he⟩ := (hR j).mp hj
      have heq := h v hv hd
      rw [he] at heq
      rw [← mem_planeBipartiteNeighbors_right_left (P := P) i j,
        ← mem_planeBipartiteNeighbors_right_left (P := Q) i j,
        heq]

/-- The singleton parent label at a nonroot word, and the empty set at
the root. This agrees with the parent exclusion in MatchesPlaneShape. -/
def planeParentLabels {V : Type*} (label : List ℕ → V) (v : List ℕ) : Set V :=
  if v = [] then ∅ else {label v.dropLast}

/-- The set of the fixed ordered children's labels. -/
def planeChildLabels {V : Type*} (shape : PlaneShape) (label : List ℕ → V)
    (v : List ℕ) : Set V :=
  range (fun i : Fin (shape.childCount v) => label (v ++ [i.val]))

private theorem planeParentLabels_disjoint_childLabels {V : Type*}
    {shape : PlaneShape} {label : List ℕ → V} (hlabel : InjOn label shape.slots)
    {v : List ℕ} (hv : v ∈ shape.slots) (hd : v.length < shape.depth) :
    Disjoint (planeParentLabels label v) (planeChildLabels shape label v) := by
  by_cases hroot : v = []
  · simp [planeParentLabels, hroot]
  · have hlast : v.dropLast ++ [v.getLast hroot] = v := List.dropLast_append_getLast hroot
    have hpar : v.dropLast ∈ shape.slots :=
      ((shape.child_mem ..).mp (hlast.symm ▸ hv)).1
    rw [Set.disjoint_left]
    rintro w hw ⟨i, hi⟩
    have hw' : w = label v.dropLast := by
      simpa only [planeParentLabels, if_neg hroot, mem_singleton_iff] using hw
    have hc : v ++ [i.val] ∈ shape.slots := (shape.child_mem ..).mpr ⟨hv, hd, i.isLt⟩
    have heq := hlabel hc hpar (hi.trans hw')
    have hlen := congrArg List.length heq
    have hlastlen := congrArg List.length hlast
    simp only [List.length_append, List.length_cons, List.length_nil, zero_add] at hlen hlastlen
    omega

private theorem planeParentLabels_subset_neighbors_of_matches {n : ℕ}
    {P : Fin n × Fin n → Prop} {shape : PlaneShape} {root : PlaneVertex n}
    {label : List ℕ → PlaneVertex n}
    (hm : MatchesPlaneShape shape root (planeBipartiteNeighbors P) label)
    {v : List ℕ} (hv : v ∈ shape.slots) :
    planeParentLabels label v ⊆ planeBipartiteNeighbors P (label v) := by
  by_cases hroot : v = []
  · simp [planeParentLabels, hroot]
  · let u := v.dropLast
    let i := v.getLast hroot
    have he : u ++ [i] = v := List.dropLast_append_getLast hroot
    have hs := (shape.child_mem u i).mp (he.symm ▸ hv)
    have heq : planeBipartiteNeighbors P (label u) \ planeParentLabels label u =
        planeChildLabels shape label u := (hm.2 u hs.1 hs.2.1).2
    have hV : label v ∈ planeChildLabels shape label u :=
      ⟨⟨i, hs.2.2⟩, congrArg label he⟩
    have hn := planeBipartiteNeighbors_symm (show label v ∈ planeBipartiteNeighbors P (label u) from
      (show label v ∈ planeBipartiteNeighbors P (label u) \ planeParentLabels label u from
        heq.symm ▸ hV).1)
    intro w hw
    have hw' : w = label u := by
      simpa only [planeParentLabels, if_neg hroot, mem_singleton_iff] using hw
    rwa [hw']

/-- For a fixed injective ordered placement, the exact retained graph
event is the cylinder prescribed by the images of its interior vertices
and edges. The test on each retained edge can be added separately. -/
theorem matchesPlaneShape_iff_labelledNeighborhoodEvent {n : ℕ}
    (shape : PlaneShape) (root : PlaneVertex n) (label : List ℕ → PlaneVertex n)
    (L R : Finset (Fin n)) (E : Finset (Fin n × Fin n))
    (hE : E ⊆ neighborhoodTestedEdges L R) (hroot : label [] = root)
    (hinj : InjOn label shape.slots)
    (hmono : ∀ v ∈ shape.slots, v.length < shape.depth →
      StrictMono (fun i : Fin (shape.childCount v) => label (v ++ [i.val])))
    (hL : ∀ i, i ∈ L ↔ ∃ v ∈ shape.slots, v.length < shape.depth ∧ label v = toLex (Sum.inl i))
    (hR : ∀ j, j ∈ R ↔ ∃ v ∈ shape.slots, v.length < shape.depth ∧ label v = toLex (Sum.inr j))
    (hEdge : ∀ v ∈ shape.slots, v.length < shape.depth →
      planeBipartiteNeighbors (fun e => e ∈ E) (label v) =
        planeParentLabels label v ∪ planeChildLabels shape label v)
    (A : Set ℝ) (C : CostArray) :
    MatchesPlaneShape shape root (planeBipartiteNeighbors (planeRetainedPredicate C A)) label ↔
      C ∈ labelledNeighborhoodEvent L R E A (fun _ => univ) := by
  rw [mem_labelledNeighborhoodEvent_iff L R E hE,
    tested_agreement_iff_neighborAgreement shape label L R hL hR]
  constructor
  · intro hm v hv hd
    have hN : planeBipartiteNeighbors (planeRetainedPredicate C A) (label v) \
        planeParentLabels label v = planeChildLabels shape label v := (hm.2 v hv hd).2
    rw [hEdge v hv hd]
    have hParent := planeParentLabels_subset_neighbors_of_matches hm hv
    ext w
    constructor
    · intro hw
      by_cases hp : w ∈ planeParentLabels label v
      · exact Or.inl hp
      · exact Or.inr (hN ▸ (show w ∈ _ \ _ from ⟨hw, hp⟩))
    · rintro (hp | hc)
      · exact hParent hp
      · exact (show w ∈ planeBipartiteNeighbors (planeRetainedPredicate C A) (label v) \
          planeParentLabels label v from hN.symm ▸ hc).1
  · intro h
    refine ⟨hroot, fun v hv hd => ⟨hmono v hv hd, ?_⟩⟩
    change planeBipartiteNeighbors (planeRetainedPredicate C A) (label v) \
      planeParentLabels label v = planeChildLabels shape label v
    rw [h v hv hd, hEdge v hv hd]
    have hDisj := Set.disjoint_left.mp (planeParentLabels_disjoint_childLabels hinj hv hd)
    ext w
    constructor
    · rintro ⟨(hp | hc), hnot⟩
      · exact (hnot hp).elim
      · exact hc
    · exact fun hc => ⟨Or.inr hc, fun hp => hDisj hp hc⟩

end Certificate.LocalExploration

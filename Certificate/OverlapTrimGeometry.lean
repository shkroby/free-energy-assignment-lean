import Certificate.OverlapTrim
import Certificate.OverlapLocalSensitivity
import Certificate.OverlapLocalConcentration

/-! A single row affects only a bounded neighborhood in the trimmed graph. -/

open Finset MeasureTheory Set

namespace Certificate.Overlap

open OverlapBelief

/-- Retained short edges of a finite cost matrix. -/
noncomputable def shortEdgesOfRows (d κ R : ℝ) (n : ℕ)
    (x : Fin n → Fin n → ℝ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun e => lengthScale d κ n * x e.1 e.2 ≤ R)

/-- The degree-trimmed graph as a measurable function of the finite rows. -/
noncomputable def trimmedGraphOfRows (β d κ R : ℝ) (n D : ℕ)
    (x : Fin n → Fin n → ℝ) : WeightedGraph (Fin n ⊕ Fin n) (Fin n × Fin n) :=
  (squareWeightedGraph (fun i j => Real.exp (-β * (lengthScale d κ n * x i j)))
    (fun _ _ => Real.exp_nonneg _)).retain (trimDegrees D (shortEdgesOfRows d κ R n x))
      (Finset.subset_univ _)

/-- Extend the finite square by zero so that every finite input row
matrix can be used in the definitions on the infinite array. -/
def extendCostRows (n : ℕ) (x : Fin n → Fin n → ℝ) : CostArray :=
  fun e => if hi : e.1 < n then if hj : e.2 < n then x ⟨e.1,hi⟩ ⟨e.2,hj⟩ else 0 else 0

theorem measurable_extendCostRows (n : ℕ) : Measurable (extendCostRows n) := by
  apply measurable_pi_iff.mpr
  intro e
  unfold extendCostRows
  split_ifs
  · exact (measurable_pi_apply _).comp (measurable_pi_apply _)
  · exact measurable_const
  · exact measurable_const

@[simp] theorem costRows_extendCostRows (n : ℕ) (x : Fin n → Fin n → ℝ) :
    costRows n (extendCostRows n x) = x := by
  funext i j
  simp only [costRows,extendCostRows, dif_pos i.isLt,dif_pos j.isLt]

theorem trimmedGraphOfRows_costRows (β d κ R : ℝ) (n D : ℕ) (C : CostArray) :
    trimmedGraphOfRows β d κ R n D (costRows n C) = trimmedAssignmentGraph β d κ R n D C := rfl

theorem shortEdgesOfRows_agree_outside {d κ R : ℝ} {n : ℕ}
    {x y : Fin n → Fin n → ℝ} {r : Fin n} (h : ∀ i ≠ r, x i = y i) :
    ∀ e, e.1 ≠ r → (e ∈ shortEdgesOfRows d κ R n x ↔ e ∈ shortEdgesOfRows d κ R n y) := by
  intro e he
  simp only [shortEdgesOfRows, mem_filter, Finset.mem_univ, true_and, h e.1 he]

theorem measurableSet_shortEdgesOfRows_eq (d κ R : ℝ) (n : ℕ)
    (s : Finset (Fin n × Fin n)) :
    MeasurableSet {x : Fin n → Fin n → ℝ | shortEdgesOfRows d κ R n x = s} := by
  let A (e : Fin n × Fin n) := {x : Fin n → Fin n → ℝ |
    lengthScale d κ n * x e.1 e.2 ≤ R}
  let B (e : Fin n × Fin n) := if e ∈ s then A e else (A e)ᶜ
  have hA (e : Fin n × Fin n) : MeasurableSet (A e) := by
    have hx : Measurable (fun x : Fin n → Fin n → ℝ => x e.1 e.2) :=
      (measurable_pi_apply e.2).comp (measurable_pi_apply e.1)
    exact measurableSet_le (hx.const_mul (lengthScale d κ n)) measurable_const
  have hB (e : Fin n × Fin n) : MeasurableSet (B e) := by
    unfold B
    split_ifs
    · exact hA e
    · exact (hA e).compl
  have heq : {x | shortEdgesOfRows d κ R n x = s} = ⋂ e, B e := by
    ext x
    simp only [mem_ofPred_eq, mem_iInter, B]
    constructor
    · intro he e
      by_cases h : e ∈ s
      · have h' : e ∈ shortEdgesOfRows d κ R n x := he ▸ h
        simpa only [if_pos h, A, mem_ofPred_eq, shortEdgesOfRows, mem_filter,
          Finset.mem_univ, true_and] using h'
      · have h' : e ∉ shortEdgesOfRows d κ R n x := he ▸ h
        simpa only [if_neg h, A, mem_compl_iff, mem_ofPred_eq, shortEdgesOfRows, mem_filter,
          Finset.mem_univ, true_and] using h'
    · intro he
      apply Finset.ext
      intro e
      specialize he e
      by_cases h : e ∈ s
      · have h' : e ∈ shortEdgesOfRows d κ R n x := by
          simpa only [if_pos h, A, mem_ofPred_eq, shortEdgesOfRows, mem_filter,
            Finset.mem_univ, true_and] using he
        exact iff_of_true h' h
      · have h' : e ∉ shortEdgesOfRows d κ R n x := by
          simpa only [if_neg h, A, mem_compl_iff, mem_ofPred_eq, shortEdgesOfRows, mem_filter,
            Finset.mem_univ, true_and] using he
        exact iff_of_false h' h
  rw [heq]
  exact MeasurableSet.iInter hB

theorem measurableSet_trimmedGraphOfRows_edges_eq (β d κ R : ℝ) (n D : ℕ)
    (s : Finset (Fin n × Fin n)) :
    MeasurableSet {x : Fin n → Fin n → ℝ | (trimmedGraphOfRows β d κ R n D x).edges = s} := by
  classical
  let Q := {t : Finset (Fin n × Fin n) // trimDegrees D t = s}
  have heq : {x | (trimmedGraphOfRows β d κ R n D x).edges = s} =
      ⋃ t : Q, {x | shortEdgesOfRows d κ R n x = t.val} := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · intro h
      exact ⟨⟨shortEdgesOfRows d κ R n x,h⟩,rfl⟩
    · rintro ⟨⟨t,ht⟩,rfl⟩
      exact ht
  rw [heq]
  exact MeasurableSet.iUnion fun t => measurableSet_shortEdgesOfRows_eq d κ R n t.val

/-- At most D edges are incident to any vertex after degree trimming. -/
theorem card_incidentEdges_trimmedGraphOfRows_le (β d κ R : ℝ) (n D : ℕ)
    (x : Fin n → Fin n → ℝ) (v : Fin n ⊕ Fin n) :
    (incidentEdges (trimmedGraphOfRows β d κ R n D x) v).card ≤ D := by
  let s := shortEdgesOfRows d κ R n x
  cases v with
  | inl i =>
    have hi : incidentEdges (trimmedGraphOfRows β d κ R n D x) (Sum.inl i) =
        rowEdges (trimDegrees D s) i := by
      ext e
      simp [incidentEdges, trimmedGraphOfRows, rowEdges, s, WeightedGraph.retain, squareWeightedGraph,
        Tree.Bipartite.ends, eq_comm]
    rw [hi]
    exact rowEdges_trimDegrees_card_le _ _ _
  | inr j =>
    have hj : incidentEdges (trimmedGraphOfRows β d κ R n D x) (Sum.inr j) =
        colEdges (trimDegrees D s) j := by
      ext e
      simp [incidentEdges, trimmedGraphOfRows, colEdges, s, WeightedGraph.retain, squareWeightedGraph,
        Tree.Bipartite.ends, eq_comm]
    rw [hj]
    exact colEdges_trimDegrees_card_le _ _ _

set_option maxHeartbeats 1000000 in
/-- Replacing one input row changes the weighted graph only near a
bounded set of affected vertices. -/
theorem exists_trimmedGraphOfRows_affectedVertices {β d κ R : ℝ} {n : ℕ} (D k : ℕ)
    (x y : Fin n → Fin n → ℝ) (r : Fin n) (h : ∀ i ≠ r, x i = y i) :
    let G := trimmedGraphOfRows β d κ R n D x
    let H := trimmedGraphOfRows β d κ R n D y
    ∃ bad : Finset (Fin n × Fin n),
      (∀ e ∉ bad, (e ∈ G.edges ↔ e ∈ H.edges) ∧
        (e ∈ G.edges → G.weight e = H.weight e)) ∧
      (affectedVertices G.ends (G.edges ∪ H.edges) bad k).card ≤
        2 * (4*D^2 + 2*D) * (1+2*(2*D))^k := by
  let G := trimmedGraphOfRows β d κ R n D x
  let H := trimmedGraphOfRows β d κ R n D y
  let A := G.edges
  let B := H.edges
  let bad := (A \ B) ∪ (B \ A) ∪ rowEdges (A ∪ B) r
  have hdegree (v : Fin n ⊕ Fin n) :
      ((A∪B).filter fun e => v ∈ G.ends e).card ≤ 2*D := by
    have hsplit : (A∪B).filter (fun e => v ∈ G.ends e) =
        incidentEdges G v ∪ incidentEdges H v := by
      ext e
      simp only [incidentEdges, mem_filter, Finset.mem_union]
      change (e ∈ A ∨ e ∈ B) ∧ v ∈ Tree.Bipartite.ends e ↔ _
      tauto
    rw [hsplit]
    refine (Finset.card_union_le _ _).trans ?_
    simpa only [two_mul] using add_le_add
      (card_incidentEdges_trimmedGraphOfRows_le β d κ R n D x v)
      (card_incidentEdges_trimmedGraphOfRows_le β d κ R n D y v)
  have hrow : (rowEdges (A ∪ B) r).card ≤ 2*D := by
    have hr : rowEdges (A ∪ B) r = (A∪B).filter (fun e => Sum.inl r ∈ G.ends e) := by
      ext e
      simp [A, B, G, H, trimmedGraphOfRows, rowEdges, Tree.Bipartite.ends,
        WeightedGraph.retain, squareWeightedGraph, eq_comm]
    rw [hr]
    exact hdegree (Sum.inl r)
  have hbad : bad.card ≤ 4*D^2 + 2*D :=
    (Finset.card_union_le _ _).trans (add_le_add
      (card_trimDegrees_changedEdges_le D r (shortEdgesOfRows_agree_outside (d := d) (κ := κ) (R := R) h))
      hrow)
  have hsub : bad ⊆ A ∪ B := by
    intro e he
    rcases mem_union.mp he with he | he
    · rcases mem_union.mp he with he | he
      · exact mem_union_left _ (mem_sdiff.mp he).1
      · exact mem_union_right _ (mem_sdiff.mp he).1
    · exact (mem_filter.mp he).1
  refine ⟨bad, ?_, ?_⟩
  · intro e hn
    have hAB : e ∈ A ↔ e ∈ B := by
      constructor
      · intro he
        by_contra ht
        exact hn (mem_union_left _ (mem_union_left _ (mem_sdiff.mpr ⟨he,ht⟩)))
      · intro he
        by_contra ht
        exact hn (mem_union_left _ (mem_union_right _ (mem_sdiff.mpr ⟨he,ht⟩)))
    refine ⟨hAB, fun he => ?_⟩
    have hne : e.1 ≠ r := fun hr => hn (mem_union_right _
      (mem_filter.mpr ⟨mem_union_left _ he,hr⟩))
    change Real.exp (-β * (lengthScale d κ n * x e.1 e.2)) =
      Real.exp (-β * (lengthScale d κ n * y e.1 e.2))
    rw [h _ hne]
  · exact (card_affectedVertices_le G.ends (A∪B) bad hsub
      (fun e _ => (Tree.Bipartite.ends_card e).le) hdegree k).trans (by gcongr)

end Certificate.Overlap

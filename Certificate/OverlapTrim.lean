import Certificate.SoftAssignment

/-! Degree truncation for the locally tree-like graphs in the overlap proof. -/

open Finset

namespace Certificate.Overlap

variable {L R : Type*} [DecidableEq L] [DecidableEq R]

/-- The edges in one row of a finite bipartite graph. -/
def rowEdges (S : Finset (L × R)) (i : L) : Finset (L × R) :=
  S.filter (fun e => e.1 = i)

/-- The edges in one column of a finite bipartite graph. -/
def colEdges (S : Finset (L × R)) (j : R) : Finset (L × R) :=
  S.filter (fun e => e.2 = j)

/-- Delete every edge at rows whose degree exceeds the bound. -/
def trimRows (D : ℕ) (S : Finset (L × R)) : Finset (L × R) :=
  S.filter (fun e => (rowEdges S e.1).card ≤ D)

/-- After cutting the rows, delete every edge at columns of excess degree. -/
def trimDegrees (D : ℕ) (S : Finset (L × R)) : Finset (L × R) :=
  (trimRows D S).filter (fun e => (colEdges (trimRows D S) e.2).card ≤ D)

omit [DecidableEq R] in
theorem trimRows_subset (D : ℕ) (S : Finset (L × R)) : trimRows D S ⊆ S :=
  Finset.filter_subset _ _

theorem trimDegrees_subset_rows (D : ℕ) (S : Finset (L × R)) :
    trimDegrees D S ⊆ trimRows D S := Finset.filter_subset _ _

theorem trimDegrees_subset (D : ℕ) (S : Finset (L × R)) : trimDegrees D S ⊆ S :=
  (trimDegrees_subset_rows D S).trans (trimRows_subset D S)

omit [DecidableEq R] in
private theorem rowEdges_mono {S T : Finset (L × R)} (h : S ⊆ T) (i : L) :
    rowEdges S i ⊆ rowEdges T i := Finset.filter_subset_filter _ h

omit [DecidableEq L] in
private theorem colEdges_mono {S T : Finset (L × R)} (h : S ⊆ T) (j : R) :
    colEdges S j ⊆ colEdges T j := Finset.filter_subset_filter _ h

omit [DecidableEq R] in
theorem rowEdges_trimRows_card_le (D : ℕ) (S : Finset (L × R)) (i : L) :
    (rowEdges (trimRows D S) i).card ≤ D := by
  by_cases h : (rowEdges S i).card ≤ D
  · exact (card_le_card (rowEdges_mono (trimRows_subset D S) i)).trans h
  · have heq : rowEdges (trimRows D S) i = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro e he
      obtain ⟨heS, hei⟩ := mem_filter.mp he
      exact h (hei ▸ (mem_filter.mp heS).2)
    simp [heq]

theorem rowEdges_trimDegrees_card_le (D : ℕ) (S : Finset (L × R)) (i : L) :
    (rowEdges (trimDegrees D S) i).card ≤ D :=
  (card_le_card (rowEdges_mono (trimDegrees_subset_rows D S) i)).trans
    (rowEdges_trimRows_card_le D S i)

theorem colEdges_trimDegrees_card_le (D : ℕ) (S : Finset (L × R)) (j : R) :
    (colEdges (trimDegrees D S) j).card ≤ D := by
  by_cases h : (colEdges (trimRows D S) j).card ≤ D
  · exact (card_le_card (colEdges_mono (trimDegrees_subset_rows D S) j)).trans h
  · have heq : colEdges (trimDegrees D S) j = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro e he
      obtain ⟨heS, hej⟩ := mem_filter.mp he
      exact h (hej ▸ (mem_filter.mp heS).2)
    simp [heq]

/-- Each discarded edge is incident to a row or column whose degree already
exceeded the cap in the original graph. -/
theorem trimDegree_discarded_subset (D : ℕ) (S : Finset (L × R)) :
    S \ trimDegrees D S ⊆
      S.filter (fun e => D < (rowEdges S e.1).card) ∪
        S.filter (fun e => D < (colEdges S e.2).card) := by
  intro e he
  obtain ⟨heS, heT⟩ := mem_sdiff.mp he
  by_cases hr : (rowEdges S e.1).card ≤ D
  · have hrow : e ∈ trimRows D S := mem_filter.mpr ⟨heS, hr⟩
    have hc : D < (colEdges (trimRows D S) e.2).card :=
      lt_of_not_ge fun h => heT (mem_filter.mpr ⟨hrow, h⟩)
    exact mem_union_right _ (mem_filter.mpr ⟨heS,
      hc.trans_le (card_le_card (colEdges_mono (trimRows_subset D S) e.2))⟩)
  · exact mem_union_left _ (mem_filter.mpr ⟨heS, lt_of_not_ge hr⟩)

/-- The count of discarded edges is bounded by the sum of the high original
degrees on the two sides. -/
theorem card_trimDegree_discarded_le [Fintype L] [Fintype R] (D : ℕ)
    (S : Finset (L × R)) :
    (S \ trimDegrees D S).card ≤
      (∑ i, if D < (rowEdges S i).card then (rowEdges S i).card else 0) +
      ∑ j, if D < (colEdges S j).card then (colEdges S j).card else 0 := by
  have hrow : (S.filter (fun e => D < (rowEdges S e.1).card)).card =
      ∑ i, if D < (rowEdges S i).card then (rowEdges S i).card else 0 := by
    rw [card_eq_sum_card_fiberwise (f := Prod.fst)
      (t := Finset.univ) (fun _ _ => mem_univ _)]
    apply sum_congr rfl
    intro i _
    by_cases h : D < (rowEdges S i).card
    · rw [if_pos h]
      apply congrArg Finset.card
      ext e
      simp only [mem_filter, rowEdges]
      exact ⟨fun hh => ⟨(mem_filter.mp hh.1).1, hh.2⟩,
        fun hh => ⟨mem_filter.mpr ⟨hh.1, hh.2.symm ▸ h⟩, hh.2⟩⟩
    · rw [if_neg h]
      apply card_eq_zero.mpr
      apply eq_empty_iff_forall_notMem.mpr
      intro e he
      obtain ⟨heS, hi⟩ := mem_filter.mp he
      exact h (hi ▸ (mem_filter.mp heS).2)
  have hcol : (S.filter (fun e => D < (colEdges S e.2).card)).card =
      ∑ j, if D < (colEdges S j).card then (colEdges S j).card else 0 := by
    rw [card_eq_sum_card_fiberwise (f := Prod.snd)
      (t := Finset.univ) (fun _ _ => mem_univ _)]
    apply sum_congr rfl
    intro j _
    by_cases h : D < (colEdges S j).card
    · rw [if_pos h]
      apply congrArg Finset.card
      ext e
      simp only [mem_filter, colEdges]
      exact ⟨fun hh => ⟨(mem_filter.mp hh.1).1, hh.2⟩,
        fun hh => ⟨mem_filter.mpr ⟨hh.1, hh.2.symm ▸ h⟩, hh.2⟩⟩
    · rw [if_neg h]
      apply card_eq_zero.mpr
      apply eq_empty_iff_forall_notMem.mpr
      intro e he
      obtain ⟨heS, hj⟩ := mem_filter.mp he
      exact h (hj ▸ (mem_filter.mp heS).2)
  calc
    _ ≤ (S.filter (fun e => D < (rowEdges S e.1).card) ∪
          S.filter (fun e => D < (colEdges S e.2).card)).card :=
      card_le_card (trimDegree_discarded_subset D S)
    _ ≤ _ := by
      rw [← hrow, ← hcol]
      exact card_union_le _ _

omit [DecidableEq R] in
private theorem trimRows_agree_outside {S T : Finset (L × R)} (D : ℕ) (r : L)
    (h : ∀ e, e.1 ≠ r → (e ∈ S ↔ e ∈ T)) :
    ∀ e, e.1 ≠ r → (e ∈ trimRows D S ↔ e ∈ trimRows D T) := by
  intro e hr
  have heq : rowEdges S e.1 = rowEdges T e.1 := by
    ext u
    simp only [rowEdges, mem_filter]
    constructor
    · rintro ⟨hu, he⟩
      exact ⟨(h u (he.trans_ne hr)).mp hu, he⟩
    · rintro ⟨hu, he⟩
      exact ⟨(h u (he.trans_ne hr)).mpr hu, he⟩
  simp only [trimRows, mem_filter, heq, h e hr]

private theorem card_sdiff_rowTrim_le {S T : Finset (L × R)} (D : ℕ) (r : L)
    (h : ∀ e, e.1 ≠ r → (e ∈ S ↔ e ∈ T)) :
    (trimRows D S \ trimRows D T).card ≤ D := by
  apply (card_le_card (t := rowEdges (trimRows D S) r) ?_).trans
    (rowEdges_trimRows_card_le D S r)
  intro e he
  obtain ⟨heS, heT⟩ := mem_sdiff.mp he
  exact mem_filter.mpr ⟨heS, by_contra fun hn =>
    heT ((trimRows_agree_outside D r h e hn).mp heS)⟩

/-- Changing an arbitrary row changes at most (4D^2) retained edges after
the degree cutoff. Affected columns are among those reached by the changed
edges after the first cutoff. -/
theorem card_trimDegrees_changedEdges_le {S T : Finset (L × R)} (D : ℕ) (r : L)
    (h : ∀ e, e.1 ≠ r → (e ∈ S ↔ e ∈ T)) :
    ((trimDegrees D S \ trimDegrees D T) ∪ (trimDegrees D T \ trimDegrees D S)).card ≤
      4 * D^2 := by
  let A := trimRows D S
  let B := trimRows D T
  let cols := ((A \ B) ∪ (B \ A)).image Prod.snd
  have hcols : cols.card ≤ 2 * D := by
    calc
      _ ≤ ((A \ B) ∪ (B \ A)).card := card_image_le
      _ ≤ (A \ B).card + (B \ A).card := card_union_le _ _
      _ ≤ D + D := add_le_add (card_sdiff_rowTrim_le D r h)
        (card_sdiff_rowTrim_le D r fun e he => (h e he).symm)
      _ = _ := by omega
  have hcol (j : R) (hj : j ∉ cols) : colEdges A j = colEdges B j := by
    ext e
    simp only [colEdges, mem_filter]
    constructor
    · rintro ⟨he, hcol⟩
      refine ⟨by_contra fun hn => hj ?_, hcol⟩
      exact mem_image.mpr ⟨e, mem_union_left _ (mem_sdiff.mpr ⟨he, hn⟩), hcol⟩
    · rintro ⟨he, hcol⟩
      refine ⟨by_contra fun hn => hj ?_, hcol⟩
      exact mem_image.mpr ⟨e, mem_union_right _ (mem_sdiff.mpr ⟨he, hn⟩), hcol⟩
  have hagree (e : L × R) (he : e.2 ∉ cols) :
      e ∈ trimDegrees D S ↔ e ∈ trimDegrees D T := by
    have hc := hcol e.2 he
    have hab : e ∈ A ↔ e ∈ B := by
      have hm : e ∈ colEdges A e.2 ↔ e ∈ colEdges B e.2 := by rw [hc]
      simpa only [colEdges, mem_filter, and_true] using hm
    simp only [trimDegrees, mem_filter]
    change (e ∈ A ∧ (colEdges A e.2).card ≤ D) ↔
      (e ∈ B ∧ (colEdges B e.2).card ≤ D)
    rw [hab, hc]
  have hfiber (U : Finset (L × R)) (hU : ∀ j, (colEdges U j).card ≤ D) :
      (U.filter (fun e => e.2 ∈ cols)).card ≤ cols.card * D := by
    rw [← sum_card_fiberwise_eq_card_filter U cols Prod.snd]
    calc
      _ ≤ ∑ _j ∈ cols, D := sum_le_sum fun j _ => hU j
      _ = _ := by simp
  have hd₁ : trimDegrees D S \ trimDegrees D T ⊆
      (trimDegrees D S).filter (fun e => e.2 ∈ cols) := by
    intro e hE
    obtain ⟨hS, hT⟩ := mem_sdiff.mp hE
    exact mem_filter.mpr ⟨hS, by_contra fun he => hT ((hagree e he).mp hS)⟩
  have hd₂ : trimDegrees D T \ trimDegrees D S ⊆
      (trimDegrees D T).filter (fun e => e.2 ∈ cols) := by
    intro e hE
    obtain ⟨hT, hS⟩ := mem_sdiff.mp hE
    exact mem_filter.mpr ⟨hT, by_contra fun he => hS ((hagree e he).mpr hT)⟩
  calc
    _ ≤ (trimDegrees D S \ trimDegrees D T).card +
        (trimDegrees D T \ trimDegrees D S).card := card_union_le _ _
    _ ≤ cols.card * D + cols.card * D := add_le_add
      ((card_le_card hd₁).trans
        (hfiber _ (colEdges_trimDegrees_card_le D S)))
      ((card_le_card hd₂).trans
        (hfiber _ (colEdges_trimDegrees_card_le D T)))
    _ ≤ (2 * D) * D + (2 * D) * D := by gcongr
    _ = _ := by ring

/-- The assignment graph keeping only short edges and trimming degrees. -/
noncomputable def trimmedAssignmentGraph (β d κ Rcut : ℝ) (n D : ℕ) (C : CostArray) :
    WeightedGraph (Fin n ⊕ Fin n) (Fin n × Fin n) :=
  (assignmentGraph β d κ n C).retain (trimDegrees D (retainedEdges d κ Rcut n C))
    (subset_univ _)

end Certificate.Overlap

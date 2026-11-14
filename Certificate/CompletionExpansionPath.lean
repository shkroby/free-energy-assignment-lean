import Certificate.CompletionProbability
import Certificate.CompletionPath

/-!
# Augmenting directly between free endpoints

If the deficit is at least `n / 40`, select free subsets on opposite sides.
The common expansion event's cut condition supplies a one-edge augmentation.
-/

open Finset

namespace Certificate.Completion

/-- Rows not used by a matching. -/
noncomputable def freeRows {n : ℕ} (m : Fin n → Option (Fin n)) : Finset (Fin n) :=
  univ \ AugmentingPath.matchedRows m

/-- Columns used by a matching. -/
noncomputable def matchedCols {n : ℕ} (m : Fin n → Option (Fin n)) : Finset (Fin n) :=
  open Classical in
  univ.filter (fun j => ∃ i, m i = some j)

/-- Columns not used by a matching. -/
noncomputable def freeCols {n : ℕ} (m : Fin n → Option (Fin n)) : Finset (Fin n) :=
  univ \ matchedCols m

@[simp] theorem mem_freeRows {n : ℕ} {m : Fin n → Option (Fin n)} {i : Fin n} :
    i ∈ freeRows m ↔ m i = none := by
  classical
  simp [freeRows]

@[simp] theorem mem_matchedCols {n : ℕ} {m : Fin n → Option (Fin n)} {j : Fin n} :
    j ∈ matchedCols m ↔ ∃ i, m i = some j := by
  classical
  simp [matchedCols]

@[simp] theorem mem_freeCols {n : ℕ} {m : Fin n → Option (Fin n)} {j : Fin n} :
    j ∈ freeCols m ↔ ∀ i, m i ≠ some j := by
  classical
  simp [freeCols]

theorem freeRows_card {n : ℕ} (m : Fin n → Option (Fin n)) :
    (freeRows m).card = n - (AugmentingPath.matchedRows m).card := by
  rw [freeRows, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simp

private theorem exists_matchedCol {n : ℕ} {m : Fin n → Option (Fin n)}
    (i : AugmentingPath.matchedRows m) : ∃ j, m i.val = some j := by
  have h := AugmentingPath.mem_matchedRows.mp i.property
  cases hmi : m i.val with
  | none => exact (h hmi).elim
  | some j => exact ⟨j, rfl⟩

theorem matchedCols_card {n : ℕ} {m : Fin n → Option (Fin n)} (hm : IsMatching m) :
    (matchedCols m).card = (AugmentingPath.matchedRows m).card := by
  classical
  let col (i : AugmentingPath.matchedRows m) : Fin n := Classical.choose (exists_matchedCol i)
  have hcol (i : AugmentingPath.matchedRows m) : m i.val = some (col i) :=
    Classical.choose_spec (exists_matchedCol i)
  let matchCol (i : AugmentingPath.matchedRows m) : matchedCols m :=
    ⟨col i, mem_matchedCols.mpr ⟨i.val, hcol i⟩⟩
  have hbij : Function.Bijective matchCol := by
    constructor
    · intro i i' hi
      apply Subtype.ext
      exact hm (hcol i) ((hcol i').trans (congrArg some (congrArg Subtype.val hi).symm))
    · intro j
      obtain ⟨i, hi⟩ := mem_matchedCols.mp j.property
      let i' : AugmentingPath.matchedRows m :=
        ⟨i, AugmentingPath.mem_matchedRows.mpr (by simp [hi])⟩
      exact ⟨i', Subtype.ext (Option.some.inj ((hcol i').symm.trans hi))⟩
  simpa only [Fintype.card_coe] using (Fintype.card_congr (Equiv.ofBijective matchCol hbij)).symm

theorem freeCols_card {n : ℕ} {m : Fin n → Option (Fin n)} (hm : IsMatching m) :
    (freeCols m).card = n - (AugmentingPath.matchedRows m).card := by
  rw [freeCols, Finset.card_sdiff_of_subset (Finset.subset_univ _), matchedCols_card hm]
  simp

/-- A path's proposed new edges are all cheap at threshold `t`. -/
def AugmentingPath.IsCheap {n k : ℕ} {m : Fin n → Option (Fin n)}
    (p : AugmentingPath m k) (C : CostArray) (t : ℝ) : Prop :=
  ∀ i, C ((p.rows i).val, (p.cols i).val) ≤ t

/-- For a large deficit the common good event gives a one-edge augmenting path
for every matching with that deficit. -/
theorem exists_cheap_singleAugmentation_of_not_mem_commonFailure
    {n : ℕ} {cutoff : ℕ → ℝ} {C : CostArray} {m : Fin n → Option (Fin n)}
    (hC : C ∉ commonExpansionFailure n cutoff) (hm : IsMatching m)
    {j : ℕ} (hj : 0 < j) (hjn : j ≤ n) (hjh : n / 40 ≤ j)
    (hdeficit : n - (AugmentingPath.matchedRows m).card = j) :
    ∃ p : AugmentingPath m 0, p.IsCheap C (cutoff j) := by
  have hL : n / 40 ≤ (freeRows m).card := by rw [freeRows_card, hdeficit]; exact hjh
  have hR : n / 40 ≤ (freeCols m).card := by rw [freeCols_card hm, hdeficit]; exact hjh
  obtain ⟨S, hS, hcS⟩ := Finset.exists_subset_card_eq hL
  obtain ⟨T, hT, hcT⟩ := Finset.exists_subset_card_eq hR
  obtain ⟨i, hi, k, hk, hcheap⟩ := cheapEdge_of_not_mem_commonFailure hC hj hjn S T hcS hcT
  let p : AugmentingPath m 0 :=
    { rows := ⟨fun _ => i, fun a b _ => Fin.ext (by have ha := a.isLt; have hb := b.isLt; omega)⟩
      cols := ⟨fun _ => k, fun a b _ => Fin.ext (by have ha := a.isLt; have hb := b.isLt; omega)⟩
      startFree := mem_freeRows.mp (hS hi)
      matched := fun a => Fin.elim0 a
      endFree := mem_freeCols.mp (hT hk) }
  exact ⟨p, fun _ => hcheap⟩

/-- The counting step in a forest enlargement: tenfold expansion leaves four
times the number of outer vertices available after excluding at most six times
that many already visited vertices. -/
theorem freshCheapNeighbors_card_lower {n : ℕ}
    (byRow : Bool) (t : ℝ) (S visited : Finset (Fin n)) (C : CostArray)
    (hexp : 10 * S.card ≤ (cheapNeighbors byRow t S C).card) (hused : visited.card ≤ 6 * S.card) :
    4 * S.card ≤ (cheapNeighbors byRow t S C \ visited).card := by
  have h := Finset.card_le_card_sdiff_add_card
    (s := cheapNeighbors byRow t S C) (t := visited)
  omega

/-- Fresh neighbor columns can be attached using distinct matching partners.
Keeping mates together ensures that the returned pairs avoid the rows and
columns already visited. -/
theorem exists_freshCheapColumns_and_partners {n : ℕ} {m : Fin n → Option (Fin n)}
    (t : ℝ) (C : CostArray) (S usedRows usedCols : Finset (Fin n)) {r : ℕ}
    (hfree : freeCols m ⊆ usedCols)
    (hclosed : ∀ i ∈ usedRows, ∀ j, m i = some j → j ∈ usedCols)
    (hexp : 10 * S.card ≤ (cheapNeighbors true t S C).card)
    (hused : usedCols.card ≤ 6 * S.card) (hr : r ≤ 4 * S.card) :
    ∃ T : Finset (Fin n), T.card = r ∧ T ⊆ cheapNeighbors true t S C ∧
      Disjoint T usedCols ∧
      ∃ mate : T ↪ Fin n, ∀ j : T, m (mate j) = some j.val ∧ mate j ∉ usedRows := by
  obtain ⟨T, hT, hcard⟩ := Finset.exists_subset_card_eq
    (hr.trans (freshCheapNeighbors_card_lower true t S usedCols C hexp hused))
  have hfresh (j : T) : j.val ∉ usedCols := (Finset.mem_sdiff.mp (hT j.property)).2
  have hmatched (j : T) : ∃ i : Fin n, m i = some j.val := by
    by_contra! h
    exact hfresh j (hfree (mem_freeCols.mpr h))
  let f (j : T) := Classical.choose (hmatched j)
  have hf (j : T) : m (f j) = some j.val := Classical.choose_spec (hmatched j)
  have hinj : Function.Injective f := by
    intro j k h
    have h' := hf j
    rw [h] at h'
    exact Subtype.ext (Option.some.inj (h'.symm.trans (hf k)))
  refine ⟨T, hcard, fun j hj => (Finset.mem_sdiff.mp (hT hj)).1,
    Finset.disjoint_left.mpr (fun j hj => hfresh ⟨j, hj⟩), ⟨f, hinj⟩, ?_⟩
  intro j
  refine ⟨hf j, fun hj => hfresh j (hclosed _ hj _ (hf j))⟩

end Certificate.Completion

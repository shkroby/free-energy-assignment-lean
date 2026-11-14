import Certificate.CompletionExpansionWalk

/-!
# Bounded augmentations from cheap-edge expansion

The directed-walk representation permits forward and backward search without
requiring two disjoint forests. Repeated vertices can be removed at the end.
The one search step follows a cheap edge and, when necessary, the existing
matching edge incident to its destination column.
-/

open Finset
open scoped SetRel

namespace Certificate.Completion

private def FromFreeRow {n : ℕ} (m : Fin n → Option (Fin n)) (C : CostArray) (t : ℝ)
    (steps : ℕ) (v : Fin n ⊕ Fin n) : Prop :=
  ∃ i ∈ freeRows m, ∃ p : RelSeries (cheapArc m C t),
    p.head = Sum.inl i ∧ p.last = v ∧ p.length ≤ steps

private def ToFreeCol {n : ℕ} (m : Fin n → Option (Fin n)) (C : CostArray) (t : ℝ)
    (steps : ℕ) (v : Fin n ⊕ Fin n) : Prop :=
  ∃ j ∈ freeCols m, ∃ p : RelSeries (cheapArc m C t),
    p.head = v ∧ p.last = Sum.inr j ∧ p.length ≤ steps

private theorem fromFreeRow_step {n : ℕ} {m : Fin n → Option (Fin n)}
    {C : CostArray} {t : ℝ} {steps : ℕ} {a b : Fin n ⊕ Fin n}
    (h : FromFreeRow m C t steps a) (hab : a ~[cheapArc m C t] b) :
    FromFreeRow m C t (steps + 1) b := by
  obtain ⟨i, hi, p, hhead, hlast, hlen⟩ := h
  let q := p.snoc b (by rw [hlast]; exact hab)
  exact ⟨i, hi, q, by simpa [q] using hhead, by simp [q], by simpa [q] using hlen⟩

private theorem toFreeCol_step {n : ℕ} {m : Fin n → Option (Fin n)}
    {C : CostArray} {t : ℝ} {steps : ℕ} {a b : Fin n ⊕ Fin n}
    (h : ToFreeCol m C t steps b) (hab : a ~[cheapArc m C t] b) :
    ToFreeCol m C t (steps + 1) a := by
  obtain ⟨j, hj, p, hhead, hlast, hlen⟩ := h
  let q := p.cons a (by rw [hhead]; exact hab)
  exact ⟨j, hj, q, by simp [q], by simpa [q] using hlast, by simpa [q] using hlen⟩

private theorem hasAugmentingWalk_mono {n : ℕ} {m : Fin n → Option (Fin n)}
    {C : CostArray} {t : ℝ} {k l : ℕ}
    (hk : HasAugmentingWalk m C t k) (hkl : k ≤ l) : HasAugmentingWalk m C t l := by
  obtain ⟨i, hi, j, hj, p, ha, hb, hp⟩ := hk
  exact ⟨i, hi, j, hj, p, ha, hb, hp.trans hkl⟩

private theorem growForward {n : ℕ} {m : Fin n → Option (Fin n)}
    (hm : IsMatching m) {C : CostArray} {t : ℝ} {steps : ℕ} (S : Finset (Fin n))
    (hS : ∀ i ∈ S, FromFreeRow m C t steps (Sum.inl i)) {r : ℕ}
    (hr : r ≤ (cheapNeighbors true t S C).card)
    (hno : ¬ HasAugmentingWalk m C t (steps + 1)) :
    ∃ U : Finset (Fin n), U.card = r ∧
      ∀ i ∈ U, FromFreeRow m C t (steps + 1) (Sum.inl i) := by
  classical
  obtain ⟨T, hT, hcard⟩ := Finset.exists_subset_card_eq hr
  have hnext (j : T) : FromFreeRow m C t (steps + 1) (columnVertex m j.val) := by
    obtain ⟨i, hi, hcheap⟩ := (mem_cheapNeighbors true t S C j.val).mp (hT j.property)
    exact fromFreeRow_step (hS i hi) (cheapArc_to_columnVertex hcheap)
  have hmatch (j : T) : ∃ i : Fin n, m i = some j.val := by
    by_contra! hj
    have hj₀ : j.val ∈ freeCols m := mem_freeCols.mpr hj
    have he := hnext j
    rw [columnVertex_of_free hj₀] at he
    obtain ⟨i, hi, p, hhead, hlast, hlen⟩ := he
    exact hno ⟨i, hi, j.val, hj₀, p, hhead, hlast, hlen⟩
  let f (j : T) := Classical.choose (hmatch j)
  have hf (j : T) : m (f j) = some j.val := Classical.choose_spec (hmatch j)
  have hinj : Function.Injective f := by
    intro j k hjk
    have he := hf j
    rw [hjk] at he
    exact Subtype.ext (Option.some.inj (he.symm.trans (hf k)))
  let g : T ↪ Fin n := ⟨f, hinj⟩
  refine ⟨T.attach.map g, by simpa using hcard, ?_⟩
  intro i hi
  obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
  have he := hnext j
  rw [columnVertex_of_matched hm (hf j)] at he
  exact he

private theorem growBackward {n : ℕ} {m : Fin n → Option (Fin n)}
    (hm : IsMatching m) {C : CostArray} {t : ℝ} {steps : ℕ} (T : Finset (Fin n))
    (hT : ∀ j ∈ T, ToFreeCol m C t steps (columnVertex m j)) {r : ℕ}
    (hr : r ≤ (cheapNeighbors false t T C).card)
    (hno : ¬ HasAugmentingWalk m C t (steps + 1)) :
    ∃ U : Finset (Fin n), U.card = r ∧
      ∀ j ∈ U, ToFreeCol m C t (steps + 1) (columnVertex m j) := by
  classical
  obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq hr
  have hnext (i : S) : ToFreeCol m C t (steps + 1) (Sum.inl i.val) := by
    obtain ⟨j, hj, hcheap⟩ := (mem_cheapNeighbors false t T C i.val).mp (hS i.property)
    exact toFreeCol_step (hT j hj) (cheapArc_to_columnVertex hcheap)
  have hmatch (i : S) : ∃ j : Fin n, m i.val = some j := by
    cases hm_i : m i.val with
    | none =>
      have hi₀ : i.val ∈ freeRows m := mem_freeRows.mpr hm_i
      obtain ⟨j, hj, p, hhead, hlast, hlen⟩ := hnext i
      exact (hno ⟨i.val, hi₀, j, hj, p, hhead, hlast, hlen⟩).elim
    | some j => exact ⟨j, rfl⟩
  let f (i : S) := Classical.choose (hmatch i)
  have hf (i : S) : m i.val = some (f i) := Classical.choose_spec (hmatch i)
  have hinj : Function.Injective f := by
    intro i k hik
    exact Subtype.ext (hm (hf i) ((hf k).trans (congrArg some hik.symm)))
  let g : S ↪ Fin n := ⟨f, hinj⟩
  refine ⟨S.attach.map g, by simpa using hcard, ?_⟩
  intro j hj
  obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hj
  change ToFreeCol m C t (steps + 1) (columnVertex m (f i))
  rw [columnVertex_of_matched hm (hf i)]
  exact hnext i

private def reachedSize (j h k : ℕ) : ℕ := min (2 ^ k * j) h

private theorem le_reachedSize (j h k : ℕ) (hjh : j ≤ h) : j ≤ reachedSize j h k := by
  have hb : 0 < 2 ^ k := Nat.pow_pos (by decide)
  apply le_min _ hjh
  exact Nat.le_mul_of_pos_left _ hb

private theorem reachedSize_succ_le (j h k : ℕ) :
    reachedSize j h (k + 1) ≤ 2 * reachedSize j h k := by
  unfold reachedSize
  have hmul : 2 ^ (k + 1) * j = 2 * (2 ^ k * j) := by rw [pow_succ]; ring
  rw [hmul]
  by_cases hp : 2 ^ k * j ≤ h
  · rw [min_eq_left hp]
    exact min_le_left _ _
  · rw [min_eq_right (by omega : h ≤ 2 ^ k * j)]
    exact (min_le_right _ _).trans (by omega)

/-- Given the common expansion event, `r` rounds suffice whenever
`2^r * j ≥ n / 40`. The resulting augmenting path inserts at most
`2*r+1` cheap edges. -/
theorem exists_cheap_augmentingPath_of_not_mem_commonFailure
    {n : ℕ} {cutoff : ℕ → ℝ} {C : CostArray} {m : Fin n → Option (Fin n)}
    (hC : C ∉ commonExpansionFailure n cutoff) (hm : IsMatching m)
    {j r : ℕ} (hj : 0 < j) (hjn : j ≤ n)
    (hdeficit : n - (AugmentingPath.matchedRows m).card = j)
    (hr : n / 40 ≤ 2 ^ r * j) :
    ∃ k : ℕ, k + 1 ≤ 2 * r + 1 ∧ ∃ p : AugmentingPath m k, p.IsCheap C (cutoff j) := by
  classical
  by_cases hjh : n / 40 ≤ j
  · obtain ⟨p, hp⟩ := exists_cheap_singleAugmentation_of_not_mem_commonFailure
      hC hm hj hjn hjh hdeficit
    exact ⟨0, by omega, p, hp⟩
  let h := n / 40
  let t := cutoff j
  have hjh' : j ≤ h := by dsimp [h]; omega
  apply exists_cheap_augmentingPath_of_walk hm
  by_contra hno
  have reach (k : ℕ) (hk : k ≤ r) :
      (∃ S : Finset (Fin n), S.card = reachedSize j h k ∧
        ∀ i ∈ S, FromFreeRow m C t k (Sum.inl i)) ∧
      (∃ T : Finset (Fin n), T.card = reachedSize j h k ∧
        ∀ i ∈ T, ToFreeCol m C t k (columnVertex m i)) := by
    induction k with
    | zero =>
      have h0 : reachedSize j h 0 = j := by simp [reachedSize, min_eq_left hjh']
      constructor
      · refine ⟨freeRows m, by rw [freeRows_card, hdeficit, h0], ?_⟩
        intro i hi
        exact ⟨i, hi, RelSeries.singleton _ (Sum.inl i), rfl, rfl, le_rfl⟩
      · refine ⟨freeCols m, by rw [freeCols_card hm, hdeficit, h0], ?_⟩
        intro i hi
        exact ⟨i, hi, RelSeries.singleton _ (Sum.inr i), (columnVertex_of_free hi).symm,
          rfl, le_rfl⟩
    | succ k ih =>
      obtain ⟨⟨S, hScard, hS⟩, ⟨T, hTcard, hT⟩⟩ := ih (by omega)
      have hbase := le_reachedSize j h k hjh'
      have hceil : reachedSize j h k ≤ h := min_le_right _ _
      have hnext : reachedSize j h (k + 1) ≤ 10 * reachedSize j h k :=
        (reachedSize_succ_le j h k).trans (by omega)
      have hno' : ¬ HasAugmentingWalk m C t (k + 1) := fun hp =>
        hno (hasAugmentingWalk_mono hp (by omega))
      have hSL := expansion_of_not_mem_commonFailure hC true hj S
        (by rwa [hScard]) (by rwa [hScard])
      have hTL := expansion_of_not_mem_commonFailure hC false hj T
        (by rwa [hTcard]) (by rwa [hTcard])
      exact ⟨growForward hm S hS (hnext.trans (hScard ▸ hSL)) hno',
        growBackward hm T hT (hnext.trans (hTcard ▸ hTL)) hno'⟩
  obtain ⟨⟨S, hScard, hS⟩, ⟨T, hTcard, hT⟩⟩ := reach r le_rfl
  have hreach : reachedSize j h r = h := min_eq_right hr
  obtain ⟨i, hi, k, hk, hcheap⟩ := cheapEdge_of_not_mem_commonFailure hC hj hjn S T
    (hScard.trans hreach) (hTcard.trans hreach)
  obtain ⟨i₀, hi₀, p, hp₀, hp₁, hp₂⟩ := fromFreeRow_step (hS i hi)
    (cheapArc_to_columnVertex hcheap)
  obtain ⟨k₀, hk₀, q, hq₀, hq₁, hq₂⟩ := hT k hk
  let pq := p.smash q (hp₁.trans hq₀.symm)
  exact hno ⟨i₀, hi₀, k₀, hk₀, pq, by simpa [pq] using hp₀, by simpa [pq] using hq₁,
    by simp only [pq, RelSeries.smash_length]; omega⟩

end Certificate.Completion

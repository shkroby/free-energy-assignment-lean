import Certificate.CompletionExpansionPath
import Mathlib.Order.RelSeries

/-!
# Shortening a directed augmenting walk

A matched row represents its row together with the column it already occupies.
An arc moves by one cheap edge, then follows the matching backward if the
column reached is occupied. A free column is a terminal vertex.
-/

open scoped SetRel

namespace Certificate.Completion

private theorem exists_injective_relSeries_le {V : Type*} {r : SetRel V V} (p : RelSeries r) :
    ∃ q : RelSeries r, q.head = p.head ∧ q.last = p.last ∧ q.length ≤ p.length ∧
      Function.Injective q := by
  classical
  let Goal (p : RelSeries r) : Prop :=
    ∃ q : RelSeries r, q.head = p.head ∧ q.last = p.last ∧ q.length ≤ p.length ∧
      Function.Injective q
  have hreduce (n : ℕ) : ∀ p : RelSeries r, p.length = n → Goal p := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p hn
      by_cases hp : Function.Injective p
      · exact ⟨p, rfl, rfl, le_rfl, hp⟩
      · obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.mp hp
        obtain ⟨i, j, hij, heq⟩ : ∃ i j, i < j ∧ p i = p j := by
          rcases lt_or_gt_of_ne hne with hlt | hlt
          · exact ⟨a, b, hlt, hab⟩
          · exact ⟨b, a, hlt, hab.symm⟩
        let t := (p.take i).smash (p.drop j) (by simpa using heq)
        have ht : t.length < n := by
          simp only [t, RelSeries.smash_length, RelSeries.take_length, RelSeries.drop_length]
          have hj := j.isLt
          have huv : i.val < j.val := hij
          omega
        obtain ⟨q, hq₀, hq₁, hq₂, hq₃⟩ := ih t.length ht t rfl
        exact ⟨q, hq₀.trans (by simp [t]), hq₁.trans (by simp [t]),
          hq₂.trans (by omega), hq₃⟩
  exact hreduce p.length p rfl

/-- The column reached when a directed arc enters a contracted vertex. -/
def incomingColumn {n : ℕ} (m : Fin n → Option (Fin n)) : Fin n ⊕ Fin n → Option (Fin n)
  | .inl i => m i
  | .inr j => some j

/-- Terminal vertices stand for free columns. -/
def ValidDestination {n : ℕ} (m : Fin n → Option (Fin n)) : Fin n ⊕ Fin n → Prop
  | .inl _ => True
  | .inr j => j ∈ freeCols m

/-- The contracted vertex reached after traversing an edge to column `j`. -/
noncomputable def columnVertex {n : ℕ} (m : Fin n → Option (Fin n)) (j : Fin n) :
    Fin n ⊕ Fin n :=
  open Classical in
  if h : ∃ i, m i = some j then .inl (Classical.choose h) else .inr j

theorem columnVertex_of_matched {n : ℕ} {m : Fin n → Option (Fin n)} (hm : IsMatching m)
    {i j : Fin n} (hij : m i = some j) :
    columnVertex m j = Sum.inl i := by
  classical
  have h : ∃ i, m i = some j := ⟨i, hij⟩
  rw [columnVertex, dif_pos h, hm (Classical.choose_spec h) hij]

theorem columnVertex_of_free {n : ℕ} {m : Fin n → Option (Fin n)} {j : Fin n}
    (hj : j ∈ freeCols m) :
    columnVertex m j = Sum.inr j := by
  classical
  rw [columnVertex, dif_neg]
  exact fun ⟨i, hi⟩ => mem_freeCols.mp hj i hi

theorem incomingColumn_columnVertex {n : ℕ} (m : Fin n → Option (Fin n)) (j : Fin n) :
    incomingColumn m (columnVertex m j) = some j := by
  classical
  unfold columnVertex
  split
  · exact Classical.choose_spec ‹∃ i, m i = some j›
  · rfl

theorem columnVertex_valid {n : ℕ} (m : Fin n → Option (Fin n)) (j : Fin n) :
    ValidDestination m (columnVertex m j) := by
  classical
  unfold columnVertex
  split
  · trivial
  · exact mem_freeCols.mpr (fun i hi => ‹¬ ∃ i, m i = some j› ⟨i, hi⟩)

private theorem eq_of_incomingColumn_eq_some {n : ℕ} {m : Fin n → Option (Fin n)}
    (hm : IsMatching m) {a b : Fin n ⊕ Fin n} {j : Fin n}
    (ha : ValidDestination m a) (hb : ValidDestination m b)
    (ha' : incomingColumn m a = some j) (hb' : incomingColumn m b = some j) : a = b := by
  cases a with
  | inl i =>
    cases b with
    | inl i' => exact congrArg Sum.inl (hm ha' hb')
    | inr j' =>
      have h : j' = j := Option.some.inj hb'
      subst j'
      exact False.elim (mem_freeCols.mp hb i ha')
  | inr j' =>
    have h : j' = j := Option.some.inj ha'
    subst j'
    cases b with
    | inl i => exact False.elim (mem_freeCols.mp ha i hb')
    | inr k => exact congrArg Sum.inr (Option.some.inj hb').symm

/-- Directed arcs after compressing matching edges. -/
def cheapArc {n : ℕ} (m : Fin n → Option (Fin n)) (C : CostArray) (t : ℝ) :
    SetRel (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) :=
  {p | ∃ i j : Fin n, p.1 = Sum.inl i ∧ incomingColumn m p.2 = some j ∧
    ValidDestination m p.2 ∧ C (i.val, j.val) ≤ t}

theorem cheapArc_to_columnVertex {n : ℕ} {m : Fin n → Option (Fin n)}
    {C : CostArray} {t : ℝ} {i j : Fin n} (hcheap : C (i.val, j.val) ≤ t) :
    (Sum.inl i) ~[cheapArc m C t] (columnVertex m j) :=
  ⟨i, j, rfl, incomingColumn_columnVertex m j, columnVertex_valid m j, hcheap⟩

/-- A cheap directed walk, with endpoints free in the original matching. -/
def HasAugmentingWalk {n : ℕ} (m : Fin n → Option (Fin n)) (C : CostArray) (t : ℝ)
    (budget : ℕ) : Prop :=
  ∃ i ∈ freeRows m, ∃ j ∈ freeCols m, ∃ p : RelSeries (cheapArc m C t),
    p.head = Sum.inl i ∧ p.last = Sum.inr j ∧ p.length ≤ budget

/-- Removing directed cycles from a walk leaves an augmenting path of no greater
length. The original matching identifies the intermediate columns. -/
theorem exists_cheap_augmentingPath_of_walk {n : ℕ} {m : Fin n → Option (Fin n)}
    (hm : IsMatching m) {C : CostArray} {t : ℝ} {budget : ℕ}
    (h : HasAugmentingWalk m C t budget) :
    ∃ k : ℕ, k + 1 ≤ budget ∧ ∃ p : AugmentingPath m k, p.IsCheap C t := by
  classical
  obtain ⟨i₀, hi₀, j₀, hj₀, walk, hstart, hend, hlen⟩ := h
  obtain ⟨q, hqstart, hqend, hqlen, hqinj⟩ := exists_injective_relSeries_le walk
  have hq₀ : q.head = Sum.inl i₀ := hqstart.trans hstart
  have hq₁ : q.last = Sum.inr j₀ := hqend.trans hend
  have hqn : q.length ≠ 0 := by
    intro hlen0
    have hqhl : q.head = q.last := by
      unfold RelSeries.head RelSeries.last
      congr 1
      ext
      simp [hlen0]
    exact Sum.inl_ne_inr (hq₀.symm.trans (hqhl.trans hq₁))
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hqn
  let index (a : Fin (k + 1)) : Fin q.length := Fin.cast hk.symm a
  have harc (a : Fin (k + 1)) : ∃ i j : Fin n,
      q (index a).castSucc = Sum.inl i ∧ incomingColumn m (q (index a).succ) = some j ∧
      ValidDestination m (q (index a).succ) ∧ C (i.val, j.val) ≤ t := q.step (index a)
  choose row col hrow hcol hdest hcheap using harc
  have hrowInj : Function.Injective row := by
    intro a b h
    have he := hqinj ((hrow a).trans ((congrArg Sum.inl h).trans (hrow b).symm))
    exact (Fin.cast_injective hk.symm) (Fin.castSucc_injective _ he)
  have hcolInj : Function.Injective col := by
    intro a b h
    have he := eq_of_incomingColumn_eq_some hm (hdest a) (hdest b) (hcol a)
      ((hcol b).trans (congrArg some h.symm))
    exact (Fin.cast_injective hk.symm) (Fin.succ_injective _ (hqinj he))
  have hrow₀ : row 0 = i₀ := by
    have hindex : (index (0 : Fin (k + 1))).castSucc = (0 : Fin (q.length + 1)) := by
      ext
      rfl
    apply Sum.inl.inj
    rw [← hrow 0, hindex, RelSeries.apply_zero, hq₀]
  have hcol₀ : col (Fin.last k) = j₀ := by
    have hl : (index (Fin.last k)).succ = Fin.last q.length := by
      ext
      simp [index, hk]
    apply Option.some.inj
    rw [← hcol (Fin.last k), hl, RelSeries.apply_last, hq₁]
    rfl
  have hmates (a : Fin k) : m (row a.succ) = some (col a.castSucc) := by
    have he : (index a.castSucc).succ = (index a.succ).castSucc := by ext; rfl
    have h := hcol a.castSucc
    rw [he, hrow a.succ] at h
    exact h
  refine ⟨k, by omega, ?_⟩
  let p : AugmentingPath m k :=
    { rows := ⟨row, hrowInj⟩
      cols := ⟨col, hcolInj⟩
      startFree := by change m (row 0) = none; rw [hrow₀]; exact mem_freeRows.mp hi₀
      matched := hmates
      endFree := by change ∀ i, m i ≠ some (col (Fin.last k)); rw [hcol₀]; exact mem_freeCols.mp hj₀ }
  exact ⟨p, hcheap⟩

end Certificate.Completion

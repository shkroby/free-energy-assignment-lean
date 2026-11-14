import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card

/-!
# Flipping an augmenting path

A partial matching sends each row to either its matched column or `none`.
An augmenting path has distinct rows and columns, a free first row and last column,
and a matched edge from each nonfirst row to the preceding column.
-/

namespace Certificate.Completion

/-- An optional row function is a matching when its occupied column labels are distinct. -/
def IsMatching {ι κ : Type*} (m : ι → Option κ) : Prop :=
  ∀ ⦃i j c⦄, m i = some c → m j = some c → i = j

/-- Alternating path with `k + 1` edges to insert and `k` edges to remove. -/
structure AugmentingPath {ι κ : Type*} (m : ι → Option κ) (k : ℕ) where
  rows : Fin (k + 1) ↪ ι
  cols : Fin (k + 1) ↪ κ
  startFree : m (rows 0) = none
  matched : ∀ j : Fin k, m (rows j.succ) = some (cols j.castSucc)
  endFree : ∀ i : ι, m i ≠ some (cols (Fin.last k))

namespace AugmentingPath

variable {ι κ : Type*} {m : ι → Option κ} {k : ℕ}

/-- Replace every path-row assignment by its new column on the path. -/
noncomputable def flip (p : AugmentingPath m k) (i : ι) : Option κ :=
  open Classical in
  if hi : ∃ j, p.rows j = i then some (p.cols (Classical.choose hi)) else m i

@[simp] theorem flip_on_path (p : AugmentingPath m k) (j : Fin (k + 1)) :
    p.flip (p.rows j) = some (p.cols j) := by
  classical
  have hj : ∃ l, p.rows l = p.rows j := ⟨j, rfl⟩
  rw [flip, dif_pos hj, p.rows.injective (Classical.choose_spec hj)]

theorem flip_off_path (p : AugmentingPath m k) {i : ι} (hi : ¬ ∃ j, p.rows j = i) :
    p.flip i = m i := by
  classical
  rw [flip, dif_neg hi]

private theorem no_path_col_off_path (p : AugmentingPath m k) (hm : IsMatching m)
    {i : ι} (hi : ¬ ∃ j, p.rows j = i) (j : Fin (k + 1)) :
    m i ≠ some (p.cols j) := by
  rcases Fin.eq_castSucc_or_eq_last j with ⟨a, rfl⟩ | rfl
  · intro heq
    exact hi ⟨a.succ, hm (p.matched a) heq⟩
  · exact p.endFree i

/-- Flipping produces another matching. -/
theorem isMatching_flip (p : AugmentingPath m k) (hm : IsMatching m) :
    IsMatching p.flip := by
  intro i j c hi hj
  by_cases ip : ∃ a, p.rows a = i
  · obtain ⟨a, rfl⟩ := ip
    rw [p.flip_on_path] at hi
    by_cases jp : ∃ b, p.rows b = j
    · obtain ⟨b, rfl⟩ := jp
      rw [p.flip_on_path] at hj
      exact congrArg p.rows (p.cols.injective (Option.some.inj (hi.trans hj.symm)))
    · rw [p.flip_off_path jp, ← Option.some.inj hi] at hj
      exact False.elim (p.no_path_col_off_path hm jp a hj)
  · rw [p.flip_off_path ip] at hi
    by_cases jp : ∃ b, p.rows b = j
    · obtain ⟨b, rfl⟩ := jp
      rw [p.flip_on_path] at hj
      exact False.elim (p.no_path_col_off_path hm ip b (hi.trans hj.symm))
    · rw [p.flip_off_path jp] at hj
      exact hm hi hj

/-- The rows that receive an edge in an optional row function. -/
noncomputable def matchedRows [Fintype ι] (m : ι → Option κ) : Finset ι :=
  open Classical in Finset.univ.filter (fun i => m i ≠ none)

@[simp] theorem mem_matchedRows [Fintype ι] {i : ι} :
    i ∈ matchedRows m ↔ m i ≠ none := by
  classical
  simp [matchedRows]

/-- The augmentation adds just the starting row to the set of matched rows. -/
theorem matchedRows_flip [Fintype ι] [DecidableEq ι] (p : AugmentingPath m k) :
    matchedRows p.flip = insert (p.rows 0) (matchedRows m) := by
  ext i
  simp only [Finset.mem_insert, mem_matchedRows]
  by_cases ip : ∃ a, p.rows a = i
  · obtain ⟨a, rfl⟩ := ip
    rw [p.flip_on_path]
    refine iff_of_true (by simp) ?_
    rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨b, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (by rw [p.matched b]; simp)
  · rw [p.flip_off_path ip]
    exact (or_iff_right (fun h => ip ⟨0, h.symm⟩)).symm

/-- An augmenting flip increases the size by one. -/
theorem matchedRows_card_flip [Fintype ι] (p : AugmentingPath m k) :
    (matchedRows p.flip).card = (matchedRows m).card + 1 := by
  classical
  rw [p.matchedRows_flip, Finset.card_insert_of_notMem]
  simp [p.startFree]

end AugmentingPath

end Certificate.Completion

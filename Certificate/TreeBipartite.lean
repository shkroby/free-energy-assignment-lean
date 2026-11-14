import Certificate.Tree
import Certificate.CompletionModel
import Certificate.Removal

/-!
# The bipartite model in the tree and completion arguments

An edge set in the deletion model and a partial row assignment in the weighted
completion model encode the same matching. This module identifies the two
partition functions.
-/

open scoped BigOperators
open Finset

namespace Certificate.Tree

namespace Bipartite

variable {n : ℕ}

/-- The two endpoints of a row-column edge in the complete bipartite graph. -/
def ends (ij : Fin n × Fin n) : Finset (Fin n ⊕ Fin n) :=
  {Sum.inl ij.1, Sum.inr ij.2}

@[simp] theorem ends_card (ij : Fin n × Fin n) : (ends ij).card = 2 := by
  simp [ends]

/-- Interpret a partial row assignment as its graph of occupied edges. -/
def edgesOf (m : Fin n → Option (Fin n)) : Finset (Fin n × Fin n) :=
  univ.filter fun ij => m ij.1 = some ij.2

@[simp] theorem mem_edgesOf {m : Fin n → Option (Fin n)} {i j : Fin n} :
    (i, j) ∈ edgesOf m ↔ m i = some j := by
  simp [edgesOf]

theorem edgesOf_injective : Function.Injective (edgesOf (n := n)) := by
  intro m p h
  funext i
  cases hm : m i with
  | none =>
    cases hp : p i with
    | none => rfl
    | some j =>
      have hj : (i, j) ∈ edgesOf p := mem_edgesOf.mpr hp
      rw [← h, mem_edgesOf, hm] at hj
      cases hj
  | some j =>
    have hj : (i, j) ∈ edgesOf m := mem_edgesOf.mpr hm
    rw [h, mem_edgesOf] at hj
    exact hj.symm

theorem edgesOf_valid_iff (m : Fin n → Option (Fin n)) :
    edgesOf m ∈ matchings ends univ univ ↔ Completion.IsMatching m := by
  constructor
  · intro h i j c hi hj
    by_contra hij
    have hne : (i, c) ≠ (j, c) := fun e => hij (congrArg Prod.fst e)
    have hd := (mem_matchings.mp h).2.2 (i, c) (mem_edgesOf.mpr hi) (j, c)
      (mem_edgesOf.mpr hj) hne
    exact disjoint_left.mp hd (by simp [ends] : Sum.inr c ∈ ends (i,c)) (by simp [ends])
  · intro h
    apply mem_matchings.mpr
    refine ⟨subset_univ _, fun e _ => subset_univ _, ?_⟩
    rintro ⟨i, c⟩ he ⟨j, c'⟩ hf hne
    apply disjoint_left.mpr
    rintro (r | r) hr hs
    · have hir : r = i := by simpa [ends] using hr
      have hjr : r = j := by simpa [ends] using hs
      have hij : i = j := hir.symm.trans hjr
      rw [← hij] at hf hne
      have hc := Option.some.inj ((mem_edgesOf.mp he).symm.trans (mem_edgesOf.mp hf))
      exact hne (congrArg (i, ·) hc)
    · have hcr : r = c := by simpa [ends] using hr
      have hcs : r = c' := by simpa [ends] using hs
      have hc : c = c' := hcr.symm.trans hcs
      rw [← hc] at hf hne
      exact hne (congrArg (·, c) (h (mem_edgesOf.mp he) (mem_edgesOf.mp hf)))

private theorem row_unique {M : Finset (Fin n × Fin n)}
    (hM : M ∈ matchings ends univ univ) {i j k : Fin n} (hj : (i,j) ∈ M) (hk : (i,k) ∈ M) :
    j = k := by
  by_contra hne
  have hneq : (i,j) ≠ (i,k) := fun e => hne (congrArg Prod.snd e)
  have hd := (mem_matchings.mp hM).2.2 _ hj _ hk hneq
  exact disjoint_left.mp hd (by simp [ends] : Sum.inl i ∈ ends (i,j)) (by simp [ends])

theorem exists_edgesOf_eq {M : Finset (Fin n × Fin n)}
    (hM : M ∈ matchings ends univ univ) : ∃ m, edgesOf m = M := by
  classical
  let m (i : Fin n) : Option (Fin n) :=
    if h : ∃ j, (i,j) ∈ M then some (Classical.choose h) else none
  refine ⟨m, ?_⟩
  ext ⟨i,j⟩
  rw [mem_edgesOf]
  by_cases hi : ∃ k, (i,k) ∈ M
  · have hc := Classical.choose_spec hi
    simp only [m, dif_pos hi, Option.some.injEq]
    exact ⟨fun h => h ▸ hc, fun h => row_unique hM hc h⟩
  · have hj : (i,j) ∉ M := fun h => hi ⟨j,h⟩
    simp [m, hi, hj]

theorem card_edgesOf (m : Fin n → Option (Fin n)) :
    (edgesOf m).card = (Completion.AugmentingPath.matchedRows m).card := by
  have hem : (edgesOf m).image Prod.fst = Completion.AugmentingPath.matchedRows m := by
    ext i
    rw [Completion.AugmentingPath.mem_matchedRows]
    constructor
    · intro hi
      obtain ⟨⟨j,c⟩, hjc, rfl⟩ := mem_image.mp hi
      simp [mem_edgesOf.mp hjc]
    · intro hi
      cases hm : m i with
      | none => exact (hi hm).elim
      | some c => exact mem_image.mpr ⟨(i,c), mem_edgesOf.mpr hm, rfl⟩
  rw [← hem, Finset.card_image_of_injOn]
  rintro ⟨i,c⟩ h1 ⟨j,c'⟩ h2 (heq : i = j)
  subst j
  have hc := Option.some.inj ((mem_edgesOf.mp h1).symm.trans (mem_edgesOf.mp h2))
  exact congrArg (i, ·) hc

theorem prod_edgesOf_eq_partialWeight (β : ℝ) (x : Fin n → Fin n → ℝ)
    (m : Fin n → Option (Fin n)) :
    (∏ ij ∈ edgesOf m, Real.exp (-β * x ij.1 ij.2)) = Completion.partialWeight β x m := by
  classical
  rw [edgesOf, Finset.prod_filter, Fintype.prod_prod_type]
  unfold Completion.partialWeight
  apply Finset.prod_congr rfl
  intro i _
  change (∏ j : Fin n, if m i = some j then Real.exp (-β * x i j) else 1) =
    Completion.rowWeight β x i (m i)
  cases m i with
  | none => simp
  | some j =>
    rw [Completion.rowWeight_some]
    rw [Finset.prod_eq_single j]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp

/-- All row functions satisfying the matching constraint, across every deficit. -/
noncomputable def allPartial (n : ℕ) : Finset (Fin n → Option (Fin n)) := by
  classical
  exact univ.filter Completion.IsMatching

@[simp] theorem mem_allPartial {m : Fin n → Option (Fin n)} :
    m ∈ allPartial n ↔ Completion.IsMatching m := by
  classical
  simp [allPartial]

theorem matchings_eq_image_allPartial (n : ℕ) :
    matchings (ends (n := n)) univ univ = (allPartial n).image edgesOf := by
  ext M
  constructor
  · intro hM
    obtain ⟨m, hm⟩ := exists_edgesOf_eq hM
    exact mem_image.mpr ⟨m, mem_allPartial.mpr ((edgesOf_valid_iff m).mp (hm ▸ hM)), hm⟩
  · intro hM
    obtain ⟨m, hm, rfl⟩ := mem_image.mp hM
    exact (edgesOf_valid_iff m).mpr (mem_allPartial.mp hm)

private theorem matchedRows_card_le (m : Fin n → Option (Fin n)) :
    (Completion.AugmentingPath.matchedRows m).card ≤ n := by
  simpa using (Finset.card_le_univ (Completion.AugmentingPath.matchedRows m))

/-- The vertex-deletion model and the grouped-by-deficit model define the same
monomer partition on every finite bipartite cost array. This equality holds
also at zero fugacity. -/
theorem monomerPartition_eq_grouped (β d κ z : ℝ) (n : ℕ) (C : CostArray) :
    Tree.monomerPartition (ends (n := n)) univ univ
      (fun ij => Real.exp (-β * Completion.scaledCost d κ n C ij.1 ij.2)) z =
    Certificate.monomerPartition n (fun k => Completion.deficitPartition β d κ n k C) z := by
  classical
  let deficit (m : Fin n → Option (Fin n)) : ℕ :=
    n - (Completion.AugmentingPath.matchedRows m).card
  let a (m : Fin n → Option (Fin n)) : ℝ :=
    z ^ (2 * deficit m) * Completion.partialWeight β (Completion.scaledCost d κ n C) m
  rw [Tree.monomerPartition, matchings_eq_image_allPartial, Finset.sum_image edgesOf_injective.injOn]
  calc
    _ = ∑ m ∈ allPartial n, a m := by
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [prod_edgesOf_eq_partialWeight, card_edgesOf]
      have hv : (univ : Finset (Fin n ⊕ Fin n)).card = 2 * n := by simp; omega
      rw [hv]
      congr 2
      simp [deficit, Nat.mul_sub]
    _ = ∑ k ∈ range (n + 1), ∑ m ∈ (allPartial n).filter (fun m => deficit m = k), a m := by
      symm
      apply Finset.sum_fiberwise_of_maps_to
      intro m _
      exact mem_range.mpr (Nat.lt_succ_of_le (Nat.sub_le _ _))
    _ = _ := by
      unfold Certificate.monomerPartition
      refine Finset.sum_congr rfl fun k _ => ?_
      have hfilter : (allPartial n).filter (fun m => deficit m = k) =
          Completion.matchingsAtDeficit n k := by
        ext m
        simp only [mem_filter, mem_allPartial, Completion.mem_matchingsAtDeficit]
        have hcard := matchedRows_card_le m
        simp [deficit]
        omega
      change _ = z ^ (2 * k) * Completion.deficitPartition β d κ n k C
      unfold Completion.deficitPartition
      rw [Finset.mul_sum, ← hfilter]
      refine Finset.sum_congr rfl fun m hm => ?_
      simp [a, (mem_filter.mp hm).2]

/-- Setting the fugacity to zero recovers the permanent partition for perfect
assignments in the same finite graph. -/
theorem monomerPartition_zero_eq_permanent (β d κ : ℝ) (n : ℕ) (C : CostArray) :
    Tree.monomerPartition (ends (n := n)) univ univ
      (fun ij => Real.exp (-β * Completion.scaledCost d κ n C ij.1 ij.2)) 0 =
    assignmentPartition β d κ n C := by
  rw [monomerPartition_eq_grouped, ← Completion.deficitPartition_zero]
  unfold Certificate.monomerPartition
  rw [Finset.sum_eq_single 0]
  · simp
  · intro b _ hb
    simp [zero_pow (show 2 * b ≠ 0 by omega)]
  · simp

end Bipartite
end Certificate.Tree

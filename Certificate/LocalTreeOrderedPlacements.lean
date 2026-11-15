import Certificate.LocalTreePlacements
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.Perm

/-! Counting injective placements with increasing labels within each sibling group. -/

open Filter
open scoped Topology

namespace Certificate.LocalExploration

section Grouped

variable {G L : Type*} {k : G → ℕ} [LinearOrder L]

/-- An injective placement of children in which the labels increase
within each sibling group. -/
abbrev SiblingOrderedEmbedding (k : G → ℕ) (L : Type*) [LinearOrder L] :=
  {f : (Σ g, Fin (k g)) ↪ L // ∀ g, StrictMono (fun i => f ⟨g,i⟩)}

private def groupEmbedding (f : (Σ g, Fin (k g)) ↪ L) (g : G) : Fin (k g) ↪ L :=
  ⟨fun i => f ⟨g,i⟩, fun i j h => by
    apply Fin.ext
    exact congrArg (fun p : Σ g, Fin (k g) => p.2.val) (f.injective h)⟩

private def groupImage (f : (Σ g, Fin (k g)) ↪ L) (g : G) : Finset L :=
  Finset.univ.map (groupEmbedding f g)

omit [LinearOrder L] in
private theorem card_groupImage (f : (Σ g, Fin (k g)) ↪ L) (g : G) :
    (groupImage f g).card = k g := by
  simp [groupImage]

omit [LinearOrder L] in
private theorem mem_groupImage_iff {f : (Σ g, Fin (k g)) ↪ L} {g : G} {v : L} :
    v ∈ groupImage f g ↔ ∃ i : Fin (k g), f ⟨g,i⟩ = v := by
  simp [groupImage, Finset.mem_map]
  rfl

private noncomputable def groupImageEquiv (f : (Σ g, Fin (k g)) ↪ L) (g : G) :
    Fin (k g) ≃ ↥(groupImage f g) :=
  Equiv.ofBijective (fun i => ⟨f ⟨g,i⟩, mem_groupImage_iff.mpr ⟨i,rfl⟩⟩)
    ⟨fun i j h => (groupEmbedding f g).injective (congrArg Subtype.val h), by
      intro v
      obtain ⟨i, hi⟩ := mem_groupImage_iff.mp v.property
      exact ⟨i, Subtype.ext hi⟩⟩

private noncomputable def sortedGroup (f : (Σ g, Fin (k g)) ↪ L) (g : G) :
    Fin (k g) ≃o ↥(groupImage f g) :=
  (groupImage f g).orderIsoOfFin (card_groupImage f g)

private noncomputable def sortSiblingEmbedding (f : (Σ g, Fin (k g)) ↪ L) :
    SiblingOrderedEmbedding k L :=
  ⟨⟨fun p => (sortedGroup f p.1 p.2 : L), by
      rintro ⟨g,i⟩ ⟨h,j⟩ he
      change (sortedGroup f g i : L) = (sortedGroup f h j : L) at he
      obtain ⟨i', hi'⟩ := mem_groupImage_iff.mp (sortedGroup f g i).property
      obtain ⟨j', hj'⟩ := mem_groupImage_iff.mp (sortedGroup f h j).property
      have hgh : g = h :=
        congrArg Sigma.fst (f.injective (hi'.trans (he.trans hj'.symm)))
      subst h
      exact congrArg (Sigma.mk g) ((sortedGroup f g).injective (Subtype.ext he))⟩,
    fun g _ _ hij => (sortedGroup f g).strictMono hij⟩

private noncomputable def siblingPermutation (f : (Σ g, Fin (k g)) ↪ L) (g : G) :
    Equiv.Perm (Fin (k g)) :=
  (groupImageEquiv f g).trans (sortedGroup f g).toEquiv.symm

private def permuteSiblingEmbedding (f : SiblingOrderedEmbedding k L)
    (π : ∀ g, Equiv.Perm (Fin (k g))) : (Σ g, Fin (k g)) ↪ L :=
  (Equiv.sigmaCongrRight π).toEmbedding.trans f.val

private theorem permute_sortSiblingEmbedding (f : (Σ g, Fin (k g)) ↪ L) :
    permuteSiblingEmbedding (sortSiblingEmbedding f) (siblingPermutation f) = f := by
  ext p
  obtain ⟨g,i⟩ := p
  change (sortedGroup f g ((sortedGroup f g).symm (groupImageEquiv f g i)) : L) = f ⟨g,i⟩
  rw [OrderIso.apply_symm_apply]
  rfl

private theorem groupImage_permuteSiblingEmbedding (f : SiblingOrderedEmbedding k L)
    (π : ∀ g, Equiv.Perm (Fin (k g))) (g : G) :
    groupImage (permuteSiblingEmbedding f π) g = groupImage f.val g := by
  ext v
  simp only [mem_groupImage_iff]
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨π g i, hi⟩
  · rintro ⟨i,hi⟩
    refine ⟨(π g).symm i, ?_⟩
    change f.val ⟨g, π g ((π g).symm i)⟩ = v
    rw [Equiv.apply_symm_apply, hi]

private theorem sort_permuteSiblingEmbedding (f : SiblingOrderedEmbedding k L)
    (π : ∀ g, Equiv.Perm (Fin (k g))) :
    sortSiblingEmbedding (permuteSiblingEmbedding f π) = f := by
  apply Subtype.ext
  ext p
  obtain ⟨g,i⟩ := p
  have he := Finset.orderEmbOfFin_unique
    (s := groupImage (permuteSiblingEmbedding f π) g)
    (card_groupImage (permuteSiblingEmbedding f π) g)
    (f := fun j => f.val ⟨g,j⟩) (fun j => by
      rw [groupImage_permuteSiblingEmbedding]
      exact mem_groupImage_iff.mpr ⟨j,rfl⟩) (f.property g)
  exact (congrFun he i).symm

private theorem permuteSiblingEmbedding_injective (f : SiblingOrderedEmbedding k L) :
    Function.Injective (permuteSiblingEmbedding f) := by
  intro π τ h
  funext g
  ext i
  have heq : f.val ⟨g,π g i⟩ = f.val ⟨g,τ g i⟩ := congrArg (fun p => p ⟨g,i⟩) h
  exact congrArg (fun p : Σ g, Fin (k g) => p.2.val) (f.val.injective heq)

/-- Sorting each group gives a bijection between arbitrary injections and
the increasing injections with a permutation for every sibling group. -/
noncomputable def siblingOrderedEmbeddingEquiv :
    ((Σ g, Fin (k g)) ↪ L) ≃
      SiblingOrderedEmbedding k L × (∀ g, Equiv.Perm (Fin (k g))) where
  toFun f := (sortSiblingEmbedding f, siblingPermutation f)
  invFun p := permuteSiblingEmbedding p.1 p.2
  left_inv := permute_sortSiblingEmbedding
  right_inv := by
    rintro ⟨f,π⟩
    apply Prod.ext
    · exact sort_permuteSiblingEmbedding f π
    · apply permuteSiblingEmbedding_injective f
      have h := permute_sortSiblingEmbedding (permuteSiblingEmbedding f π)
      rw [sort_permuteSiblingEmbedding] at h
      exact h

end Grouped

section Count

variable {G L : Type*} [Fintype G] [Fintype L] [LinearOrder L] (k : G → ℕ)

noncomputable instance : Fintype (SiblingOrderedEmbedding k L) := by
  classical
  exact Fintype.ofFinite _

/-- The factorial factor accounts for the orderings of the siblings in
each group and is independent of the size of the label space. -/
def siblingGroupFactorials (k : G → ℕ) : ℕ := ∏ g, (k g).factorial

theorem siblingGroupFactorials_pos : 0 < siblingGroupFactorials k := by
  unfold siblingGroupFactorials
  exact Finset.prod_pos fun g _ => Nat.factorial_pos (k g)

theorem card_siblingOrderedEmbedding_mul_factorials :
    Fintype.card (SiblingOrderedEmbedding k L) * siblingGroupFactorials k =
      (Fintype.card L).descFactorial (∑ g, k g) := by
  classical
  have h := Fintype.card_congr (siblingOrderedEmbeddingEquiv (k := k) (L := L))
  rw [Fintype.card_prod, Fintype.card_pi, Fintype.card_embedding_eq, Fintype.card_sigma] at h
  simpa only [Fintype.card_fin, Fintype.card_perm, siblingGroupFactorials] using h.symm

end Count

section Pinned

variable {G H : Type*} (a : G → ℕ) (b : H → ℕ)

/-- The non-root row labels avoid the actual pinned root; sibling groups
are assigned in increasing label order in both vertex classes. -/
abbrev PinnedSiblingOrderedBipartitePlacement {n : ℕ} (r : Fin n) :=
  SiblingOrderedEmbedding a {v : Fin n // v ≠ r} × SiblingOrderedEmbedding b (Fin n)

/-- Restore the pinned root as the image of `none`, preserving all
chosen labels on the non-root vertices. -/
def extendPinnedRoot {n : ℕ} (r : Fin n)
    (f : SiblingOrderedEmbedding a {v : Fin n // v ≠ r}) :
    Option (Σ g, Fin (a g)) ↪ Fin n :=
  let e := f.val.trans (Function.Embedding.subtype _)
  e.optionElim r (by rintro ⟨p, hp⟩; exact (f.val p).property hp)

@[simp] theorem extendPinnedRoot_none {n : ℕ} (r : Fin n)
    (f : SiblingOrderedEmbedding a {v : Fin n // v ≠ r}) :
    extendPinnedRoot a r f none = r := rfl

@[simp] theorem extendPinnedRoot_some {n : ℕ} (r : Fin n)
    (f : SiblingOrderedEmbedding a {v : Fin n // v ≠ r}) (p : Σ g, Fin (a g)) :
    extendPinnedRoot a r f (some p) = (f.val p : Fin n) := rfl

variable [Fintype G] [Fintype H]

private theorem card_labels_away_from_root {n : ℕ} (r : Fin n) :
    Fintype.card {v : Fin n // v ≠ r} = n - 1 := by
  rw [Fintype.card_subtype_compl (· = r), Fintype.card_subtype_eq, Fintype.card_fin]

/-- Multiplying the actual sibling-ordered placement count by the group
factorials gives the un-ordered count for the same pinned root. -/
theorem card_pinnedSiblingOrderedBipartitePlacement_mul_factorials {n : ℕ} (r : Fin n) :
    Fintype.card (PinnedSiblingOrderedBipartitePlacement a b r) *
      (siblingGroupFactorials a * siblingGroupFactorials b) =
      Fintype.card (RootedBipartitePlacement (∑ g, a g) (∑ h, b h) n) := by
  rw [card_rootedBipartitePlacement, Fintype.card_prod, mul_mul_mul_comm,
    card_siblingOrderedEmbedding_mul_factorials, card_siblingOrderedEmbedding_mul_factorials,
    card_labels_away_from_root, Fintype.card_fin]

/-- Exact number of sibling-ordered placements in the actual row and column
label sets. -/
theorem card_pinnedSiblingOrderedBipartitePlacement {n : ℕ} (r : Fin n) :
    Fintype.card (PinnedSiblingOrderedBipartitePlacement a b r) =
      ((n-1).descFactorial (∑ g, a g) * n.descFactorial (∑ h, b h)) /
        (siblingGroupFactorials a * siblingGroupFactorials b) := by
  have hp := Nat.mul_pos (siblingGroupFactorials_pos a) (siblingGroupFactorials_pos b)
  have h := card_pinnedSiblingOrderedBipartitePlacement_mul_factorials a b r
  rw [card_rootedBipartitePlacement, mul_comm _ (siblingGroupFactorials a * siblingGroupFactorials b)] at h
  exact Nat.eq_div_of_mul_eq_right hp.ne' h

/-- The leading factor in the ordered placement count is the reciprocal
product of the sibling factorials, uniformly in the pinned root labels. -/
theorem tendsto_normalized_card_pinnedSiblingOrderedBipartitePlacement
    (roots : ∀ n : ℕ, Fin (n + 1)) :
    Tendsto (fun n : ℕ =>
      (Fintype.card (PinnedSiblingOrderedBipartitePlacement a b (roots n)) : ℝ) /
        ((n+1 : ℕ) : ℝ)^((∑ g, a g) + ∑ h, b h)) atTop
      (𝓝 (1 / ((siblingGroupFactorials a * siblingGroupFactorials b : ℕ) : ℝ))) := by
  let D := (siblingGroupFactorials a * siblingGroupFactorials b : ℕ)
  have hD : (D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr
    (Nat.mul_pos (siblingGroupFactorials_pos a) (siblingGroupFactorials_pos b)).ne'
  have h := ((tendsto_normalized_card_rootedBipartitePlacement (∑ g, a g) (∑ h, b h)).comp
    (tendsto_add_atTop_nat 1)).div_const (D : ℝ)
  refine h.congr' (Eventually.of_forall fun n => ?_)
  let q := ((n+1 : ℕ) : ℝ)^((∑ g, a g) + ∑ h, b h)
  let M := Fintype.card (PinnedSiblingOrderedBipartitePlacement a b (roots n))
  change (Fintype.card (RootedBipartitePlacement (∑ g, a g) (∑ h, b h) (n+1)) : ℝ) / q /
    (D : ℝ) = (M : ℝ) / q
  have he : M * D = Fintype.card
      (RootedBipartitePlacement (∑ g, a g) (∑ h, b h) (n+1)) :=
    card_pinnedSiblingOrderedBipartitePlacement_mul_factorials a b (roots n)
  rw [← he, Nat.cast_mul]
  calc
    _ = ((M : ℝ) * (D : ℝ) / (D : ℝ)) / q := by ring
    _ = _ := by rw [mul_div_cancel_right₀ _ hD]

end Pinned

end Certificate.LocalExploration

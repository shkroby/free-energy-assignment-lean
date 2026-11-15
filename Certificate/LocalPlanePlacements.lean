import Certificate.LocalPlaneEmbedding
import Certificate.LocalTreeOrderedPlacements
import Mathlib.Data.Sum.Order

/-! The sibling-group encoding of concrete depth-truncated plane shapes. -/

open Filter Set
open scoped Topology

namespace Certificate.LocalExploration.PlaneShape

/-- The usable words of a concrete plane shape. -/
abbrev Slot (shape : PlaneShape) := ↥shape.slots

/-- The slots whose offspring are tested at the prescribed depth. -/
abbrev Interior (shape : PlaneShape) := {u : List ℕ // u ∈ shape.slots ∧ u.length < shape.depth}

noncomputable instance (shape : PlaneShape) : Fintype shape.Interior :=
  (shape.finite_slots.subset (fun _ h => h.1)).fintype

/-- The odd-level parents have row children when the root is a row. -/
abbrev OddInterior (shape : PlaneShape) :=
  {u : List ℕ // u ∈ shape.slots ∧ u.length < shape.depth ∧ u.length % 2 = 1}

/-- The even-level parents have column children when the root is a row. -/
abbrev EvenInterior (shape : PlaneShape) :=
  {u : List ℕ // u ∈ shape.slots ∧ u.length < shape.depth ∧ u.length % 2 = 0}

noncomputable instance (shape : PlaneShape) : Fintype shape.Slot :=
  shape.finite_slots.fintype

noncomputable instance (shape : PlaneShape) : Fintype shape.OddInterior :=
  (shape.finite_slots.subset (fun _ h => h.1)).fintype

noncomputable instance (shape : PlaneShape) : Fintype shape.EvenInterior :=
  (shape.finite_slots.subset (fun _ h => h.1)).fintype

/-- Splitting interior parents by parity is a bijection. -/
def interiorParityEquiv (shape : PlaneShape) :
    shape.OddInterior ⊕ shape.EvenInterior ≃ shape.Interior where
  toFun := Sum.elim
    (fun u => ⟨u.val,u.property.1,u.property.2.1⟩)
    (fun u => ⟨u.val,u.property.1,u.property.2.1⟩)
  invFun u := if h : u.val.length % 2 = 1 then
    Sum.inl ⟨u.val,u.property.1,u.property.2,h⟩
    else Sum.inr ⟨u.val,u.property.1,u.property.2,by omega⟩
  left_inv := by
    rintro (u|u)
    · have h := u.property.2.2
      dsimp only [Sum.elim_inl]
      rw [dif_pos h]
    · have h : ¬u.val.length % 2 = 1 := by have h' := u.property.2.2; omega
      dsimp only [Sum.elim_inr]
      rw [dif_neg h]
  right_inv := by
    intro u
    dsimp only
    split <;> rfl

theorem card_interior_eq_sum_parities (shape : PlaneShape) :
    Fintype.card shape.Interior = Fintype.card shape.OddInterior + Fintype.card shape.EvenInterior := by
  rw [← Fintype.card_congr (shape.interiorParityEquiv), Fintype.card_sum]

def rowGroupSize (shape : PlaneShape) (u : shape.OddInterior) : ℕ := shape.childCount u.val

def colGroupSize (shape : PlaneShape) (u : shape.EvenInterior) : ℕ := shape.childCount u.val

/-- The row side consists of the root and the children of odd interior
parents. The column side consists of the children of even interior parents. -/
abbrev PlacementKey (shape : PlaneShape) :=
  Option (Σ u, Fin (shape.rowGroupSize u)) ⊕ (Σ u, Fin (shape.colGroupSize u))

private def wordOfKey (shape : PlaneShape) : shape.PlacementKey → shape.Slot
  | .inl none => ⟨[], shape.root_mem⟩
  | .inl (some ⟨u,i⟩) =>
    ⟨u.val ++ [i.val], (shape.child_mem _ _).mpr ⟨u.property.1,u.property.2.1,i.isLt⟩⟩
  | .inr ⟨u,i⟩ =>
    ⟨u.val ++ [i.val], (shape.child_mem _ _).mpr ⟨u.property.1,u.property.2.1,i.isLt⟩⟩

private theorem childWord_injective (shape : PlaneShape) (S : Set (List ℕ)) :
    Function.Injective (fun q : Σ u : S, Fin (shape.childCount u.val) => q.1.val ++ [q.2.val]) := by
  rintro ⟨u,i⟩ ⟨v,j⟩ h
  obtain ⟨hu,hi⟩ := List.append_singleton_inj.mp h
  have hv : u = v := Subtype.ext hu
  subst v
  exact congrArg (Sigma.mk u) (Fin.ext hi)

private theorem wordOfKey_injective (shape : PlaneShape) : Function.Injective (wordOfKey shape) := by
  rintro (x|x) (y|y) h
  · cases x with
    | none =>
      cases y with
      | none => rfl
      | some y =>
        obtain ⟨v,j⟩ := y
        have he : [] = v.val ++ [j.val] := congrArg Subtype.val h
        simp at he
    | some x =>
      cases y with
      | none =>
        obtain ⟨u,i⟩ := x
        have he : u.val ++ [i.val] = [] := congrArg Subtype.val h
        simp at he
      | some y =>
        apply congrArg (fun z => Sum.inl (some z))
        exact childWord_injective shape _ (congrArg Subtype.val h)
  · obtain ⟨v,j⟩ := y
    cases x with
    | none =>
      have he : [] = v.val ++ [j.val] := congrArg Subtype.val h
      simp at he
    | some x =>
      obtain ⟨u,i⟩ := x
      have he : u.val ++ [i.val] = v.val ++ [j.val] := congrArg Subtype.val h
      have hlen := congrArg List.length (List.append_singleton_inj.mp he).1
      have hu := u.property.2.2
      have hv := v.property.2.2
      omega
  · obtain ⟨u,i⟩ := x
    cases y with
    | none =>
      have he : u.val ++ [i.val] = [] := congrArg Subtype.val h
      simp at he
    | some y =>
      obtain ⟨v,j⟩ := y
      have he : u.val ++ [i.val] = v.val ++ [j.val] := congrArg Subtype.val h
      have hlen := congrArg List.length (List.append_singleton_inj.mp he).1
      have hu := u.property.2.2
      have hv := v.property.2.2
      omega
  · exact congrArg Sum.inr (childWord_injective shape _ (congrArg Subtype.val h))

private theorem wordOfKey_surjective (shape : PlaneShape) : Function.Surjective (wordOfKey shape) := by
  rintro ⟨v,hv⟩
  induction v using List.reverseRecOn with
  | nil => exact ⟨Sum.inl none,rfl⟩
  | append_singleton u i _ =>
    obtain ⟨hu,hd,hi⟩ := (shape.child_mem u i).mp hv
    by_cases h : u.length % 2 = 1
    · exact ⟨Sum.inl (some ⟨⟨u,hu,hd,h⟩,⟨i,hi⟩⟩),rfl⟩
    · have he : u.length % 2 = 0 := by omega
      exact ⟨Sum.inr ⟨⟨u,hu,hd,he⟩,⟨i,hi⟩⟩,rfl⟩

/-- Every slot is uniquely the root or a child index of the corresponding
interior parent. -/
noncomputable def placementKeyEquiv (shape : PlaneShape) : shape.PlacementKey ≃ shape.Slot :=
  Equiv.ofBijective (wordOfKey shape) ⟨wordOfKey_injective shape,wordOfKey_surjective shape⟩

/-- Ordered placements in the actual finite array, with the root row pinned. -/
abbrev OrderedPlacement (shape : PlaneShape) {n : ℕ} (root : Fin n) :=
  PinnedSiblingOrderedBipartitePlacement shape.rowGroupSize shape.colGroupSize root

private def keyLabel (shape : PlaneShape) {n : ℕ} (root : Fin n)
    (p : shape.OrderedPlacement root) : shape.PlacementKey ↪ (Fin n ⊕ Fin n) :=
  (extendPinnedRoot shape.rowGroupSize root p.1).sumMap p.2.val

/-- Actual row or column label of each slot. The value off the shape is
irrelevant and is set to the root. -/
noncomputable def placementLabel (shape : PlaneShape) {n : ℕ} (root : Fin n)
    (p : shape.OrderedPlacement root) (v : List ℕ) : Lex (Fin n ⊕ Fin n) := by
  classical
  exact if h : v ∈ shape.slots then toLex (keyLabel shape root p (shape.placementKeyEquiv.symm ⟨v,h⟩))
    else toLex (Sum.inl root)

private theorem placementLabel_ofKey (shape : PlaneShape) {n : ℕ} (root : Fin n)
    (p : shape.OrderedPlacement root) (q : shape.PlacementKey) :
    shape.placementLabel root p (wordOfKey shape q).val = toLex (keyLabel shape root p q) := by
  have h : shape.placementKeyEquiv.symm (wordOfKey shape q) = q :=
    shape.placementKeyEquiv.symm_apply_apply q
  simp only [placementLabel, dif_pos (wordOfKey shape q).property]
  rw [h]

@[simp] theorem placementLabel_root (shape : PlaneShape) {n : ℕ} (root : Fin n)
    (p : shape.OrderedPlacement root) :
    shape.placementLabel root p [] = toLex (Sum.inl root) :=
  shape.placementLabel_ofKey root p (Sum.inl none)

theorem placementLabel_left_child (shape : PlaneShape) {n : ℕ} (root : Fin n)
    (p : shape.OrderedPlacement root) (u : shape.OddInterior) (i : Fin (shape.rowGroupSize u)) :
    shape.placementLabel root p (u.val ++ [i.val]) = toLex (Sum.inl (p.1.val ⟨u,i⟩ : Fin n)) :=
  shape.placementLabel_ofKey root p (Sum.inl (some ⟨u,i⟩))

theorem placementLabel_right_child (shape : PlaneShape) {n : ℕ} (root : Fin n)
    (p : shape.OrderedPlacement root) (u : shape.EvenInterior) (i : Fin (shape.colGroupSize u)) :
    shape.placementLabel root p (u.val ++ [i.val]) = toLex (Sum.inr (p.2.val ⟨u,i⟩)) :=
  shape.placementLabel_ofKey root p (Sum.inr ⟨u,i⟩)

theorem placementLabel_injOn (shape : PlaneShape) {n : ℕ} (root : Fin n)
    (p : shape.OrderedPlacement root) : InjOn (shape.placementLabel root p) shape.slots := by
  intro u hu v hv hEq
  simp only [placementLabel, dif_pos hu, dif_pos hv] at hEq
  exact congrArg Subtype.val (shape.placementKeyEquiv.symm.injective
    ((keyLabel shape root p).injective (toLex.injective hEq)))

theorem placementLabel_child_strictMono (shape : PlaneShape) {n : ℕ} (root : Fin n)
    (p : shape.OrderedPlacement root) {v : List ℕ} (hv : v ∈ shape.slots) (hd : v.length < shape.depth) :
    StrictMono (fun i : Fin (shape.childCount v) => shape.placementLabel root p (v ++ [i.val])) := by
  intro i j hij
  by_cases h : v.length % 2 = 1
  · let u : shape.OddInterior := ⟨v,hv,hd,h⟩
    change shape.placementLabel root p (u.val ++ [i.val]) <
      shape.placementLabel root p (u.val ++ [j.val])
    rw [placementLabel_left_child shape root p u i, placementLabel_left_child shape root p u j,
      Sum.Lex.inl_lt_inl_iff]
    exact p.1.property u hij
  · have he : v.length % 2 = 0 := by omega
    let u : shape.EvenInterior := ⟨v,hv,hd,he⟩
    change shape.placementLabel root p (u.val ++ [i.val]) <
      shape.placementLabel root p (u.val ++ [j.val])
    rw [placementLabel_right_child shape root p u i, placementLabel_right_child shape root p u j,
      Sum.Lex.inr_lt_inr_iff]
    exact p.2.property u hij

theorem placementLabel_even (shape : PlaneShape) {n : ℕ} (root : Fin n)
    (p : shape.OrderedPlacement root) {v : List ℕ} (hv : v ∈ shape.slots) (h : v.length % 2 = 0) :
    ∃ row, shape.placementLabel root p v = toLex (Sum.inl row) := by
  induction v using List.reverseRecOn with
  | nil => exact ⟨root, shape.placementLabel_root root p⟩
  | append_singleton u i _ =>
    obtain ⟨hu,hd,hi⟩ := (shape.child_mem u i).mp hv
    have h' : u.length % 2 = 1 := by simp only [List.length_append, List.length_singleton] at h; omega
    exact ⟨_, shape.placementLabel_left_child root p ⟨u,hu,hd,h'⟩ ⟨i,hi⟩⟩

theorem placementLabel_odd (shape : PlaneShape) {n : ℕ} (root : Fin n)
    (p : shape.OrderedPlacement root) {v : List ℕ} (hv : v ∈ shape.slots) (h : v.length % 2 = 1) :
    ∃ col, shape.placementLabel root p v = toLex (Sum.inr col) := by
  induction v using List.reverseRecOn with
  | nil => simp at h
  | append_singleton u i _ =>
    obtain ⟨hu,hd,hi⟩ := (shape.child_mem u i).mp hv
    have h' : u.length % 2 = 0 := by simp only [List.length_append, List.length_singleton] at h; omega
    exact ⟨_, shape.placementLabel_right_child root p ⟨u,hu,hd,h'⟩ ⟨i,hi⟩⟩

/-- Agreement of two actual label functions on the shape determines the
whole sibling-ordered placement. -/
theorem eq_of_placementLabel_eqOn (shape : PlaneShape) {n : ℕ} (root : Fin n)
    {p q : shape.OrderedPlacement root}
    (h : EqOn (shape.placementLabel root p) (shape.placementLabel root q) shape.slots) :
    p = q := by
  apply Prod.ext
  · apply Subtype.ext
    apply Function.Embedding.ext
    rintro ⟨u,i⟩
    apply Subtype.ext
    have hw := h ((shape.child_mem u.val i.val).mpr ⟨u.property.1,u.property.2.1,i.isLt⟩)
    rw [placementLabel_left_child shape root p u i, placementLabel_left_child shape root q u i] at hw
    exact Sum.inl.inj (toLex.injective hw)
  · apply Subtype.ext
    apply Function.Embedding.ext
    rintro ⟨u,i⟩
    have hw := h ((shape.child_mem u.val i.val).mpr ⟨u.property.1,u.property.2.1,i.isLt⟩)
    rw [placementLabel_right_child shape root p u i, placementLabel_right_child shape root q u i] at hw
    exact Sum.inr.inj (toLex.injective hw)

/-- Product of all sibling ordering factors on the two sides. -/
noncomputable def placementDivisor (shape : PlaneShape) : ℕ :=
  siblingGroupFactorials shape.rowGroupSize * siblingGroupFactorials shape.colGroupSize

theorem placementDivisor_pos (shape : PlaneShape) : 0 < shape.placementDivisor :=
  Nat.mul_pos (siblingGroupFactorials_pos _) (siblingGroupFactorials_pos _)

theorem card_slots_eq_succ_childCount (shape : PlaneShape) :
    Fintype.card shape.Slot = 1 + ((∑ u, shape.rowGroupSize u) + ∑ v, shape.colGroupSize v) := by
  have h := Fintype.card_congr shape.placementKeyEquiv
  rw [Fintype.card_sum, Fintype.card_option, Fintype.card_sigma, Fintype.card_sigma] at h
  simpa only [Fintype.card_fin, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h.symm

/-- The placement exponent is the number of edges of the shape, one for each
non-root word. -/
theorem card_slots_sub_one_eq_childCount (shape : PlaneShape) :
    Fintype.card shape.Slot - 1 = (∑ u, shape.rowGroupSize u) + ∑ v, shape.colGroupSize v := by
  rw [card_slots_eq_succ_childCount]
  omega

theorem placementDivisor_eq_prod_interior_factorial (shape : PlaneShape) :
    shape.placementDivisor = ∏ u : shape.Interior, (shape.childCount u.val).factorial := by
  have h := shape.interiorParityEquiv.prod_comp (fun u => (shape.childCount u.val).factorial)
  rw [Fintype.prod_sum_type] at h
  exact h

theorem sum_interior_childCount (shape : PlaneShape) :
    (∑ u : shape.Interior, shape.childCount u.val) = Fintype.card shape.Slot - 1 := by
  rw [card_slots_sub_one_eq_childCount]
  have h := shape.interiorParityEquiv.sum_comp (fun u => shape.childCount u.val)
  rw [Fintype.sum_sum_type] at h
  exact h.symm

/-- The normalized placement factor and the fixed labelled-cylinder
coefficient multiply to the product of the Poisson offspring masses. -/
theorem normalizedPlacementCylinderMass_eq_poisson_product (shape : PlaneShape) (rate : ℝ) :
    (rate^(Fintype.card shape.Slot - 1) * Real.exp (-(Fintype.card shape.Interior : ℝ) * rate)) *
      (1 / (shape.placementDivisor : ℝ)) =
      ∏ u : shape.Interior, Real.exp (-rate) * rate^(shape.childCount u.val) /
        (shape.childCount u.val).factorial := by
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Finset.prod_pow_eq_pow_sum, sum_interior_childCount, ← Real.exp_nat_mul,
    ← Nat.cast_prod, ← placementDivisor_eq_prod_interior_factorial]
  rw [mul_neg, ← neg_mul]
  ring

/-- The actual shape's ordered placement count divided by the array size to
its edge count converges to the reciprocal of its sibling ordering factor. -/
theorem tendsto_normalized_card_orderedPlacement (shape : PlaneShape)
    (roots : ∀ n : ℕ, Fin (n + 1)) :
    Tendsto (fun n : ℕ => (Fintype.card (shape.OrderedPlacement (roots n)) : ℝ) /
        ((n+1 : ℕ) : ℝ)^(Fintype.card shape.Slot - 1))
      atTop (𝓝 (1 / (shape.placementDivisor : ℝ))) := by
  rw [card_slots_sub_one_eq_childCount]
  exact tendsto_normalized_card_pinnedSiblingOrderedBipartitePlacement
    shape.rowGroupSize shape.colGroupSize roots

end Certificate.LocalExploration.PlaneShape

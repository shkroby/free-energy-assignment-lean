import Certificate.OverlapTrimShapeChildren
import Mathlib.Data.Finset.Option

/-! The row and column degrees of the symbolic plane shape decompose
into the parent contribution and the children. -/

open Finset Set
open scoped BigOperators

namespace Certificate.LocalExploration.PlaneShape

variable (shape : PlaneShape)

/-- The parent edge of a child, indexed by its position under the given slot. -/
def childEdgeOf (v : shape.Slot) (hv : v.val.length < shape.depth) (i : Fin (shape.childCount v.val)) :
    PlaneNonrootSlot shape :=
  ⟨v.val ++ [i.val], (shape.child_mem ..).mpr ⟨v.property,hv,i.isLt⟩, by simp⟩

theorem childEdgeOf_injective (v : shape.Slot) (hv : v.val.length < shape.depth) :
    Function.Injective (shape.childEdgeOf v hv) := by
  intro a b h
  have h' := congrArg Subtype.val h
  change v.val ++ [a.val] = v.val ++ [b.val] at h'
  exact Fin.ext (by simpa only [List.append_cancel_left_eq, List.singleton_inj] using h')

theorem edgeParent_childEdgeOf (v : shape.Slot) (hv : v.val.length < shape.depth)
    (i : Fin (shape.childCount v.val)) :
    shape.edgeParent (shape.childEdgeOf v hv i) = v := by
  apply Subtype.ext
  change (v.val ++ [i.val]).dropLast = v.val
  rw [List.dropLast_concat]

theorem filter_edgeParent_eq_image (S : Finset (PlaneNonrootSlot shape)) (v : shape.Slot)
    (hv : v.val.length < shape.depth) :
    S.filter (fun e => shape.edgeParent e = v) =
      (Finset.univ.filter (fun i => shape.childEdgeOf v hv i ∈ S)).image (shape.childEdgeOf v hv) := by
  apply Finset.ext
  intro e
  rw [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨he,hE⟩
    let i₀ := e.val.getLast e.property.2
    have hlast : e.val.dropLast ++ [i₀] = e.val := List.dropLast_append_getLast e.property.2
    have hp : e.val.dropLast = v.val := congrArg Subtype.val hE
    rw [hp] at hlast
    have hc := (shape.child_mem v.val i₀).mp (hlast.symm ▸ e.property.1)
    let i : Fin (shape.childCount v.val) := ⟨i₀,hc.2.2⟩
    have he' : shape.childEdgeOf v hv i = e := Subtype.ext hlast
    exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rwa [he']⟩,he'⟩
  · rintro ⟨i,hi,rfl⟩
    exact ⟨(Finset.mem_filter.mp hi).2,shape.edgeParent_childEdgeOf v hv i⟩

private theorem child_length_pos (e : PlaneNonrootSlot shape) :
    0 < (shape.edgeChild e).val.length := List.length_pos_iff.mpr e.property.2

private theorem parent_length (e : PlaneNonrootSlot shape) :
    (shape.edgeParent e).val.length + 1 = (shape.edgeChild e).val.length := by
  have h := shape.child_length_pos e
  change e.val.dropLast.length + 1 = e.val.length
  rw [List.length_dropLast]
  change 0 < e.val.length at h
  omega

theorem shapeEdgeRow_eq_of_even_child {e : PlaneNonrootSlot shape} (h : e.val.length % 2 = 0) :
    shape.shapeEdgeRow e = shape.edgeChild e := by
  rw [shapeEdgeRow, if_pos h]
  rfl

theorem shapeEdgeRow_eq_of_odd_child {e : PlaneNonrootSlot shape} (h : e.val.length % 2 = 1) :
    shape.shapeEdgeRow e = shape.edgeParent e := by
  have hn : e.val.length % 2 ≠ 0 := by omega
  rw [shapeEdgeRow, if_neg hn]
  rfl

theorem shapeEdgeCol_eq_of_even_child {e : PlaneNonrootSlot shape} (h : e.val.length % 2 = 0) :
    shape.shapeEdgeCol e = shape.edgeParent e := by
  rw [shapeEdgeCol, if_pos h]
  rfl

theorem shapeEdgeCol_eq_of_odd_child {e : PlaneNonrootSlot shape} (h : e.val.length % 2 = 1) :
    shape.shapeEdgeCol e = shape.edgeChild e := by
  have hn : e.val.length % 2 ≠ 0 := by omega
  rw [shapeEdgeCol, if_neg hn]
  rfl

private theorem rowFiber_iff (v : shape.Slot) (hv : v.val.length % 2 = 0)
    (e : PlaneNonrootSlot shape) :
    shape.shapeEdgeRow e = v ↔ shape.edgeParent e = v ∨ shape.edgeChild e = v := by
  have hlen := shape.parent_length e
  change (shape.edgeParent e).val.length+1 = e.val.length at hlen
  by_cases h : e.val.length % 2 = 0
  · have hne : shape.edgeParent e ≠ v := by
      intro hP
      have heq := congrArg (fun a : shape.Slot => a.val.length) hP
      omega
    simp [shape.shapeEdgeRow_eq_of_even_child h,hne]
  · have hc : e.val.length % 2 = 1 := by omega
    have hne : shape.edgeChild e ≠ v := by
      intro hC
      have heq : e.val.length = v.val.length := congrArg (fun a : shape.Slot => a.val.length) hC
      omega
    simp [shape.shapeEdgeRow_eq_of_odd_child hc,hne]

private theorem colFiber_iff (v : shape.Slot) (hv : v.val.length % 2 = 1)
    (e : PlaneNonrootSlot shape) :
    shape.shapeEdgeCol e = v ↔ shape.edgeParent e = v ∨ shape.edgeChild e = v := by
  have hlen := shape.parent_length e
  change (shape.edgeParent e).val.length+1 = e.val.length at hlen
  by_cases h : e.val.length % 2 = 0
  · have hne : shape.edgeChild e ≠ v := by
      intro hC
      have heq : e.val.length = v.val.length := congrArg (fun a : shape.Slot => a.val.length) hC
      omega
    simp [shape.shapeEdgeCol_eq_of_even_child h,hne]
  · have hc : e.val.length % 2 = 1 := by omega
    have hne : shape.edgeParent e ≠ v := by
      intro hP
      have heq := congrArg (fun a : shape.Slot => a.val.length) hP
      omega
    simp [shape.shapeEdgeCol_eq_of_odd_child hc,hne]

private theorem card_filter_parent_or_child (S : Finset (PlaneNonrootSlot shape))
    (v : shape.Slot) (hv : v.val.length < shape.depth) :
    (S.filter (fun e => shape.edgeParent e = v ∨ shape.edgeChild e = v)).card =
      (Finset.univ.filter (fun i => shape.childEdgeOf v hv i ∈ S)).card +
      (S ∩ (shape.parentEdge v).toFinset).card := by
  classical
  have hEq : S.filter (fun e => shape.edgeParent e = v ∨ shape.edgeChild e = v) =
      (S.filter (fun e => shape.edgeParent e = v)) ∪ (S ∩ (shape.parentEdge v).toFinset) := by
    apply Finset.ext
    intro e
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_inter, Option.mem_toFinset, Option.mem_def,
      ← and_or_left]
    rw [shape.parentEdge_eq_some_iff, eq_comm (a := v)]
  rw [hEq, Finset.card_union_of_disjoint, shape.filter_edgeParent_eq_image S v hv,
    Finset.card_image_of_injective _ (shape.childEdgeOf_injective v hv)]
  refine Finset.disjoint_left.mpr ?_
  intro e hp hc
  have hp' : shape.edgeParent e = v := (Finset.mem_filter.mp hp).2
  have hc' := (shape.parentEdge_eq_some_iff v e).mp (Option.mem_def.mp (Option.mem_toFinset.mp (Finset.mem_inter.mp hc).2))
  exact shape.edgeParent_ne_child e (hp'.trans hc')

/-- An interior row has one edge per child and, away from the root,
its own edge to its parent. -/
theorem rawRowDegree_eq_childCount (v : shape.Slot) (hv : v.val.length < shape.depth)
    (hrow : v.val.length % 2 = 0) :
    (Finset.univ.filter (fun e => shape.shapeEdgeRow e = v)).card =
      shape.childCount v.val + if v.val = [] then 0 else 1 := by
  have heq : Finset.univ.filter (fun e => shape.shapeEdgeRow e = v) =
      Finset.univ.filter (fun e => shape.edgeParent e = v ∨ shape.edgeChild e = v) := by
    apply Finset.ext
    intro e
    simp only [Finset.mem_filter, shape.rowFiber_iff v hrow]
  rw [heq, shape.card_filter_parent_or_child Finset.univ v hv]
  by_cases h : v.val = [] <;> simp [parentEdge,h]

/-- If a column's parent edge passed the row trim, then its post-row
degree counts that edge and exactly the originally eligible child rows. -/
theorem postRowColumnDegree_eq_eligibleChildren (D : ℕ) (v : shape.Slot)
    (hv : v.val.length + 1 < shape.depth) (hcol : v.val.length % 2 = 1)
    (p : PlaneNonrootSlot shape)
    (hp : shape.parentEdge v = some p) (hpKeep : p ∈ shape.shapeTrimRows D) :
    ((shape.shapeTrimRows D).filter (fun e => shape.shapeEdgeCol e = v)).card =
      (Finset.univ.filter (fun i : Fin (shape.childCount v.val) =>
        shape.childCount ((shape.childEdgeOf v (by omega) i).val) + 1 ≤ D)).card + 1 := by
  have hv' : v.val.length < shape.depth := by omega
  have heq : (shape.shapeTrimRows D).filter (fun e => shape.shapeEdgeCol e = v) =
      (shape.shapeTrimRows D).filter (fun e => shape.edgeParent e = v ∨ shape.edgeChild e = v) := by
    apply Finset.ext
    intro e
    simp only [Finset.mem_filter, shape.colFiber_iff v hcol]
  rw [heq, shape.card_filter_parent_or_child _ v hv', hp]
  have hInt : shape.shapeTrimRows D ∩ (some p).toFinset = {p} := by
    simp [hpKeep]
  rw [hInt, Finset.card_singleton]
  apply congrArg (fun N : ℕ => N + 1)
  apply congrArg (fun S : Finset (Fin (shape.childCount v.val)) => S.card)
  apply Finset.ext
  intro i
  let e := shape.childEdgeOf v hv' i
  have heV : e.val.length = v.val.length+1 := by simp [e,childEdgeOf]
  have parity : e.val.length % 2 = 0 := by omega
  have hlen : (shape.edgeChild e).val.length < shape.depth := heV ▸ hv
  have hne : (shape.edgeChild e).val ≠ [] := e.property.2
  have hRaw := shape.rawRowDegree_eq_childCount (shape.edgeChild e) hlen parity
  simp only [hne, if_false] at hRaw
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change e ∈ shape.shapeTrimRows D ↔ shape.childCount e.val + 1 ≤ D
  rw [shapeTrimRows, Finset.mem_filter, shape.shapeEdgeRow_eq_of_even_child parity,
    hRaw]
  simp [edgeChild]

/-- A slot is reached if it is an originally eligible root, or if its
own parent edge passed both trims. -/
def TrimReached (D : ℕ) (v : shape.Slot) : Prop :=
  (v.val = [] ∧ shape.childCount v.val ≤ D) ∨
    ∃ p, shape.parentEdge v = some p ∧ p ∈ shape.shapeTrimDegrees D

theorem mem_shapeTrimRows (D : ℕ) (e : PlaneNonrootSlot shape) :
    e ∈ shape.shapeTrimRows D ↔
      (Finset.univ.filter (fun f => shape.shapeEdgeRow f = shape.shapeEdgeRow e)).card ≤ D :=
  Finset.mem_filter.trans (and_iff_right (Finset.mem_univ e))

theorem mem_shapeTrimDegrees (D : ℕ) (e : PlaneNonrootSlot shape) :
    e ∈ shape.shapeTrimDegrees D ↔ e ∈ shape.shapeTrimRows D ∧
      ((shape.shapeTrimRows D).filter (fun f => shape.shapeEdgeCol f = shape.shapeEdgeCol e)).card ≤ D :=
  Finset.mem_filter

theorem trimReached_of_kept (D : ℕ) (e : PlaneNonrootSlot shape) (he : e ∈ shape.shapeTrimDegrees D) :
    shape.TrimReached D (shape.edgeChild e) :=
  Or.inr ⟨e,(shape.parentEdge_eq_some_iff _ _).mpr rfl,he⟩

private theorem orderedRowOfReached (D : ℕ) (v : shape.Slot) (hv : v.val.length < shape.depth)
    (hr : v.val.length % 2 = 0) (hReach : shape.TrimReached D v) :
    (Finset.univ.filter (fun e => shape.shapeEdgeRow e = v)).card ≤ D := by
  rcases hReach with ⟨h0,hd⟩ | ⟨p,hp,hKeep⟩
  · rw [shape.rawRowDegree_eq_childCount v hv hr, if_pos h0, Nat.add_zero]
    exact hd
  · have hVp : v = shape.edgeChild p := (shape.parentEdge_eq_some_iff _ _).mp hp
    have hpEven : p.val.length % 2 = 0 := by
      rw [hVp] at hr
      exact hr
    have hs : shape.shapeEdgeRow p = v :=
      (shape.shapeEdgeRow_eq_of_even_child hpEven).trans hVp.symm
    have hd := (shape.mem_shapeTrimRows D p).mp ((shape.mem_shapeTrimDegrees D p).mp hKeep).1
    rwa [hs] at hd

private theorem orderedColumnOfReached (D : ℕ) (v : shape.Slot) (hc : v.val.length % 2 = 1)
    (hReach : shape.TrimReached D v) :
    ((shape.shapeTrimRows D).filter (fun e => shape.shapeEdgeCol e = v)).card ≤ D := by
  rcases hReach with ⟨h0,_⟩ | ⟨p,hp,hKeep⟩
  · simp [h0] at hc
  · have hVp : v = shape.edgeChild p := (shape.parentEdge_eq_some_iff _ _).mp hp
    have hpOdd : p.val.length % 2 = 1 := by
      rw [hVp] at hc
      exact hc
    have hs : shape.shapeEdgeCol p = v :=
      (shape.shapeEdgeCol_eq_of_odd_child hpOdd).trans hVp.symm
    have hd := ((shape.mem_shapeTrimDegrees D p).mp hKeep).2
    rwa [hs] at hd

/-- From an eligible row, a child column is kept exactly when the child
column's post-row degree passes. From an eligible column, a child row
is kept exactly when that row's original degree passes. -/
theorem childEdge_mem_trim_of_reached (D : ℕ) (v : shape.Slot)
    (hv : v.val.length + 2 < shape.depth) (hReach : shape.TrimReached D v)
    (i : Fin (shape.childCount v.val)) :
    shape.childEdgeOf v (by omega) i ∈ shape.shapeTrimDegrees D ↔
      if v.val.length % 2 = 0 then
        1 + (Finset.univ.filter (fun j : Fin (shape.childCount (v.val ++ [i.val])) =>
          1 + shape.childCount ((v.val ++ [i.val]) ++ [j.val]) ≤ D)).card ≤ D
      else 1 + shape.childCount (v.val ++ [i.val]) ≤ D := by
  let e := shape.childEdgeOf v (by omega) i
  let w := shape.edgeChild e
  have hParent : shape.edgeParent e = v := shape.edgeParent_childEdgeOf _ _ _
  have hLen : e.val.length = v.val.length + 1 := by simp [e,childEdgeOf]
  have hW : w.val.length = e.val.length := rfl
  have hV : v.val.length < shape.depth := by omega
  have hNotRoot : w.val ≠ [] := e.property.2
  by_cases hpar : v.val.length % 2 = 0
  · have he : e.val.length % 2 = 1 := by omega
    have hRow := (shape.shapeEdgeRow_eq_of_odd_child he).trans hParent
    have hKeep : e ∈ shape.shapeTrimRows D := by
      rw [shape.mem_shapeTrimRows D e, hRow]
      exact shape.orderedRowOfReached D v hV hpar hReach
    have hCol := shape.postRowColumnDegree_eq_eligibleChildren D w (by omega) he e
      ((shape.parentEdge_eq_some_iff _ _).mpr rfl) hKeep
    simp only [if_pos hpar]
    change e ∈ shape.shapeTrimDegrees D ↔ _
    rw [shape.mem_shapeTrimDegrees D e, shape.shapeEdgeCol_eq_of_odd_child he, hCol, and_iff_right hKeep]
    simp [w,e,edgeChild,childEdgeOf,Nat.add_comm]
    rfl
  · have hpar' : v.val.length % 2 = 1 := by omega
    have he : e.val.length % 2 = 0 := by omega
    have hCol := (shape.shapeEdgeCol_eq_of_even_child he).trans hParent
    have hKeep := shape.orderedColumnOfReached D v hpar' hReach
    have hRaw := shape.rawRowDegree_eq_childCount w (by omega) he
    simp only [hNotRoot, if_false] at hRaw
    simp only [if_neg hpar]
    change e ∈ shape.shapeTrimDegrees D ↔ _
    rw [shape.mem_shapeTrimDegrees D e, hCol, and_iff_left hKeep, shape.mem_shapeTrimRows D e,
      shape.shapeEdgeRow_eq_of_even_child he, hRaw]
    simp [w,e,edgeChild,childEdgeOf,Nat.add_comm]

end Certificate.LocalExploration.PlaneShape

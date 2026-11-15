import Certificate.OverlapUnorderedTreeLaw
import Certificate.OverlapUnorderedBP
import Certificate.OverlapCanonicalIterates
import Certificate.OverlapCanonicalSupport

/-! The unordered evaluator computes the same finite-depth quantities as
the degree-trimmed canonical recursion. -/

open Filter Finset MeasureTheory Set
open scoped BigOperators

namespace Certificate.CanonicalTree

open UnorderedTree

variable {β d R z : ℝ} {D : ℕ} {ω : Environment}

private theorem child_ne_root (v : Vertex) (i : ℕ) : child v i ≠ [] := by
  simp [child]

private theorem canonicalRowDegree (k : ℕ) (v : Vertex) (hv : v ≠ []) :
    rowDegree (k+1) (canonicalUnorderedTree d R (k+1) ω v) = cutoffDegree d R ω v := by
  simp only [canonicalUnorderedTree, ofChildren, rowDegree, childCount_node, cutoffDegree,
    if_neg hv, Nat.add_comm]

private theorem canonicalColumnDegree (k : ℕ) (v : Vertex) (i : ℕ)
    (hv : cutoffDegree d R ω v ≤ D) :
    reachedColumnDegree D (k+2) (canonicalUnorderedTree d R (k+2) ω (child v i)) =
      cutoffColumnDegree d R D ω (child v i) := by
  have he : (child v i).dropLast = v := by simp [child]
  have hc (j : ℕ) :
      rowDegree (k+1) (canonicalUnorderedTree d R (k+1) ω (child (child v i) j)) =
        cutoffDegree d R ω (child (child v i) j) :=
    canonicalRowDegree k _ (child_ne_root _ _)
  classical
  change 1 + countChildrenWhere (fun a => rowDegree (k+1) a.2 ≤ D)
    (node (cutoffOffspringNat d R (ω (child v i))) (fun j =>
      (arrivalLength d (ω (child v i)) j,
        canonicalUnorderedTree d R (k+1) ω (child (child v i) j)))) = _
  rw [countChildrenWhere, sumChildren_node]
  simp only [hc, cutoffColumnDegree, if_neg (child_ne_root v i), he, if_pos hv, Nat.add_comm 1]
  congr 1
  let g (j : ℕ) : ℕ := if cutoffDegree d R ω (child (child v i) j) ≤ D then 1 else 0
  change (∑ j : Fin (cutoffOffspringNat d R (ω (child v i))), g j.val) = _
  rw [Fin.sum_univ_eq_sum_range g]
  simp [g]

private def ReachedAt (d R : ℝ) (D : ℕ) (ω : Environment) (v : Vertex) (row : Bool) : Prop :=
  if row then cutoffDegree d R ω v ≤ D else cutoffColumnDegree d R D ω v ≤ D

private theorem reached_child_weight (k : ℕ) (v : Vertex) (i : ℕ) (row : Bool)
    (hpar : v.length % 2 = 0 ↔ row = true)
    (hreach : ReachedAt d R D ω v row) (hlen : arrivalLength d (ω v) i ≤ R) :
    let t := canonicalUnorderedTree d R (k+2) ω (child v i)
    trimmedWeight β d R D ω v i =
      (if childAdmitted D row (k+2) t then Real.exp (-β * arrivalLength d (ω v) i) else 0) ∧
      (childAdmitted D row (k+2) t → ReachedAt d R D ω (child v i) (!row)) := by
  cases row with
  | false =>
    have hnot : v.length % 2 ≠ 0 := fun h => by simpa using hpar.mp h
    have hr : cutoffColumnDegree d R D ω v ≤ D := hreach
    simp only [trimmedWeight, if_neg hnot, hr, and_true, weightFor, cutoffKernel, if_pos hlen,
      childAdmitted, Bool.false_eq_true, if_false, canonicalRowDegree (k+1) _ (child_ne_root v i),
      Bool.not_false, ReachedAt, if_true]
    exact ⟨trivial, id⟩
  | true =>
    have he := hpar.mpr rfl
    have hr : cutoffDegree d R ω v ≤ D := hreach
    simp only [trimmedWeight, if_pos he, hr, true_and, weightFor, cutoffKernel, if_pos hlen,
      childAdmitted, if_true, canonicalColumnDegree k v i hr, Bool.not_true, ReachedAt,
      Bool.false_eq_true, if_false]
    exact id

private theorem canonical_weight_eq_zero_off {v : Vertex} {i : ℕ}
    (h : ¬ arrivalLength d (ω v) i ≤ R) : trimmedWeight β d R D ω v i = 0 := by
  have hb := trimmedWeight_bounds β d R D ω v i
  exact le_antisymm (hb.2.trans_eq (if_neg h)) hb.1

set_option maxHeartbeats 1000000 in
private theorem canonical_upwardIterate_eq
    (hsupp : ∀ v i, arrivalLength d (ω v) i ≤ R ↔ i < cutoffOffspringNat d R (ω v))
    (s k : ℕ) (hk : s+2 ≤ k) (v : Vertex) (row : Bool)
    (hpar : v.length % 2 = 0 ↔ row = true) (hreach : ReachedAt d R D ω v row) :
    upwardIterate D β z k s row (canonicalUnorderedTree d R k ω v) =
      trimmedDownwardIterate β d R z D s ω v := by
  induction s generalizing k v row with
  | zero =>
    cases k <;> rfl
  | succ s ih =>
    obtain ⟨k',rfl⟩ : ∃ j : ℕ, k = j+3 := ⟨k-3, by omega⟩
    let n := cutoffOffspringNat d R (ω v)
    let f (i : ℕ) := trimmedWeight β d R D ω v i *
      trimmedDownwardIterate β d R z D s ω (child v i)
    change (z + sumChildren _ (node n (fun i =>
      (arrivalLength d (ω v) i,
        canonicalUnorderedTree d R (k'+2) ω (child v i)))))⁻¹ = (z + ∑' i, f i)⁻¹
    rw [sumChildren_node, tsum_eq_sum (s := range n) (fun i hi => by
      simp only [f, canonical_weight_eq_zero_off (fun h => hi (mem_range.mpr ((hsupp v i).mp h))),
        zero_mul]), ← Fin.sum_univ_eq_sum_range]
    congr 2
    apply sum_congr rfl
    intro i _
    dsimp only [f, Prod.fst, Prod.snd]
    have hw := reached_child_weight (β := β) (D := D) k' v i.val row hpar hreach
      ((hsupp v i.val).mpr i.isLt)
    have hp : (child v i.val).length % 2 = 0 ↔ (!row) = true := by
      simp only [child, List.length_append, List.length_singleton]
      cases row <;> simp_all <;> omega
    rw [hw.1]
    split_ifs with h
    · rw [ih (k'+2) (by omega) (child v i.val) (!row) hp (hw.2 h)]
    · simp

private theorem canonical_rootChildTerm_eq
    (hsupp : ∀ v i, arrivalLength d (ω v) i ≤ R ↔ i < cutoffOffspringNat d R (ω v))
    (s k : ℕ) (hk : s+2 ≤ k) (hroot : cutoffDegree d R ω [] ≤ D)
    (i : Fin (cutoffOffspringNat d R (ω []))) :
    rootChildTerm D β z k s (arrivalLength d (ω []) i,
        canonicalUnorderedTree d R k ω (child [] i)) =
      trimmedWeight β d R D ω [] i * trimmedDownwardIterate β d R z D s ω (child [] i) := by
  obtain ⟨k',rfl⟩ : ∃ j : ℕ, k = j+2 := ⟨k-2, by omega⟩
  unfold rootChildTerm
  dsimp only [Prod.fst, Prod.snd]
  have hw := reached_child_weight (β := β) (D := D) k' [] i.val true (by simp)
    hroot ((hsupp [] i.val).mpr i.isLt)
  rw [hw.1]
  split_ifs with h
  · rw [canonical_upwardIterate_eq hsupp s (k'+2) hk (child [] i.val) false (by simp [child])
      (hw.2 h)]
  · simp

private theorem canonical_rootExcluding_eq
    (hsupp : ∀ v i, arrivalLength d (ω v) i ≤ R ↔ i < cutoffOffspringNat d R (ω v))
    (s k : ℕ) (hk : s+2 ≤ k) (hroot : cutoffDegree d R ω [] ≤ D)
    (i : Fin (cutoffOffspringNat d R (ω []))) :
    rootExcluding D β z k s (canonicalUnorderedTree d R (k+1) ω [])
        (arrivalLength d (ω []) i, canonicalUnorderedTree d R k ω (child [] i)) =
      trimmedRootCavityIterate β d R z D ω s i := by
  cases s with
  | zero => rfl
  | succ s =>
    let n := cutoffOffspringNat d R (ω [])
    let f (j : ℕ) := trimmedWeight β d R D ω [] j *
      trimmedDownwardIterate β d R z D s ω (child [] j)
    change (z + sumChildren (rootChildTerm D β z k s) (node n (fun j =>
        (arrivalLength d (ω []) j, canonicalUnorderedTree d R k ω (child [] j)))) -
          rootChildTerm D β z k s
            (arrivalLength d (ω []) i, canonicalUnorderedTree d R k ω (child [] i)))⁻¹ =
      (z + ∑' j, (if j = i.val then 0 else trimmedWeight β d R D ω [] j) *
        trimmedDownwardIterate β d R z D s ω (child [] j))⁻¹
    rw [sumChildren_node]
    simp_rw [canonical_rootChildTerm_eq hsupp s k (by omega : s+2 ≤ k) hroot]
    change (z + (∑ j : Fin n, f j.val) - f i.val)⁻¹ = _
    rw [Fin.sum_univ_eq_sum_range f]
    have hf (j : ℕ) : (if j = i.val then 0 else trimmedWeight β d R D ω [] j) *
        trimmedDownwardIterate β d R z D s ω (child [] j) = if j ≠ i.val then f j else 0 := by
      by_cases hj : j = i.val <;> simp [hj, f]
    simp_rw [hf]
    have hs := Finset.sum_erase_add (range n) f (mem_range.mpr i.isLt)
    have hs' : (∑ j ∈ range n, f j) - f i.val = ∑ j ∈ (range n).erase i.val, f j := by
      linarith
    rw [tsum_eq_sum (s := range n) (fun j hj => by
      have hw := canonical_weight_eq_zero_off (β := β) (D := D)
        (fun h => hj (mem_range.mpr ((hsupp [] j).mp h)))
      simp [f, hw])]
    simp only [← Finset.sum_filter, Finset.filter_ne']
    rw [add_sub_assoc, hs']

set_option maxHeartbeats 1000000 in
theorem canonical_rootChildOccupation_eq
    (hsupp : ∀ v i, arrivalLength d (ω v) i ≤ R ↔ i < cutoffOffspringNat d R (ω v))
    (s : ℕ) (i : Fin (cutoffOffspringNat d R (ω []))) :
    rootChildOccupation D β z (s+2) s (canonicalUnorderedTree d R (s+3) ω [])
        (arrivalLength d (ω []) i, canonicalUnorderedTree d R (s+2) ω (child [] i)) =
      trimmedRootOccupationIterate β d R z D s ω i := by
  have hr : cutoffDegree d R ω [] = cutoffOffspringNat d R (ω []) := by simp [cutoffDegree]
  have hc :
      childCount (canonicalUnorderedTree d R (s+3) ω []) = cutoffOffspringNat d R (ω []) :=
    childCount_node _
  by_cases hroot : cutoffDegree d R ω [] ≤ D
  · have hw := reached_child_weight (β := β) (D := D) s [] i.val true (by simp)
      hroot ((hsupp [] i.val).mpr i.isLt)
    have hn : cutoffOffspringNat d R (ω []) ≤ D := by simpa only [hr] using hroot
    simp only [rootChildOccupation, hc, hn, true_and, trimmedRootOccupationIterate, hw.1,
      Prod.fst, Prod.snd]
    split_ifs with h
    · rw [canonical_rootExcluding_eq hsupp s (s+2) le_rfl hroot,
        canonical_upwardIterate_eq hsupp s (s+2) le_rfl _ false (by simp [child]) (hw.2 h)]
    · simp [edgeOccupation]
  · have hn : ¬ cutoffOffspringNat d R (ω []) ≤ D := by simpa only [hr] using hroot
    simp [rootChildOccupation, hc, hn, trimmedRootOccupationIterate, hroot,
      trimmedWeight, edgeOccupation]

theorem ae_canonical_rootSquare_eq {β d R z : ℝ} (hd : 0 < d) (hR : 0 ≤ R)
    (D s : ℕ) :
    ∀ᵐ ω ∂law, rootSquare D β z (s+2) s (canonicalUnorderedTree d R (s+3) ω []) =
      trimmedSquareTest β d R z D s ω := by
  filter_upwards [ae_arrivalLength_le_iff_lt_cutoffOffspringNat hd hR] with ω h
  let n := cutoffOffspringNat d R (ω [])
  change min 1 (sumChildren _ (node n (fun i =>
      (arrivalLength d (ω []) i, canonicalUnorderedTree d R (s+2) ω (child [] i))))) = _
  rw [sumChildren_node]
  simp only [canonical_rootChildOccupation_eq h s, trimmedSquareTest, Overlap.squareRowTest]
  let g (j : ℕ) := (trimmedRootOccupationIterate β d R z D s ω j)^2
  change min 1 (∑ i : Fin n, g i.val) = min 1 (∑ i ∈ range n, g i)
  rw [Fin.sum_univ_eq_sum_range g]

end Certificate.CanonicalTree

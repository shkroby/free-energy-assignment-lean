import Certificate.OverlapCanonicalEvaluator
import Certificate.OverlapUnorderedThird

/-! The canonical third occupation is read from the same unordered marked
neighborhood as the square sum. -/

open Filter MeasureTheory Finset Set

namespace Certificate.CanonicalTree

open UnorderedTree

theorem trimmedRootOccupationIterate_mem {β d R z : ℝ} (hz : 0 < z) (D k : ℕ)
    (ω : Environment) (i : ℕ) : trimmedRootOccupationIterate β d R z D k ω i ∈ Set.Icc 0 1 := by
  have hW (v : Vertex) (j : ℕ) : 0 ≤ trimmedWeight β d R D ω v j :=
    (trimmedWeight_bounds β d R D ω v j).1
  have hUp (s : ℕ) (v : Vertex) : 0 ≤ trimmedDownwardIterate β d R z D s ω v := by
    induction s generalizing v with
    | zero => exact inv_nonneg.mpr hz.le
    | succ s ih =>
      exact (TreeBoundary.update_pos_le hz (hW v) (fun j => ih (child v j))).1.le
  have hRoot : 0 ≤ trimmedRootCavityIterate β d R z D ω k i := by
    cases k with
    | zero => exact inv_nonneg.mpr hz.le
    | succ k =>
      apply (TreeBoundary.update_pos_le hz (w := fun j => if j = i then 0 else trimmedWeight β d R D ω [] j)
        (fun j => ?_) (fun j => hUp k (child [] j))).1.le
      split_ifs
      · exact le_rfl
      · exact hW [] j
  let x := trimmedWeight β d R D ω [] i * trimmedRootCavityIterate β d R z D ω k i *
    trimmedDownwardIterate β d R z D k ω (child [] i)
  have hx : 0 ≤ x := mul_nonneg (mul_nonneg (hW [] i) hRoot) (hUp k (child [] i))
  have hp : 0 < 1+x := by linarith only [hx]
  change x/(1+x) ∈ Set.Icc 0 1
  exact ⟨div_nonneg hx hp.le, (div_le_one hp).mpr (by linarith)⟩

theorem ae_canonical_rootSmallThird_eq {β d R z η : ℝ}
    (hd : 0 < d) (hR : 0 ≤ R) (hz : 0 < z) (D s : ℕ) :
    ∀ᵐ ω ∂law,
      Overlap.smallOccupationTest η (rootThird D β z (s+2) s (canonicalUnorderedTree d R (s+3) ω [])) =
        trimmedSmallThirdTest β d R z η D s ω := by
  filter_upwards [ae_arrivalLength_le_iff_lt_cutoffOffspringNat hd hR] with ω h
  let n := cutoffOffspringNat d R (ω [])
  let x (i : Fin n) := (arrivalLength d (ω []) i,
    canonicalUnorderedTree d R (s+2) ω (child [] i))
  let a (i : ℕ) := trimmedRootOccupationIterate β d R z D s ω i
  have hOcc (i : Fin n) : rootChildOccupation D β z (s+2) s (node n x) (x i) = a i :=
    canonical_rootChildOccupation_eq h s i
  have hThird := rootThird_node D β z s x (fun i => by
    rw [hOcc]
    exact trimmedRootOccupationIterate_mem hz D s ω i)
  have he : (Finset.univ : Finset (Fin n)).image Fin.val = Finset.range n := by
    apply Finset.ext
    intro j
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range]
    exact ⟨fun ⟨i,hi⟩ => hi ▸ i.isLt, fun hj => ⟨⟨j,hj⟩,rfl⟩⟩
  change Overlap.smallOccupationTest η (rootThird D β z (s+2) s (node n x)) =
    Overlap.smallOccupationTest η (Overlap.thirdOccupation (Finset.range n) a)
  apply congrArg (Overlap.smallOccupationTest η)
  rw [hThird, ← he, Overlap.thirdOccupation_image _ Fin.val Fin.val_injective]
  exact congrArg (Overlap.thirdOccupation (Finset.univ : Finset (Fin n)))
    (funext fun i => hOcc i)

end Certificate.CanonicalTree

import Certificate.OverlapCanonicalBridge
import Certificate.OverlapCanonicalThird
import Certificate.OverlapUnorderedShapeMixture
import Certificate.OverlapTrimShapeUnordered

/-! The two occupation observables have the same finite-depth expectation
in the canonical marked tree and in the independent-mark shape mixture. -/

open Filter MeasureTheory Set

namespace Certificate.Overlap

open LocalExploration CanonicalTree UnorderedTree

private theorem rootSquare_mem (D : ℕ) (β z : ℝ) (k s : ℕ) (t : Depth (k+1)) :
    rootSquare D β z k s t ∈ Icc 0 1 := by
  unfold rootSquare sumChildren
  refine ⟨le_min zero_le_one ?_, min_le_left _ _⟩
  let f (a : ℝ × Depth k) := (rootChildOccupation D β z k s t a)^2
  change 0 ≤ (Multiset.map f t).sum
  exact Multiset.sum_nonneg (fun x hx => by
    obtain ⟨a,_,rfl⟩ := Multiset.mem_map.mp hx
    exact sq_nonneg _)

theorem canonicalOccupationTests {β d : ℝ} (hβ : 0 < β) (hd : 0 < d) :
    CanonicalOccupationTests β d := by
  apply canonicalOccupationTests_of_integral_eq hβ hd
  · intro z hz R hR D s
    have hR' : 0 < (R:ℝ) := Nat.cast_pos.mpr hR
    let P := rootSquare D β z (s+2) s
    have hmix := integral_canonicalUnorderedTree_eq_shapeMixture hd hR' (s+3) P
      (measurable_rootSquare D β z (s+2) s) (rootSquare_mem D β z (s+2) s)
    calc
      _ = ∑' c : PlaneShapeCode (s+3), cutoffShapeMass d R c *
            ∫ x, P (c.shape.encodeUnorderedAt c.shape_depth x)
              ∂Measure.infinitePi (fun _ : c.shape.NonRootSlot => truncatedIntensity d R) := by
        apply tsum_congr
        intro c
        congr 1
        apply integral_congr_ae
        exact Eventually.of_forall fun x =>
          c.shape.squareRowTestBCF_eq_unordered D β hz x s c.shape_depth
      _ = ∫ ω, P (canonicalUnorderedTree d R (s+3) ω []) ∂law := hmix.symm
      _ = _ := integral_congr_ae (ae_canonical_rootSquare_eq hd hR'.le D s)
  · intro z hz R hR D s η hη
    have hR' : 0 < (R:ℝ) := Nat.cast_pos.mpr hR
    let P (t : Depth (s+3)) := smallOccupationTest η (rootThird D β z (s+2) s t)
    have hmix := integral_canonicalUnorderedTree_eq_shapeMixture hd hR' (s+3) P
      ((continuous_smallOccupationTest η).measurable.comp
        (measurable_rootThird D β z (s+2) s)) (fun _ => smallOccupationTest_mem _ _)
    calc
      _ = ∑' c : PlaneShapeCode (s+3), cutoffShapeMass d R c *
            ∫ x, P (c.shape.encodeUnorderedAt c.shape_depth x)
              ∂Measure.infinitePi (fun _ : c.shape.NonRootSlot => truncatedIntensity d R) := by
        apply tsum_congr
        intro c
        congr 1
        apply integral_congr_ae
        exact Eventually.of_forall fun x =>
          c.shape.smallOccupationTestBCF_eq_unordered D β η hz x s c.shape_depth
      _ = ∫ ω, P (canonicalUnorderedTree d R (s+3) ω []) ∂law := hmix.symm
      _ = _ := integral_congr_ae (ae_canonical_rootSmallThird_eq hd hR'.le hz D s)

end Certificate.Overlap

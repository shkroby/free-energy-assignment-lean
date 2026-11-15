import Certificate.OverlapEmpiricalTreeAssembly
import Certificate.OverlapCanonicalTestLimits
import Certificate.OverlapCanonicalIterateLimit

/-! Convergence of the empirical test limits, once identified with the
corresponding finite-depth expectations on the canonical tree. -/

open Filter MeasureTheory
open scoped Topology

namespace Certificate.Overlap

open LocalExploration CanonicalTree

theorem canonicalOccupationTests_of_integral_eq {β d : ℝ} (hβ : 0 < β) (hd : 0 < d)
    (hSquare : ∀ {z : ℝ} (hz : 0 < z) {R : ℕ}, 0 < R → ∀ D k : ℕ,
      (∑' c : PlaneShapeCode (k+3), cutoffShapeMass d R c *
        ∫ x, c.shape.squareRowTestBCF D k β hz x
          ∂Measure.infinitePi (fun _ : c.shape.NonRootSlot => truncatedIntensity d R)) =
        ∫ ω, trimmedSquareTest β d R z D k ω ∂law)
    (hThird : ∀ {z : ℝ} (hz : 0 < z) {R : ℕ}, 0 < R → ∀ D k : ℕ, ∀ {η : ℝ}, 0 < η →
      (∑' c : PlaneShapeCode (k+3), cutoffShapeMass d R c *
        ∫ x, c.shape.smallOccupationTestBCF D k β η hz x
          ∂Measure.infinitePi (fun _ : c.shape.NonRootSlot => truncatedIntensity d R)) =
        ∫ ω, trimmedSmallThirdTest β d R z η D k ω ∂law) :
    CanonicalOccupationTests β d := by
  intro z hz R hR D
  have hR' : 0 ≤ (R:ℝ) := Nat.cast_nonneg _
  have ht := ae_tendsto_trimmedRootOccupationIterate hβ.le hd hR' hz D
  constructor
  · simp_rw [hSquare hz hR D]
    exact tendsto_integral_trimmedSquareTest hd hR' D ht
  · intro η hη
    refine ⟨∫ ω, trimmedThirdScore β d R z η D ω ∂law, ?_,
      integral_trimmedThirdScore_le_firstThreeScore hd hR' hη D⟩
    simp_rw [hThird hz hR D _ hη]
    exact tendsto_integral_trimmedSmallThirdTest D ht

end Certificate.Overlap

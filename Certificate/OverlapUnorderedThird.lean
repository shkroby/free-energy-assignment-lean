import Certificate.OverlapUnorderedBP
import Certificate.OverlapThirdRational

/-! The measurable third occupation on unordered trees agrees with the
existing finite order statistic, counting distinct edge coordinates. -/

open Finset Set
open scoped BigOperators

namespace Certificate.UnorderedTree

open Overlap

theorem countRootOccupationsGE_node {k n : ℕ} (D : ℕ) (β z : ℝ) (s : ℕ) (q : ℝ)
    (x : Fin n → ℝ × Depth k) :
    countRootOccupationsGE D β z k s q (node n x) =
      ((Finset.univ : Finset (Fin n)).filter (fun i => q ≤ rootChildOccupation D β z k s (node n x) (x i))).card := by
  classical
  rw [countRootOccupationsGE, countChildrenWhere, sumChildren_node, ← Finset.sum_filter]
  simp

/-- The rational threshold construction and the finite third-largest
statistic give exactly the same value for a child vector. -/
theorem rootThird_node {k n : ℕ} (D : ℕ) (β z : ℝ) (s : ℕ)
    (x : Fin n → ℝ × Depth k)
    (hOcc : ∀ i, rootChildOccupation D β z k s (node n x) (x i) ∈ Set.Icc (0:ℝ) 1) :
    rootThird D β z k s (node n x) =
      thirdOccupation Finset.univ (fun i => rootChildOccupation D β z k s (node n x) (x i)) := by
  have hr := rationalThird_eq_thirdOccupation (Finset.univ : Finset (Fin n))
    (fun i => rootChildOccupation D β z k s (node n x) (x i)) (fun i _ => (hOcc i).2)
  unfold rationalThird at hr
  simpa only [rootThird, countRootOccupationsGE_node] using hr

end Certificate.UnorderedTree

import Certificate.LocalExplorationSize
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! Uniform size control of the finite cutoff neighborhood. -/

open Filter MeasureTheory Set
open scoped ENNReal BigOperators

namespace Certificate.LocalExploration

private abbrev BallPaths {n : ℕ} (root : Fin n ⊕ Fin n) (radius : ℕ) :=
  Σ k : Fin (radius + 1), RootedSimplePath root k.val

private def pathEndpoint {n k : ℕ} {root : Fin n ⊕ Fin n}
    (p : RootedSimplePath root k) : Fin n ⊕ Fin n :=
  Fin.cons (α := fun _ ↦ Fin n ⊕ Fin n) root p.val (Fin.last k)

private noncomputable def retainedBallPaths {n : ℕ} (root : Fin n ⊕ Fin n)
    (radius : ℕ) (A : Set ℝ) (C : CostArray) : Finset (BallPaths root radius) := by
  classical
  exact Finset.univ.filter (fun p ↦ C ∈ retainedPathEvent (rootedSimplePathEntries p.2) A)

/-- The vertices reached from the root by retained simple paths of length
at most the fixed radius. -/
noncomputable def cutoffBall {n : ℕ} (root : Fin n ⊕ Fin n) (radius : ℕ)
    (A : Set ℝ) (C : CostArray) : Finset (Fin n ⊕ Fin n) :=
  (retainedBallPaths root radius A C).image (fun p ↦ pathEndpoint p.2)

private noncomputable def allShortPathCount {n : ℕ} (root : Fin n ⊕ Fin n)
    (radius : ℕ) (A : Set ℝ) (C : CostArray) : ℝ :=
  ∑ j : Fin (radius + 1), retainedPathFamilyCount (rootedSimplePathEntries (root := root) (k := j.val)) A C

private theorem card_cutoffBall_le {n : ℕ} (root : Fin n ⊕ Fin n)
    (radius : ℕ) (A : Set ℝ) (C : CostArray) :
    ((cutoffBall root radius A C).card : ℝ) ≤ allShortPathCount root radius A C := by
  classical
  have h := Finset.card_image_le (s := retainedBallPaths root radius A C)
    (f := fun p ↦ pathEndpoint p.2)
  apply (show ((cutoffBall root radius A C).card : ℝ) ≤
    (retainedBallPaths root radius A C).card from Nat.cast_le.mpr h).trans_eq
  unfold retainedBallPaths allShortPathCount retainedPathFamilyCount
  rw [Finset.card_filter]
  push_cast
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro p _
  by_cases hC : C ∈ retainedPathEvent (rootedSimplePathEntries p) A <;> simp [hC]

/-- At a fixed cutoff and radius, the probability of more than a given
number of visible vertices is bounded by a constant divided by that number,
uniformly over all roots and large graph sizes. -/
theorem eventually_measure_cutoffBall_card_ge_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {d κ R : ℝ} (hd : 0 < d) (hκ : 0 < κ) (hR : 0 < R) (h : SmallCostTail μ κ d)
    (radius : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ root : Fin n ⊕ Fin n, ∀ J : ℝ, 0 < J →
      iidCosts μ {C | J ≤ ((cutoffBall root radius (Iic (R / lengthScale d κ n)) C).card : ℝ)} ≤
        ENNReal.ofReal (∑ k : Fin (radius + 1), (2 * (R ^ d + 1)) ^ k.val) / ENNReal.ofReal J := by
  have hAll :
      ∀ᶠ n : ℕ in atTop, ∀ k : Fin (radius + 1), ∀ root : Fin n ⊕ Fin n,
        (∫ C, retainedPathFamilyCount (rootedSimplePathEntries (root := root) (k := k.val))
          (Iic (R / lengthScale d κ n)) C ∂iidCosts μ) ≤ (2 * (R ^ d + 1)) ^ k.val :=
    Filter.eventually_all.mpr (fun k ↦ eventually_integral_short_rootedSimplePathCount_le hd hκ hR h k.val)
  filter_upwards [hAll] with n hBound
  intro root J hJ
  let P := iidCosts μ
  let : IsProbabilityMeasure P := by unfold P iidCosts; infer_instance
  let A := Iic (R / lengthScale d κ n)
  let B := allShortPathCount root radius A
  have hA : MeasurableSet A := measurableSet_Iic
  have hInt (k : Fin (radius + 1)) :
      Integrable (retainedPathFamilyCount (rootedSimplePathEntries (root := root) (k := k.val)) A) P := by
    unfold retainedPathFamilyCount
    exact integrable_finsetSum _ fun p _ ↦
      (integrable_const (1 : ℝ)).indicator (measurableSet_retainedPathEvent (rootedSimplePathEntries p) hA)
  have hB : Integrable B P := integrable_finsetSum _ fun k _ ↦ hInt k
  have hNonneg (C : CostArray) : 0 ≤ B C := by
    unfold B allShortPathCount retainedPathFamilyCount
    exact Finset.sum_nonneg fun j _ ↦ Finset.sum_nonneg fun p _ ↦
      indicator_nonneg (fun _ _ ↦ zero_le_one) _
  have hM := meas_ge_le_lintegral_div (μ := P) hB.aemeasurable.ennreal_ofReal
    (ENNReal.ofReal_pos.mpr hJ).ne' ENNReal.ofReal_ne_top
  rw [← ofReal_integral_eq_lintegral_ofReal hB (.of_forall hNonneg)] at hM
  have hSum : (∫ C, B C ∂P) ≤ ∑ k : Fin (radius + 1), (2 * (R ^ d + 1)) ^ k.val := by
    unfold B allShortPathCount
    rw [integral_finsetSum _ (fun k _ ↦ hInt k)]
    exact Finset.sum_le_sum fun k _ ↦ hBound k root
  refine (measure_mono ?_).trans (hM.trans ?_)
  · intro C hC
    exact ENNReal.ofReal_le_ofReal ((mem_ofPred_eq.mp hC).trans (card_cutoffBall_le root radius A C))
  · gcongr

end Certificate.LocalExploration

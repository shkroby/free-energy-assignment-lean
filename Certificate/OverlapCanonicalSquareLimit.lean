import Certificate.OverlapCanonicalTrim

/-! The squared occupation sum is stable under the degree and length cutoffs. -/

open Filter MeasureTheory Set
open scoped Topology

namespace Certificate.CanonicalTree

private theorem tendsto_tsum_sq_of_pointwise_le {p : ℕ → ℕ → ℝ} {q a : ℕ → ℝ}
    (ha : Summable a) (ha₀ : ∀ i, 0 ≤ a i)
    (hp : ∀ n i, 0 ≤ p n i ∧ p n i ≤ a i)
    (ht : ∀ i, Tendsto (fun n => p n i) atTop (𝓝 (q i))) :
    Tendsto (fun n => ∑' i, (p n i)^2) atTop (𝓝 (∑' i, (q i)^2)) := by
  apply tendsto_tsum_of_dominated_convergence (ha.mul_right (∑' i, a i))
  · exact fun i => (ht i).pow 2
  · refine Eventually.of_forall fun n i => ?_
    rw [Real.norm_of_nonneg (sq_nonneg _), sq]
    exact mul_le_mul (hp n i).2 ((hp n i).2.trans (ha.le_tsum i (fun j _ => ha₀ j)))
      (hp n i).1 (ha₀ i)

private theorem rootOccupation_nonneg_le {z x a b : ℝ} (hz : 0 < z) (hx : 0 ≤ x)
    (ha : a ∈ Icc 0 z⁻¹) (hb : b ∈ Icc 0 z⁻¹) : 0 ≤ x*a*b ∧ x*a*b ≤ x*z⁻¹*z⁻¹ := by
  exact ⟨mul_nonneg (mul_nonneg hx ha.1) hb.1,
    mul_le_mul (mul_le_mul_of_nonneg_left ha.2 hx) hb.2 hb.1
      (mul_nonneg hx (inv_nonneg.mpr hz.le))⟩

/-- Degree-cutoff removal preserves the squared occupation sum almost surely. -/
theorem ae_tendsto_trimmed_squareSum {β d z : ℝ} (hβ : 0 < β) (hd : 0 < d) (hz : 0 < z) (R : ℕ) :
    ∀ᵐ ω ∂law, Tendsto (fun D => ∑' i, (trimmedRootOccupation β d R z D ω i)^2) atTop
      (𝓝 (∑' i, (cutoffRootOccupation β d R z ω i)^2)) := by
  let K := cutoffKernel β R
  filter_upwards [ae_summable_weightFor (ae_summable_cutoffKernel hβ hd R),
    ae_tendsto_trimmed_occupations hβ hd hz R] with ω hw ht
  have hdom : Summable (fun i => weightFor K d ω [] i * z⁻¹ * z⁻¹) :=
    ((hw []).mul_right z⁻¹).mul_right z⁻¹
  refine tendsto_tsum_sq_of_pointwise_le hdom (fun i => ?_) (fun D i => ?_) ht
  · exact mul_nonneg (mul_nonneg (cutoffKernel_nonneg _ _ _) (inv_nonneg.mpr hz.le)) (inv_nonneg.mpr hz.le)
  · have h (v : Vertex) : trimmedLower β d R z D v ω ∈ Icc 0 z⁻¹ ∧
        trimmedUpper β d R z D v ω ∈ Icc 0 z⁻¹ := by
      have h := trimmedDepth_brackets hz hw D 0 v
      exact ⟨⟨h.1,h.2.1.trans h.2.2⟩,⟨h.1.trans h.2.1,h.2.2⟩⟩
    have hW := trimmedWeight_bounds β d R D ω [] i
    have hP := rootOccupation_nonneg_le hz hW.1 (h []).2 (h (child [] i)).1
    exact ⟨hP.1, hP.2.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hW.2 (inv_nonneg.mpr hz.le)) (inv_nonneg.mpr hz.le))⟩

/-- Length-cutoff removal preserves the squared occupation sum almost surely. -/
theorem ae_tendsto_cutoff_squareSum {β d z : ℝ} (hβ : 0 < β) (hd : 0 < d) (hz : 0 < z) :
    ∀ᵐ ω ∂law, Tendsto (fun R : ℕ => ∑' i, (cutoffRootOccupation β d R z ω i)^2) atTop
      (𝓝 (∑' i, (fullRootOccupation β d z ω i)^2)) := by
  have hbounds : ∀ᵐ ω ∂law, ∀ (R : ℕ) (v : Vertex),
      lowerFor (cutoffKernel β R) d z v ω ∈ Icc 0 z⁻¹ := by
    apply ae_all_iff.mpr
    intro R
    filter_upwards [ae_boundary_limitsFor hz (cutoffKernel_nonneg β R)
      (ae_summable_cutoffKernel hβ hd R)] with ω h v
    exact ⟨(h v).2.2.1.le, (h v).2.2.2.1.trans (h v).2.2.2.2.1⟩
  filter_upwards [ae_summable_weight hβ hd, hbounds,
    ae_tendsto_cutoff_occupations hβ hd hz] with ω hw hb ht
  have hdom : Summable (fun i => weight β d ω [] i * z⁻¹ * z⁻¹) :=
    ((hw []).mul_right z⁻¹).mul_right z⁻¹
  refine tendsto_tsum_sq_of_pointwise_le hdom (fun i => ?_) (fun R i => ?_) ht
  · exact mul_nonneg (mul_nonneg (weight_nonneg β d ω [] i) (inv_nonneg.mpr hz.le)) (inv_nonneg.mpr hz.le)
  · let K := cutoffKernel β R
    have hW : weightFor K d ω [] i ≤ weight β d ω [] i := by
      unfold K weightFor cutoffKernel
      split
      · exact le_rfl
      · exact weight_nonneg β d ω [] i
    have hP := rootOccupation_nonneg_le hz (cutoffKernel_nonneg β R (arrivalLength d (ω []) i))
      (hb R []) (hb R (child [] i))
    exact ⟨hP.1, hP.2.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hW (inv_nonneg.mpr hz.le)) (inv_nonneg.mpr hz.le))⟩

end Certificate.CanonicalTree

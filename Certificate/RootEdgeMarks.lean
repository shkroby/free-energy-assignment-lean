import Certificate.ShortEdges
import Certificate.Intensity
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Conditional lengths of retained edges

At a fixed cutoff the probability of a retained edge is of order `1/n`.
Conditional on retention, its length has the normalized truncated law.
The CDF converges at each interior point to that of the restricted intensity.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

namespace Certificate

theorem cdf_pos_of_smallCostTail {μ : Measure ℝ} {d κ : ℝ}
    (hκ : 0 < κ) (h : SmallCostTail μ κ d) {x : ℝ} (hx : 0 < x) :
    0 < cdf μ x := by
  have hnear := (tendsto_order.mp h.2).1 (1 / 2) (by norm_num)
  obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hnear
  let s := min δ x / 2
  have hs : 0 < s := half_pos (lt_min hδ hx)
  have hsδ : s < δ := (half_lt_self (lt_min hδ hx)).trans_le (min_le_left ..)
  have hsx : s ≤ x := (half_lt_self (lt_min hδ hx)).le.trans (min_le_right ..)
  have hratio : 1 / 2 < cdf μ s / (κ * s ^ d) := hsub ⟨hs, hsδ⟩
  have hpos := (lt_div_iff₀ (mul_pos hκ (Real.rpow_pos_of_pos hs _))).mp hratio
  exact (by positivity : 0 < 1 / 2 * (κ * s ^ d)).trans_le (hpos.le.trans (monotone_cdf μ hsx))

/-- Law of one scaled edge length. -/
noncomputable def scaledLengthLaw (μ : Measure ℝ) (d κ : ℝ) (n : ℕ) : Measure ℝ :=
  μ.map fun c ↦ lengthScale d κ n * c

theorem scaledLengthLaw_Iic {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {d κ : ℝ} (hκ : 0 < κ) {n : ℕ} (hn : 0 < n) (x : ℝ) :
    scaledLengthLaw μ d κ n (Iic x) =
      ENNReal.ofReal (shortEdgeProbability μ d κ x n) := by
  have hs : 0 < lengthScale d κ n :=
    Real.rpow_pos_of_pos (mul_pos hκ (Nat.cast_pos.mpr hn)) _
  unfold scaledLengthLaw shortEdgeProbability
  rw [Measure.map_apply (by fun_prop) measurableSet_Iic, ofReal_cdf]
  congr 1
  ext c
  change lengthScale d κ n * c ≤ x ↔ c ≤ x / lengthScale d κ n
  rw [le_div_iff₀ hs, mul_comm]

/-- The scaled length conditional on being at most `R`. -/
noncomputable def retainedLengthLaw (μ : Measure ℝ) (d κ R : ℝ) (n : ℕ) : Measure ℝ :=
  let ν := scaledLengthLaw μ d κ n
  (ν (Iic R))⁻¹ • ν.restrict (Iic R)

theorem retainedLengthLaw_isProbabilityMeasure {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {d κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R) (h : SmallCostTail μ κ d)
    {n : ℕ} (hn : 0 < n) :
    IsProbabilityMeasure (retainedLengthLaw μ d κ R n) where
  measure_univ := by
    have hscale : 0 < lengthScale d κ n :=
      Real.rpow_pos_of_pos (mul_pos hκ (Nat.cast_pos.mpr hn)) _
    have hpos : 0 < shortEdgeProbability μ d κ R n :=
      cdf_pos_of_smallCostTail hκ h (div_pos hR hscale)
    rw [retainedLengthLaw, Measure.smul_apply, Measure.restrict_apply_univ, scaledLengthLaw_Iic hκ hn]
    exact ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr hpos) ENNReal.ofReal_ne_top

/-- Pointwise convergence of the conditional length CDF in the open
truncation window, with the limit expressed in the cumulative intensity. -/
theorem tendsto_retainedLengthLaw_Iic {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {d κ R x : ℝ} (hd : 0 < d) (hκ : 0 < κ) (hx : 0 < x) (hxR : x ≤ R)
    (h : SmallCostTail μ κ d) :
    Tendsto (fun n : ℕ ↦ (retainedLengthLaw μ d κ R n (Iic x)).toReal) atTop
      (𝓝 ((x / R) ^ d)) := by
  have hR := hx.trans_le hxR
  have hconv := (tendsto_scaled_shortEdgeProbability hd hκ hx h).div
    (tendsto_scaled_shortEdgeProbability hd hκ hR h) (Real.rpow_pos_of_pos hR d).ne'
  rw [← Real.div_rpow hx.le hR.le] at hconv
  refine hconv.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  change ((n : ℝ) * shortEdgeProbability μ d κ x n) /
      ((n : ℝ) * shortEdgeProbability μ d κ R n) = _
  rw [retainedLengthLaw, Measure.smul_apply, Measure.restrict_apply measurableSet_Iic,
    Set.inter_eq_left.mpr (Iic_subset_Iic.mpr hxR),
    scaledLengthLaw_Iic hκ hn, scaledLengthLaw_Iic hκ hn, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (show 0 ≤ shortEdgeProbability μ d κ R n from cdf_nonneg μ _),
    ENNReal.toReal_ofReal (show 0 ≤ shortEdgeProbability μ d κ x n from cdf_nonneg μ _)]
  rw [mul_div_mul_left _ _ (Nat.cast_pos.mpr hn).ne', div_eq_mul_inv, mul_comm]

end Certificate

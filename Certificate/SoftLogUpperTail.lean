import Certificate.SoftMedianBound
import Certificate.SoftMedianExistence

/-! The common stretched upper logarithmic tail for bounded soft fixed points. -/

open MeasureTheory Set
open scoped ENNReal

namespace Certificate

theorem soft_cavity_law_positive {β d z : ℝ} (hz : 0 < z)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hLaw : (markedSpacings μ).map (arrivalSoftOutput β d z) = μ) :
    μ (Ioi 0) = 1 := by
  let : IsProbabilityMeasure (markedSpacings μ) := isProbabilityMeasure_markedArrivalSequenceLaw μ
  rw [← hLaw, Measure.map_apply (measurable_arrivalSoftOutput ..) measurableSet_Ioi]
  have he : arrivalSoftOutput β d z ⁻¹' Ioi 0 = univ := by
    ext ω
    have h : 0 < arrivalSoftOutput β d z ω := by
      unfold arrivalSoftOutput
      exact inv_pos.mpr (add_pos_of_pos_of_nonneg hz ENNReal.toReal_nonneg)
    simp [h]
  rw [he, measure_univ]

/-- For fixed positive temperature and pseudo-dimension, every positive
soft cavity law with fugacity at most one has the same stretched upper-tail
envelope, in the parametrization used for the outgoing series. -/
theorem exists_uniform_soft_cavity_log_upperTail {β d : ℝ} (hβ : 0 < β) (hd : 0 < d) :
    ∃ K : ℝ, 0 < K ∧
      ∀ z : ℝ, 0 < z → z ≤ 1 → ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
        (∀ᵐ h ∂μ, h ∈ Icc 0 z⁻¹) →
        (markedSpacings μ).map (arrivalSoftOutput β d z) = μ →
        ∀ x ≥ 0, μ (Ioi (Real.exp (β * x / 2))) ≤
          ENNReal.ofReal (K * Real.exp (-((2 * (4 : ℝ) ^ d)⁻¹ * x ^ d))) := by
  obtain ⟨B, hB, hb⟩ := exists_uniform_soft_log_median_lower_bound hβ hd
  let c := (2 * (4 : ℝ) ^ d)⁻¹
  let K := Real.exp (c * (4 * B) ^ d)
  have hc : 0 < c := by dsimp [c]; positivity
  have hK : 0 < K := Real.exp_pos _
  refine ⟨K, hK, fun z hz hz₁ μ _ hμ hLaw x hx ↦ ?_⟩
  obtain ⟨b, hL, hU⟩ := exists_logMessage_median hβ μ (soft_cavity_law_positive hz μ hLaw)
  have hblo := hb z hz hz₁ μ hμ hLaw b hL hU
  have hK₁ : 1 ≤ K := Real.one_le_exp (mul_nonneg hc.le (Real.rpow_nonneg (by positivity) _))
  by_cases hxB : 4 * B ≤ x
  · have hfin : ∀ᵐ ω ∂markedSpacings μ, arrivalWeightedSum β d ω ≠ ∞ := by
      filter_upwards [ae_arrivalWeightedSum_eq_ofReal_tsum hd hβ μ hμ] with ω hω
      rw [hω]
      exact ENNReal.ofReal_ne_top
    have H := arrival_log_upperTail_of_median_lower_bound hd hβ hz.le hB μ hfin hLaw
      hU hblo (show 2 * B ≤ x / 2 by linarith)
    have he : Real.exp (-(((x / 2) / 2) ^ d / 2)) = Real.exp (-(c * x ^ d)) := by
      rw [show x / 2 / 2 = x / 4 by ring, Real.div_rpow hx (by norm_num) d]
      congr 1
      unfold c
      ring
    rw [show β * (x / 2) = β * x / 2 by ring, he] at H
    apply H.trans
    apply ENNReal.ofReal_le_ofReal
    exact le_mul_of_one_le_left (Real.exp_nonneg _) hK₁
  · have hx' : x ^ d ≤ (4 * B) ^ d := Real.rpow_le_rpow hx (le_of_not_ge hxB) hd.le
    have hE : 1 ≤ K * Real.exp (-(c * x ^ d)) := by
      unfold K
      rw [← Real.exp_add]
      apply Real.one_le_exp
      linarith only [mul_le_mul_of_nonneg_left hx' hc.le]
    exact prob_le_one.trans (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hE)

/-- The same envelope written in the scale of `β⁻¹ log H`. -/
theorem exists_uniform_soft_log_tail {β d : ℝ} (hβ : 0 < β) (hd : 0 < d) :
    ∃ K : ℝ, 0 < K ∧
      ∀ z : ℝ, 0 < z → z ≤ 1 → ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
        (∀ᵐ h ∂μ, h ∈ Icc 0 z⁻¹) →
        (markedSpacings μ).map (arrivalSoftOutput β d z) = μ →
        ∀ t ≥ 0, μ (Ioi (Real.exp (β * t))) ≤
          ENNReal.ofReal (K * Real.exp (-((t / 2) ^ d / 2))) := by
  obtain ⟨K, hK, hTail⟩ := exists_uniform_soft_cavity_log_upperTail hβ hd
  refine ⟨K, hK, fun z hz hz₁ μ _ hm hl t ht ↦ ?_⟩
  have H := hTail z hz hz₁ μ hm hl (2 * t) (by positivity)
  rw [show β * (2 * t) / 2 = β * t by ring] at H
  refine H.trans_eq ?_
  congr 3
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) ht,
    Real.div_rpow ht (by norm_num) d, show (4 : ℝ) = 2 * 2 by norm_num,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 2)]
  have h₂ : (2 : ℝ) ^ d ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
  field_simp [h₂]

end Certificate

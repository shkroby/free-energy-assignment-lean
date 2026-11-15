import Certificate.ArrivalMedianTail
import Certificate.ArrivalTruncation
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Uniform upper tightness of the positive-fugacity message laws. -/

open Filter MeasureTheory Set
open scoped ENNReal

namespace Certificate

/-- The occupation-mass bound yields a quantitative upper log-message tail for
every positive-fugacity solution. -/
theorem soft_cavity_log_upperTail_le {d β z s : ℝ} (hd : 0 < d) (hβ : 0 < β)
    (hz : 0 < z) (hs : 0 < s) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc 0 z⁻¹)
    (hLaw : (markedSpacings μ).map (arrivalSoftOutput β d z) = μ) :
    μ (Ioi (Real.exp (β * s))) ≤ ENNReal.ofReal (Real.sqrt (2 / (2 * s) ^ d)) := by
  let A := Ioi (Real.exp (β * s))
  have hA : μ A ≠ ∞ := measure_ne_top μ A
  have hpos : 0 < (2 * s) ^ d := Real.rpow_pos_of_pos (by positivity) d
  have hp := logMessage_upperTail_sq_bound hβ hd hs μ
    (expectedOccupationMass_le_one_of_soft_cavity_law hd hβ hz μ hμ hLaw)
  change ENNReal.ofReal ((2 * s) ^ d / 2) * (μ A) ^ 2 ≤ 1 at hp
  rw [← ENNReal.ofReal_toReal hA, ← ENNReal.ofReal_pow ENNReal.toReal_nonneg,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_one] at hp
  have hp' := (ENNReal.ofReal_le_ofReal_iff zero_le_one).mp hp
  change μ A ≤ _
  rw [← ENNReal.ofReal_toReal hA]
  apply ENNReal.ofReal_le_ofReal
  apply (Real.le_sqrt ENNReal.toReal_nonneg (by positivity)).mpr
  apply (le_div_iff₀ hpos).mpr
  nlinarith

/-- A single cutoff works for both the mark tail and the expected number of
above-cutoff marks in a fixed arrival window, for every positive fugacity. -/
theorem exists_uniform_soft_cavity_log_upperTail_window {d β R η : ℝ}
    (hd : 0 < d) (hβ : 0 < β) (hR : 0 ≤ R) (hη : 0 < η) :
    ∃ S > 0, ∀ s ≥ S, ∀ (z : ℝ), 0 < z →
      ∀ (μ : Measure ℝ), ∀ (_ : IsProbabilityMeasure μ),
        (∀ᵐ x ∂μ, x ∈ Icc 0 z⁻¹) →
        (markedSpacings μ).map (arrivalSoftOutput β d z) = μ →
        μ (Ioi (Real.exp (β * s))) ≤ ENNReal.ofReal η ∧
        ENNReal.ofReal (R ^ d) * μ (Ioi (Real.exp (β * s))) ≤ ENNReal.ofReal η := by
  let c : ℝ := max 1 (R ^ d)
  let a : ℝ := η / c
  have hR' : 0 ≤ R ^ d := Real.rpow_nonneg hR d
  have hc₁ : 1 ≤ c := le_max_left _ _
  have hc : 0 < c := zero_lt_one.trans_le hc₁
  have ha : 0 < a := div_pos hη hc
  have hac : c * a = η := by
    rw [mul_comm]
    exact div_mul_cancel₀ _ hc.ne'
  obtain ⟨N, hN⟩ := tendsto_atTop_atTop.mp (tendsto_rpow_atTop hd) (2 / a ^ 2)
  refine ⟨max 1 N, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro s hs z hz μ hprob hμ hLaw
  have hs₁ : 1 ≤ s := (le_max_left 1 N).trans hs
  have hs₀ : 0 < s := zero_lt_one.trans_le hs₁
  have hsize : 2 / a ^ 2 ≤ (2 * s) ^ d := hN _ (by linarith [(le_max_right 1 N).trans hs])
  have hratio : 2 / (2 * s) ^ d ≤ a ^ 2 := by
    apply (div_le_iff₀ (Real.rpow_pos_of_pos (by positivity) _)).mpr
    rw [mul_comm]
    exact (div_le_iff₀ (by positivity : 0 < a ^ 2)).mp hsize
  have hsqrt : Real.sqrt (2 / (2 * s) ^ d) ≤ a := Real.sqrt_le_iff.mpr ⟨ha.le, hratio⟩
  have htail := (soft_cavity_log_upperTail_le hd hβ hz hs₀ μ hμ hLaw).trans
    (ENNReal.ofReal_le_ofReal hsqrt)
  constructor
  · apply htail.trans
    apply ENNReal.ofReal_le_ofReal
    rw [← hac]
    exact le_mul_of_one_le_left ha.le hc₁
  · calc
      _ ≤ ENNReal.ofReal (R ^ d) * ENNReal.ofReal a := by gcongr
      _ = ENNReal.ofReal (R ^ d * a) := (ENNReal.ofReal_mul hR').symm
      _ ≤ ENNReal.ofReal (c * a) := by
        gcongr
        exact le_max_right 1 (R ^ d)
      _ = ENNReal.ofReal η := by rw [hac]

/-- For the same uniform cutoff, the probability of even one above-cutoff
mark among the canonical arrivals of length at most `R` is at most `η`. -/
theorem exists_uniform_soft_cavity_window_hit_le {d β R η : ℝ}
    (hd : 0 < d) (hβ : 0 < β) (hR : 0 ≤ R) (hη : 0 < η) :
    ∃ S > 0, ∀ s ≥ S, ∀ (z : ℝ), 0 < z →
      ∀ (μ : Measure ℝ), ∀ (_ : IsProbabilityMeasure μ),
        (∀ᵐ x ∂μ, x ∈ Icc 0 z⁻¹) →
        (markedSpacings μ).map (arrivalSoftOutput β d z) = μ →
        markedSpacings μ {ω | ∃ i,
          (arrivalLength d ω.1 i, ω.2 i) ∈ Ioc 0 R ×ˢ Ioi (Real.exp (β * s))} ≤
          ENNReal.ofReal η := by
  obtain ⟨S, hS, hbound⟩ := exists_uniform_soft_cavity_log_upperTail_window hd hβ hR hη
  refine ⟨S, hS, ?_⟩
  intro s hs z hz μ hprob hμ hLaw
  have hhit := measure_arrival_hit_le hd μ
    (s := Ioc 0 R ×ˢ Ioi (Real.exp (β * s))) (measurableSet_Ioc.prod measurableSet_Ioi)
  rw [Measure.prod_prod, intensity_Ioc_zero hd hR] at hhit
  exact hhit.trans (hbound s hs z hz μ hprob hμ hLaw).2

end Certificate

import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Second moments from power tails

The bound is the layer-cake calculation for a variable whose tail above one
is bounded by the tail of a Pareto variable of parameter `a > 2`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Certificate

private theorem lintegral_unitInterval_id :
    ∫⁻ t : ℝ in Ioc 0 1, ENNReal.ofReal t = ENNReal.ofReal (1 / 2) := by
  have hInt : IntegrableOn (fun t : ℝ ↦ t) (Ioc 0 1) :=
    (continuous_id.intervalIntegrable 0 1).1
  have hNN : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] (fun t : ℝ ↦ t) := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with t ht using ht.1.le
  rw [← ofReal_integral_eq_lintegral_ofReal hInt hNN, ← intervalIntegral.integral_of_le zero_le_one]
  rw [integral_id]
  norm_num

private theorem lintegral_power_tail {a : ℝ} (ha : 2 < a) :
    ∫⁻ t : ℝ in Ioi 1, ENNReal.ofReal (t ^ (1 - a)) = ENNReal.ofReal (1 / (a - 2)) := by
  have hInt : IntegrableOn (fun t : ℝ ↦ t ^ (1 - a)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have hNN : 0 ≤ᵐ[volume.restrict (Ioi (1 : ℝ))] (fun t : ℝ ↦ t ^ (1 - a)) := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
    exact Real.rpow_nonneg (zero_le_one.trans ht.le) _
  rw [← ofReal_integral_eq_lintegral_ofReal hInt hNN,
    integral_Ioi_rpow_of_lt (by linarith) zero_lt_one, Real.one_rpow]
  congr 1
  have h : 1 - a + 1 = -(a - 2) := by ring
  rw [h, div_neg, neg_div, neg_neg]

/-- Integrating the strict upper-tail bound gives an explicit second-moment bound. -/
theorem lintegral_sq_le_of_power_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {f : Ω → ℝ} {a : ℝ}
    (hf : Measurable f) (hNN : 0 ≤ᵐ[μ] f) (ha : 2 < a)
    (hTail : ∀ t > 1, μ {ω | t < f ω} ≤ ENNReal.ofReal (t ^ (-a))) :
    (∫⁻ ω, ENNReal.ofReal (f ω ^ (2 : ℕ)) ∂μ) ≤ ENNReal.ofReal (a / (a - 2)) := by
  have hsplit : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := by
    ext t
    simp only [mem_Ioi, mem_union, mem_Ioc]
    constructor
    · intro ht
      rcases le_or_gt t 1 with h | h
      · exact Or.inl ⟨ht, h⟩
      · exact Or.inr h
    · rintro (⟨h, _⟩ | h)
      · exact h
      · linarith
  have hdisj : Disjoint (Ioc (0 : ℝ) 1) (Ioi 1) :=
    Set.disjoint_left.mpr (fun _ h₁ h₂ ↦ not_lt_of_ge h₁.2 h₂)
  have hshort :
      (∫⁻ t : ℝ in Ioc 0 1, μ {ω | t < f ω} * ENNReal.ofReal t) ≤ ENNReal.ofReal (1 / 2) := by
    rw [← lintegral_unitInterval_id]
    apply lintegral_mono
    intro t
    exact mul_le_of_le_one_left' (prob_le_one)
  have hlong :
      (∫⁻ t : ℝ in Ioi 1, μ {ω | t < f ω} * ENNReal.ofReal t) ≤ ENNReal.ofReal (1 / (a - 2)) := by
    rw [← lintegral_power_tail ha]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
    have hpos : 0 < t := zero_lt_one.trans ht
    calc
      _ ≤ ENNReal.ofReal (t ^ (-a)) * ENNReal.ofReal t := by gcongr; exact hTail t ht
      _ = _ := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hpos.le _)]
        have h : t ^ (1 - a) = t ^ (-a) * t := by
          rw [show 1 - a = -a + 1 by ring, Real.rpow_add hpos, Real.rpow_one]
        rw [h]
  have hc := lintegral_rpow_eq_lintegral_meas_lt_mul μ hNN hf.aemeasurable
    (show (0 : ℝ) < 2 by norm_num)
  norm_num [Real.rpow_natCast] at hc
  rw [hc, hsplit, lintegral_union measurableSet_Ioi hdisj]
  calc
    _ ≤ ENNReal.ofReal 2 * (ENNReal.ofReal (1 / 2) + ENNReal.ofReal (1 / (a - 2))) :=
      by rw [ENNReal.ofReal_ofNat]; gcongr
    _ = _ := by
      have hden : 0 < a - 2 := sub_pos.mpr ha
      rw [← ENNReal.ofReal_add (by norm_num) (by positivity),
        ← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      field_simp
      ring

/-- The same estimate in the L² seminorm used by the uniform integrability step. -/
theorem eLpNorm_two_le_of_power_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {f : Ω → ℝ} {a : ℝ}
    (hf : Measurable f) (hNN : 0 ≤ᵐ[μ] f) (ha : 2 < a)
    (hTail : ∀ t > 1, μ {ω | t < f ω} ≤ ENNReal.ofReal (t ^ (-a))) :
    eLpNorm f 2 μ ≤ ENNReal.ofReal ((a / (a - 2)) ^ (1 / 2 : ℝ)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := (2 : ℝ≥0∞)) (by norm_num) (by simp)]
  norm_num only [ENNReal.toReal_ofNat]
  rw [← ENNReal.ofReal_rpow_of_nonneg (by positivity : 0 ≤ a / (a - 2)) (by norm_num)]
  apply ENNReal.rpow_le_rpow _ (by norm_num)
  refine (le_of_eq ?_).trans (lintegral_sq_le_of_power_tail μ hf hNN ha hTail)
  apply lintegral_congr_ae
  filter_upwards [hNN] with ω hω
  change ‖f ω‖ₑ ^ (2 : ℝ) = _
  rw [ENNReal.rpow_two, Real.enorm_of_nonneg hω, ENNReal.ofReal_pow hω]

end Certificate

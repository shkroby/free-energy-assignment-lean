import Certificate.HardLogLowerTail
import Certificate.CavityTightness
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! A fugacity-uniform lower logarithmic tail and compactness of soft log laws. -/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace Certificate

/-- A common stretched upper mark tail for the child laws gives a common
lower log-message tail for all soft cavity laws with fugacity at most one.
The constants are independent of the law and the fugacity. -/
theorem exists_uniform_soft_cavity_log_lowerTail {β d K : ℝ} (hd : 0 < d) (hβ : 0 < β)
    (hK : 0 ≤ K) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
      ∀ (z : ℝ), 0 < z → z ≤ 1 → ∀ (μ : Measure ℝ), ∀ (_ : IsProbabilityMeasure μ),
        (∀ᵐ x ∂μ, x ∈ Icc 0 z⁻¹) →
        (markedSpacings μ).map (arrivalSoftOutput β d z) = μ →
        (∀ t : ℝ, 0 ≤ t → μ (Ioi (Real.exp (β*t))) ≤
          ENNReal.ofReal (K * Real.exp (-((t/2)^d/2)))) →
        ∀ t : ℝ, Real.log 2 / β ≤ t →
          μ (Iio (Real.exp (-β*t))) ≤
            ENNReal.ofReal (C₁ * Real.exp (-((t/4)^d/4)) + C₂ * Real.exp (-(β*t/2))) := by
  let I := ∫⁻ x, ENNReal.ofReal (Real.exp (-((x/4)^d/4))) ∂intensity d
  let J := ∫⁻ x, ENNReal.ofReal (Real.exp (-((β/2)*x))) ∂intensity d
  let C₁ := K * I.toReal
  let C₂ := 2 * J.toReal
  have h₁ : 0 ≤ C₁ := mul_nonneg hK ENNReal.toReal_nonneg
  have h₂ : 0 ≤ C₂ := mul_nonneg (by norm_num) ENNReal.toReal_nonneg
  refine ⟨C₁, C₂, h₁, h₂, ?_⟩
  intro z hz hz₁ μ hprob hm hLaw hUpper t ht
  have ht₀ : 0 ≤ t := (div_nonneg (Real.log_nonneg (by norm_num)) hβ.le).trans ht
  have he₂ : 2 ≤ Real.exp (β*t) := by
    rw [← Real.exp_log (by norm_num : (0:ℝ) < 2), Real.exp_le_exp]
    linarith [(div_le_iff₀ hβ).mp ht]
  have hzexp : z < Real.exp (β*t) := hz₁.trans_lt ((by norm_num : (1:ℝ) < 2).trans_le he₂)
  have hf : ∀ᵐ ω ∂markedSpacings μ, arrivalWeightedSum β d ω ≠ ∞ := by
    filter_upwards [ae_arrivalWeightedSum_eq_ofReal_tsum hd hβ μ hm] with ω hω
    rw [hω]
    exact ENNReal.ofReal_ne_top
  have hp : ∀ᵐ ω ∂markedSpacings μ, 0 < z + (arrivalWeightedSum β d ω).toReal :=
    Filter.Eventually.of_forall fun _ => add_pos_of_pos_of_nonneg hz ENNReal.toReal_nonneg
  have hL := arrival_log_lowerTail_bound hd μ hf hp hLaw hzexp
  have hE := arrival_log_exceptional_intensity_le hd hK μ hUpper t ht₀
  have hD : ENNReal.ofReal (Real.exp (β*t) / 2) ≤ ENNReal.ofReal (Real.exp (β*t) - z) :=
    ENNReal.ofReal_le_ofReal (by linarith)
  have hR := ENNReal.div_le_div_left hD
    (∫⁻ x, ENNReal.ofReal (Real.exp (β*(t-x)/2)) ∂intensity d)
  rw [arrival_lowerTail_remainder_eq hd hβ t (by norm_num : (0:ℝ) < 2)] at hR
  rw [ENNReal.ofReal_add (mul_nonneg h₁ (Real.exp_nonneg _)) (mul_nonneg h₂ (Real.exp_nonneg _))]
  exact hL.trans (add_le_add hE hR)

private theorem tendsto_stretched_logTail {d a b : ℝ}
    (hd : 0 < d) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun t : ℝ => Real.exp (-((t/a)^d/b))) atTop (𝓝 0) := by
  have hscale : Tendsto (fun t : ℝ => t/a) atTop atTop := tendsto_id.atTop_div_const ha
  exact Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (((tendsto_rpow_atTop hd).comp hscale).atTop_div_const hb)

private theorem measure_abs_log_tail_le {β : ℝ} (μ : Measure ℝ)
    (hμ : ∀ᵐ x ∂μ, 0 < x) (t : ℝ) :
    μ {x | β*t < |Real.log x|} ≤
      μ (Ioi (Real.exp (β*t))) + μ (Iio (Real.exp (-β*t))) := by
  refine (measure_mono_ae ?_).trans (measure_union_le _ _)
  filter_upwards [hμ] with x hx ht
  by_cases hlog : 0 ≤ Real.log x
  · change β*t < |Real.log x| at ht
    rw [abs_of_nonneg hlog] at ht
    exact Or.inl ((Real.lt_log_iff_exp_lt hx).mp ht)
  · change β*t < |Real.log x| at ht
    rw [abs_of_nonpos (le_of_not_ge hlog)] at ht
    exact Or.inr ((Real.log_lt_iff_lt_exp hx).mp (by linarith))

/-- Families of soft message laws with a common stretched upper log tail
have compact weak closure after taking logarithms. -/
theorem isCompact_closure_of_soft_cavity_log_laws {ι : Type*} {β d K : ℝ}
    (hd : 0 < d) (hβ : 0 < β) (hK : 0 ≤ K)
    (z : ι → ℝ) (ν : ι → ProbabilityMeasure ℝ)
    (hz : ∀ i, 0 < z i) (hz₁ : ∀ i, z i ≤ 1)
    (hμ : ∀ i, ∀ᵐ x ∂(ν i : Measure ℝ), x ∈ Ioc 0 (z i)⁻¹)
    (hLaw : ∀ i, (markedSpacings (ν i : Measure ℝ)).map (arrivalSoftOutput β d (z i)) =
      (ν i : Measure ℝ))
    (hUpper : ∀ i t, 0 ≤ t → (ν i : Measure ℝ) (Ioi (Real.exp (β*t))) ≤
      ENNReal.ofReal (K * Real.exp (-((t/2)^d/2)))) :
    IsCompact (closure (range (fun i => (ν i).map Real.measurable_log.aemeasurable))) := by
  obtain ⟨C₁, C₂, _, _, hLower⟩ := exists_uniform_soft_cavity_log_lowerTail hd hβ hK
  have h₁ := (tendsto_stretched_logTail hd (by norm_num : (0:ℝ) < 2)
    (by norm_num : (0:ℝ) < 2)).const_mul K
  have h₂ := (tendsto_stretched_logTail hd (by norm_num : (0:ℝ) < 4)
    (by norm_num : (0:ℝ) < 4)).const_mul C₁
  have h₃ : Tendsto (fun t : ℝ => Real.exp (-(β*t/2))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (((tendsto_const_mul_atTop_of_pos hβ).mpr tendsto_id).atTop_div_const
        (by norm_num : (0:ℝ) < 2))
  have hSum : Tendsto (fun t : ℝ =>
      ENNReal.ofReal (K * Real.exp (-((t/2)^d/2))) +
        ENNReal.ofReal (C₁ * Real.exp (-((t/4)^d/4)) + C₂ * Real.exp (-(β*t/2))))
      atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero, ENNReal.ofReal_zero] using
      (ENNReal.tendsto_ofReal h₁).add (ENNReal.tendsto_ofReal (h₂.add (h₃.const_mul C₂)))
  have hcomp := isCompact_closure_of_uniform_log_tail (range ν) (by
    intro ε hε
    obtain ⟨T, hT⟩ := eventually_atTop.mp (hSum.eventually (Iio_mem_nhds hε))
    let t := max (Real.log 2 / β) (max 0 T)
    have ht₀ : 0 ≤ t := (le_max_left 0 T).trans (le_max_right _ _)
    have ht₁ : Real.log 2 / β ≤ t := le_max_left _ _
    have htT : T ≤ t := (le_max_right 0 T).trans (le_max_right _ _)
    refine ⟨β*t, ?_⟩
    rintro _ ⟨i, rfl⟩
    have hp := (hμ i).mono (fun _ h => h.1)
    have hb : ∀ᵐ x ∂(ν i : Measure ℝ), x ∈ Icc 0 (z i)⁻¹ :=
      (hμ i).mono (fun _ h => ⟨h.1.le, h.2⟩)
    exact ((measure_abs_log_tail_le (ν i : Measure ℝ) hp t).trans
      (add_le_add (hUpper i t ht₀)
        (hLower (z i) (hz i) (hz₁ i) (ν i : Measure ℝ) inferInstance hb
          (hLaw i) (hUpper i) t ht₁))).trans (hT t htT).le)
  rw [Set.range_comp' (fun μ : ProbabilityMeasure ℝ => μ.map Real.measurable_log.aemeasurable) ν]
  exact hcomp

end Certificate

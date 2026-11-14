import Certificate.ArrivalTruncation

/-!
# The lower logarithmic tail from upper tails of child marks

A very small root output requires an unusually large denominator. Separate
off the children whose marks exceed the tilted exponential threshold.
-/

open Filter MeasureTheory Set
open scoped ENNReal

namespace Certificate

/-- Bound the lower logarithmic tail by the intensity of exceptional child
marks and the first moment of the exponentially weighted remaining lengths. -/
theorem arrival_log_lowerTail_bound {d β z t : ℝ} (hd : 0 < d)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hfin : ∀ᵐ ω ∂markedSpacings μ, arrivalWeightedSum β d ω ≠ ∞)
    (hpos : ∀ᵐ ω ∂markedSpacings μ, 0 < z + (arrivalWeightedSum β d ω).toReal)
    (hLaw : (markedSpacings μ).map (arrivalSoftOutput β d z) = μ)
    (ht : z < Real.exp (β * t)) :
    μ (Iio (Real.exp (-β * t))) ≤
      (∫⁻ x, μ (Ioi (Real.exp (β * (t + x) / 2))) ∂intensity d) +
        (∫⁻ x, ENNReal.ofReal (Real.exp (β * (t - x) / 2)) ∂intensity d) /
          ENNReal.ofReal (Real.exp (β * t) - z) := by
  let P := markedSpacings μ
  let s : Set (ℝ × ℝ) := {p | Real.exp (β * (t + p.1) / 2) < p.2}
  let f : ℝ × ℝ → ℝ≥0∞ := fun p ↦ ENNReal.ofReal (Real.exp (-β * p.1) * p.2)
  let g : ℝ × ℝ → ℝ≥0∞ := fun p ↦ ENNReal.ofReal (Real.exp (β * (t - p.1) / 2))
  let ε := ENNReal.ofReal (Real.exp (β * t) - z)
  have hε : ε ≠ 0 := (ENNReal.ofReal_pos.mpr (sub_pos.mpr ht)).ne'
  have hs : MeasurableSet s := measurableSet_lt (by fun_prop) measurable_snd
  have hg : Measurable g := by unfold g; fun_prop
  have hfg : ∀ p ∉ s, f p ≤ g p := by
    intro p hp
    have hp' : p.2 ≤ Real.exp (β * (t + p.1) / 2) := le_of_not_gt hp
    apply ENNReal.ofReal_le_ofReal
    calc
      Real.exp (-β * p.1) * p.2 ≤ Real.exp (-β * p.1) * Real.exp (β * (t + p.1) / 2) :=
        mul_le_mul_of_nonneg_left hp' (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hM := measure_arrival_sum_gt_le_of_envelope hd μ hg hs hfg hε ENNReal.ofReal_ne_top
  have hsI : ((intensity d).prod μ) s =
      ∫⁻ x, μ (Ioi (Real.exp (β * (t + x) / 2))) ∂intensity d := by
    rw [Measure.prod_apply hs]
    rfl
  have hgI : (∫⁻ p, g p ∂(intensity d).prod μ) =
      ∫⁻ x, ENNReal.ofReal (Real.exp (β * (t - x) / 2)) ∂intensity d := by
    rw [lintegral_prod _ hg.aemeasurable]
    simp [g]
  rw [hsI, hgI] at hM
  refine le_trans ?_ hM
  nth_rw 1 [← hLaw]
  rw [Measure.map_apply (measurable_arrivalSoftOutput ..) measurableSet_Iio]
  apply measure_mono_ae
  filter_upwards [hfin, hpos] with ω hf hf₀ hω
  have hw : (z + (arrivalWeightedSum β d ω).toReal)⁻¹ < (Real.exp (β * t))⁻¹ := by
    change arrivalSoftOutput β d z ω < Real.exp (-β * t) at hω
    simpa only [arrivalSoftOutput, ← Real.exp_neg, neg_mul] using hω
  have hsum : Real.exp (β * t) - z < (arrivalWeightedSum β d ω).toReal := by
    have := (inv_lt_inv₀ hf₀ (Real.exp_pos _)).mp hw
    linarith
  change ε < arrivalWeightedSum β d ω
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (sub_nonneg.mpr ht.le)).mpr hsum |>.trans_eq
    (ENNReal.ofReal_toReal hf)

end Certificate

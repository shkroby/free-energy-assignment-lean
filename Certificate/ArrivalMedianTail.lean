import Certificate.ArrivalSoftExchange
import Certificate.CavityUpperTail
import Certificate.PoissonArrivalCount

/-! First qualifying child and upper log tails on the canonical arrivals. -/

open MeasureTheory Set
open scoped ENNReal

namespace Certificate

/-- For a recursive law whose marks exceed `exp (β b)` with probability at
least one half, the shifted logarithmic upper tail is bounded by
`exp (-t^d/2)`. -/
theorem arrival_cavity_median_upperTail {d β z b : ℝ}
    (hd : 0 < d) (hβ : 0 < β) (hz : 0 ≤ z)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hfin : ∀ᵐ ω ∂markedSpacings μ, arrivalWeightedSum β d ω ≠ ∞)
    (hLaw : (markedSpacings μ).map (arrivalSoftOutput β d z) = μ)
    (hb : 1 / 2 ≤ (μ (Ici (Real.exp (β * b)))).toReal)
    {t : ℝ} (ht : 0 ≤ t) :
    μ (Ioi (Real.exp (β * (t - b)))) ≤ ENNReal.ofReal (Real.exp (-(t ^ d / 2))) := by
  let A : Set ℝ := Ici (Real.exp (β * b))
  let B : Set ℝ := Ioi (Real.exp (β * (t - b)))
  let V : Set ArrivalConfiguration := {ω | ∀ i, (arrivalLength d ω.1 i, ω.2 i) ∉ Ioc 0 t ×ˢ A}
  have hsub : (arrivalSoftOutput β d z ⁻¹' B) ≤ᵐ[markedSpacings μ] V := by
    filter_upwards [hfin] with ω hf hω
    intro i hi
    let x := arrivalLength d ω.1 i
    let h := ω.2 i
    have ht' : x ≤ t := hi.1.2
    have hh : Real.exp (β * b) ≤ h := hi.2
    have hterm : Real.exp (β * (b - t)) ≤ Real.exp (-β * x) * h := by
      calc
        _ = Real.exp (-β * t) * Real.exp (β * b) := by
          rw [← Real.exp_add]
          congr 1
          ring
        _ ≤ _ := by
          have hs : Real.exp (-β * t) ≤ Real.exp (-β * x) := by
            apply Real.exp_le_exp.mpr
            nlinarith [mul_nonneg hβ.le (sub_nonneg.mpr ht')]
          exact mul_le_mul hs hh (Real.exp_nonneg _) (Real.exp_nonneg _)
    have hi' : ENNReal.ofReal (Real.exp (-β * x) * h) ≤ arrivalWeightedSum β d ω :=
      ENNReal.le_tsum i
    have hSum :
        Real.exp (-β * x) * h ≤ (arrivalWeightedSum β d ω).toReal := by
      have h' := ENNReal.toReal_mono hf hi'
      exact (ENNReal.toReal_ofReal (mul_nonneg (Real.exp_nonneg _)
        ((Real.exp_pos _).le.trans hh))).symm.trans_le h'
    have hden := hterm.trans (hSum.trans (le_add_of_nonneg_left hz))
    have harg := inv_anti₀ (Real.exp_pos (β * (b - t))) hden
    have he : (Real.exp (β * (b - t)))⁻¹ = Real.exp (β * (t - b)) := by
      rw [← Real.exp_neg]
      congr 1
      ring
    exact (not_lt_of_ge (harg.trans_eq he)) hω
  rw [← hLaw, Measure.map_apply (measurable_arrivalSoftOutput β d z) measurableSet_Ioi]
  calc
    _ ≤ markedSpacings μ V := measure_mono_ae hsub
    _ = ENNReal.ofReal (Real.exp (-(t ^ d * (μ A).toReal))) :=
      canonical_marked_window_void hd ht μ measurableSet_Ici
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg ht d)
      linarith

/-- A bounded recursive law at positive fugacity has expected incident
occupation at most one. -/
theorem expectedOccupationMass_le_one_of_soft_cavity_law {d β z : ℝ}
    (hd : 0 < d) (hβ : 0 < β) (hz : 0 < z)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc 0 z⁻¹)
    (hLaw : (markedSpacings μ).map (arrivalSoftOutput β d z) = μ) :
    expectedOccupationMass β d μ ≤ 1 := by
  have hfin : ∀ᵐ ω ∂markedSpacings μ, arrivalWeightedSum β d ω ≠ ∞ := by
    filter_upwards [ae_arrivalWeightedSum_eq_ofReal_tsum hd hβ μ hμ] with ω hω
    rw [hω]
    exact ENNReal.ofReal_ne_top
  change occupationMassBetween β d μ μ ≤ 1
  rw [arrivalOccupationMass_eq_mean_vacancy_deficit hd hz μ μ
    (hμ.mono fun _ h ↦ h.1) hfin hLaw]
  calc
    _ ≤ ∫⁻ _ : ℝ, (1 : ℝ≥0∞) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hμ] with x hx
      simpa using (ENNReal.ofReal_le_ofReal (by nlinarith [mul_nonneg hz.le hx.1]
        : 1 - z * x ≤ 1))
    _ = 1 := by simp

/-- A lower bound for the median makes the upper log tail uniform above
twice the bound, with the manuscript's stretched exponential. -/
theorem arrival_log_upperTail_of_median_lower_bound {d β z b B : ℝ}
    (hd : 0 < d) (hβ : 0 < β) (hz : 0 ≤ z) (hB : 0 ≤ B)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hfin : ∀ᵐ ω ∂markedSpacings μ, arrivalWeightedSum β d ω ≠ ∞)
    (hLaw : (markedSpacings μ).map (arrivalSoftOutput β d z) = μ)
    (hb : 1 / 2 ≤ (μ (Ici (Real.exp (β * b)))).toReal)
    (hblo : -B ≤ b) {x : ℝ} (hx : 2 * B ≤ x) :
    μ (Ioi (Real.exp (β * x))) ≤ ENNReal.ofReal (Real.exp (-((x / 2) ^ d / 2))) := by
  have hx₀ : 0 ≤ x / 2 := by linarith
  have hle : Real.exp (β * (x / 2 - b)) ≤ Real.exp (β * x) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith) hβ.le)
  exact (measure_mono (Ioi_subset_Ioi hle)).trans
    (arrival_cavity_median_upperTail hd hβ hz μ hfin hLaw hb hx₀)

end Certificate

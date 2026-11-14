import Certificate.Endpoints
import Certificate.Intensity

/-!
# The first upper bound on the logarithmic message

Two independent messages above `exp (β s)` give occupation probability at
least one half on every edge of length at most `2 s`. The unit bound on
the expected sum of the occupations then supplies the upper tightness estimate.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Certificate

/-- Expected occupation integrated over the edge intensity. -/
noncomputable def expectedOccupationMass (β d : ℝ) (μ : Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ∫⁻ h : ℝ × ℝ,
    ENNReal.ofReal (edgeOccupation (Real.exp (-β * x)) h.1 h.2) ∂(μ.prod μ)
    ∂intensity d

private theorem half_le_edgeOccupation_of_large_marks
    {β s x H H' : ℝ} (hβ : 0 < β) (hx : x ≤ 2 * s)
    (hH : Real.exp (β * s) ≤ H) (hH' : Real.exp (β * s) ≤ H') :
    1 / 2 ≤ edgeOccupation (Real.exp (-β * x)) H H' := by
  have hH₀ := (Real.exp_pos _).trans_le hH
  have hH'₀ := (Real.exp_pos _).trans_le hH'
  have hw := Real.exp_pos (-β * x)
  have hmul : 1 ≤ Real.exp (-β * x) * H * H' := by
    calc
      (1 : ℝ) ≤ Real.exp (β * (2 * s - x)) := Real.one_le_exp (by positivity)
      _ = Real.exp (-β * x) * Real.exp (β * s) * Real.exp (β * s) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := by gcongr
  have hden : 0 < 1 + Real.exp (-β * x) * H * H' := by linarith
  unfold edgeOccupation
  apply (le_div_iff₀ hden).mpr
  linarith

/-- Exact upper tightness inequality in the log-message proof, given the
expected occupation mass bound from the insertion identity. -/
theorem logMessage_upperTail_sq_bound {β d s : ℝ}
    (hβ : 0 < β) (hd : 0 < d) (hs : 0 < s)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmass : expectedOccupationMass β d μ ≤ 1) :
    ENNReal.ofReal ((2 * s) ^ d / 2) * (μ (Ioi (Real.exp (β * s)))) ^ 2 ≤ 1 := by
  let A : Set ℝ := Ioi (Real.exp (β * s))
  let E : Set ℝ := Ioc 0 (2 * s)
  have hA : MeasurableSet A := measurableSet_Ioi
  have hE : MeasurableSet E := measurableSet_Ioc
  have hrect : MeasurableSet (A ×ˢ A) := hA.prod hA
  let c := ENNReal.ofReal (1 / 2) * (μ A) ^ 2
  have hlower (x : ℝ) (hx : x ∈ E) :
      c ≤ ∫⁻ h : ℝ × ℝ,
        ENNReal.ofReal (edgeOccupation (Real.exp (-β * x)) h.1 h.2) ∂(μ.prod μ) := by
    have hcalc : (∫⁻ h : ℝ × ℝ, (A ×ˢ A).indicator (fun _ ↦ ENNReal.ofReal (1 / 2)) h
        ∂(μ.prod μ)) = c := by
      rw [lintegral_indicator_const hrect, Measure.prod_prod]
      simp only [c, pow_two]
    rw [← hcalc]
    refine lintegral_mono fun h ↦ ?_
    by_cases hh : h ∈ A ×ˢ A
    · rw [Set.indicator_of_mem hh]
      exact ENNReal.ofReal_le_ofReal
        (half_le_edgeOccupation_of_large_marks hβ hx.2 hh.1.le hh.2.le)
    · rw [Set.indicator_of_notMem hh]
      exact zero_le
  have hInt : (∫⁻ x, E.indicator (fun _ ↦ c) x ∂intensity d) ≤ expectedOccupationMass β d μ := by
    unfold expectedOccupationMass
    refine lintegral_mono fun x ↦ ?_
    by_cases hx : x ∈ E
    · rw [Set.indicator_of_mem hx]
      exact hlower x hx
    · rw [Set.indicator_of_notMem hx]
      exact zero_le
  rw [lintegral_indicator_const hE] at hInt
  have hME : intensity d E = ENNReal.ofReal ((2 * s) ^ d) :=
    intensity_Ioc_zero hd (by positivity)
  rw [hME] at hInt
  have hform : ENNReal.ofReal ((2 * s) ^ d / 2) * (μ A) ^ 2 =
      c * ENNReal.ofReal ((2 * s) ^ d) := by
    have he : (2 * s) ^ d / 2 = (2 * s) ^ d * (1 / 2) := by ring
    rw [he, ENNReal.ofReal_mul (by positivity)]
    dsimp [c]
    ac_rfl
  rw [hform]
  exact hInt.trans hmass

end Certificate

import Certificate.PoissonPWIT

/-!
# The first good child and the median tail bound

For the marked Poisson construction, one child whose mark exceeds the median
threshold is enough to upper bound the parent message. The probability of no
such child is the void probability in the appropriate length window.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Certificate

abbrev PWITConfiguration := ℕ → PoissonBatch (ℝ × ℝ)

/-- The nonnegative marked series before taking its reciprocal. -/
noncomputable def pwitWeightedSum (β : ℝ) (ω : PWITConfiguration) : ℝ≥0∞ :=
  ∑' j, poissonBatchSum (0, 0)
    (fun h ↦ ENNReal.ofReal (Real.exp (-β * h.1) * h.2)) (ω j)

theorem measurable_pwitWeightedSum (β : ℝ) : Measurable (pwitWeightedSum β) := by
  unfold pwitWeightedSum
  apply Measurable.tsum
  intro j
  exact (measurable_poissonBatchSum (0, 0) _ (by fun_prop)).comp (measurable_pi_apply j)

theorem pwitWeightedSum_ge_term (β : ℝ) (ω : PWITConfiguration)
    (j : ℕ) (i : Fin (ω j).1) :
    ENNReal.ofReal (Real.exp (-β * ((ω j).2 i).1) * ((ω j).2 i).2) ≤
      pwitWeightedSum β ω := by
  have hs : ENNReal.ofReal (Real.exp (-β * ((ω j).2 i).1) * ((ω j).2 i).2) ≤
      poissonBatchSum (0, 0)
        (fun h ↦ ENNReal.ofReal (Real.exp (-β * h.1) * h.2)) (ω j) := by
    rw [poissonBatchSum_eq_sum]
    apply Finset.single_le_sum (a := i) (fun _ _ ↦ by positivity)
    exact Finset.mem_univ _
  exact hs.trans (ENNReal.le_tsum j)

/-- A recursive output under the batch construction. Finiteness of the
denominator is imposed in results which reason about the real reciprocal. -/
noncomputable def pwitCavityOutput (β z : ℝ) (ω : PWITConfiguration) : ℝ :=
  (z + (pwitWeightedSum β ω).toReal)⁻¹

theorem measurable_pwitCavityOutput (β z : ℝ) : Measurable (pwitCavityOutput β z) :=
  (measurable_const.add (measurable_pwitWeightedSum β).ennreal_toReal).inv

/-- For a recursive law whose marks exceed `exp (β b)` with probability at
least one half, the shifted logarithmic upper tail is bounded by
`exp (-t^d/2)`. -/
theorem batch_cavity_median_upperTail {d β z b : ℝ}
    (hd : 0 < d) (hβ : 0 < β) (hz : 0 ≤ z)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hfin : ∀ᵐ ω ∂pwitBatchLaw d μ, pwitWeightedSum β ω ≠ ∞)
    (hLaw : (pwitBatchLaw d μ).map (pwitCavityOutput β z) = μ)
    (hb : 1 / 2 ≤ (μ (Ici (Real.exp (β * b)))).toReal)
    {t : ℝ} (ht : 0 ≤ t) :
    μ (Ioi (Real.exp (β * (t - b)))) ≤ ENNReal.ofReal (Real.exp (-(t ^ d / 2))) := by
  let A : Set ℝ := Ici (Real.exp (β * b))
  let B : Set ℝ := Ioi (Real.exp (β * (t - b)))
  let V : Set PWITConfiguration := poissonAvoid (Ioc 0 t ×ˢ A)
  have hsub : (pwitCavityOutput β z ⁻¹' B) ≤ᵐ[pwitBatchLaw d μ] V := by
    filter_upwards [hfin] with ω hf hω
    intro j _ i hi
    let x := ((ω j).2 i).1
    let h := ((ω j).2 i).2
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
    have hSum :
        Real.exp (-β * x) * h ≤ (pwitWeightedSum β ω).toReal := by
      have h' := ENNReal.toReal_mono hf (pwitWeightedSum_ge_term β ω j i)
      exact (ENNReal.toReal_ofReal (mul_nonneg (Real.exp_nonneg _)
        ((Real.exp_pos _).le.trans hh))).symm.trans_le h'
    have hden := hterm.trans (hSum.trans (le_add_of_nonneg_left hz))
    have harg := inv_anti₀ (Real.exp_pos (β * (b - t))) hden
    have he : (Real.exp (β * (b - t)))⁻¹ = Real.exp (β * (t - b)) := by
      rw [← Real.exp_neg]
      congr 1
      ring
    exact (not_lt_of_ge (harg.trans_eq he)) hω
  rw [← hLaw, Measure.map_apply (measurable_pwitCavityOutput β z) measurableSet_Ioi]
  calc
    _ ≤ pwitBatchLaw d μ V := measure_mono_ae hsub
    _ = ENNReal.ofReal (Real.exp (-(t ^ d * (μ A).toReal))) :=
      pwit_window_void hd ht μ measurableSet_Ici
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg ht d)
      linarith

end Certificate

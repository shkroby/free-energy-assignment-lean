import Certificate.CavityFinitePrefix
import Certificate.CavityLawLimit
import Certificate.CavityPrefixTail

/-! Passage through the full marked recursion under a common upper-tail bound. -/

open Filter MeasureTheory Set
open scoped Topology ENNReal

namespace Certificate

/-- Weak convergence of the mark laws gives weak convergence of the full
denominators when the marks have a common stretched upper log tail. -/
theorem tendsto_arrivalDenominatorLaws_of_log_tail {β d c K : ℝ}
    (hβ : 0 < β) (hd : 0 < d) (hc : 0 < c) (hK : 0 ≤ K)
    (z : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure ℝ) (H : ProbabilityMeasure ℝ)
    (hz : Tendsto z atTop (𝓝 0)) (hμ : Tendsto μ atTop (𝓝 H))
    (hmarks : ∀ ν ∈ insert H (range μ), ∀ᵐ h ∂(ν : Measure ℝ), 0 ≤ h)
    (htail : ∀ ν ∈ insert H (range μ), ∀ x > 0, (ν : Measure ℝ) (Ioi (Real.exp (β * x / 2))) ≤
      ENNReal.ofReal (K * Real.exp (-(c * x ^ d)))) :
    Tendsto (fun n ↦ arrivalDenominatorLaw β d (z n) (μ n)) atTop
      (𝓝 (arrivalDenominatorLaw β d 0 H)) := by
  let P (n : ℕ) := markedSpacings (μ n : Measure ℝ)
  let Q := markedSpacings (H : Measure ℝ)
  have hμm (n : ℕ) : μ n ∈ insert H (range μ) :=
    mem_insert_of_mem _ (mem_range_self n)
  have hHm : H ∈ insert H (range μ) := mem_insert _ _
  have hD : TendstoInDistribution (fun n ↦ arrivalDenominator β d (z n)) atTop
      (arrivalDenominator β d 0) P Q := by
    apply tendstoInDistribution_of_uniform_truncations
      (Xcut := fun k _ ↦ cavityPrefixSum β d k) (Ycut := cavityPrefixSum β d)
      (fun _ ↦ measurable_arrivalDenominator ..) (measurable_arrivalDenominator ..)
      (fun k _ ↦ measurable_cavityPrefixSum β hd k) (measurable_cavityPrefixSum β hd)
      (tendstoInDistribution_cavityPrefix hμ β hd)
    intro δ hδ η hη
    obtain ⟨k, hk⟩ := exists_uniform_cavity_prefix_error hβ hd hc hK (half_pos hδ) hη
    refine ⟨k, ?_, ?_⟩
    · have hsmall := hz.eventually ((continuous_abs.tendsto (0 : ℝ)).eventually
        (Iio_mem_nhds (by simpa only [abs_zero] using half_pos hδ)))
      filter_upwards [hsmall] with n hn
      refine (measureReal_mono ?_).trans (hk (μ n : Measure ℝ) (hmarks _ (hμm n)) (htail _ (hμm n)))
      intro ω hω
      change δ ≤ |z n + (arrivalWeightedSum β d ω).toReal - cavityPrefixSum β d k ω| at hω
      change δ / 2 ≤ |(arrivalWeightedSum β d ω).toReal - cavityPrefixSum β d k ω|
      rw [add_sub_assoc] at hω
      linarith [abs_add_le (z n) ((arrivalWeightedSum β d ω).toReal - cavityPrefixSum β d k ω),
        show |z n| < δ / 2 from hn]
    · refine (measureReal_mono ?_).trans (hk (H : Measure ℝ) (hmarks _ hHm) (htail _ hHm))
      intro ω hω
      change δ ≤ |cavityPrefixSum β d k ω - (0 + (arrivalWeightedSum β d ω).toReal)| at hω
      rw [zero_add, abs_sub_comm] at hω
      exact (half_le_self hδ.le).trans hω
  exact hD.tendsto

/-- A weak limit of the positive-fugacity fixed points solves the hard
equation provided the family and its limit satisfy the stated upper-tail
bound and the limiting marks are strictly positive. -/
theorem isCavityLaw_of_weak_limit_of_log_tail {β d c K : ℝ}
    (hβ : 0 < β) (hd : 0 < d) (hc : 0 < c) (hK : 0 ≤ K)
    (z : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure ℝ) (H : ProbabilityMeasure ℝ)
    (hz : Tendsto z atTop (𝓝 0)) (hμ : Tendsto μ atTop (𝓝 H))
    (hH : (H : Measure ℝ) (Ioi 0) = 1)
    (hmarks : ∀ ν ∈ insert H (range μ), ∀ᵐ h ∂(ν : Measure ℝ), 0 ≤ h)
    (htail : ∀ ν ∈ insert H (range μ), ∀ x > 0, (ν : Measure ℝ) (Ioi (Real.exp (β * x / 2))) ≤
      ENNReal.ofReal (K * Real.exp (-(c * x ^ d))))
    (hsoft : ∀ n, (markedSpacings (μ n)).map (arrivalSoftOutput β d (z n)) = (μ n : Measure ℝ)) :
    IsCavityLaw β d (H : Measure ℝ) := by
  apply isCavityLaw_of_tendsto_arrivalDenominatorLaws z μ H hH hμ hsoft
    _ (tendsto_arrivalDenominatorLaws_of_log_tail hβ hd hc hK z μ H hz hμ hmarks htail)
  have hHm : H ∈ insert H (range μ) := mem_insert _ _
  have hS := ae_summable_cavityTerm_of_stretched_log_tail hd hβ hc hK (H : Measure ℝ)
    (hmarks H hHm) (htail H hHm)
  have hH' : ∀ᵐ h ∂(H : Measure ℝ), 0 < h := (mem_ae_iff_prob_eq_one measurableSet_Ioi).mpr hH
  have hpos : ∀ᵐ ω ∂markedSpacings (H : Measure ℝ), ∀ i, 0 < ω.2 i := by
    apply ae_all_iff.mpr
    intro i
    exact (markedArrival_eval_preserving (H : Measure ℝ) i).quasiMeasurePreserving.tendsto_ae.eventually hH'
  filter_upwards [hS, hpos] with ω hsum hω
  refine ⟨hsum, ?_⟩
  have h₀ : 0 < cavityTerm β d ω 0 := mul_pos (Real.exp_pos _) (hω 0)
  exact h₀.trans_le (hsum.le_tsum 0 (fun i _ ↦ mul_nonneg (Real.exp_nonneg _) (hω i).le))

end Certificate

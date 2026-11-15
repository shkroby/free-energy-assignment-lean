import Mathlib.Probability.CDF
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! A two-sided logarithmic median for a strictly positive real law. -/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

namespace Certificate

/-- Every probability measure on the reals has a median, with closed
half-lines on both sides to allow atoms. -/
theorem exists_measure_median (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ∃ m : ℝ, 1 / 2 ≤ (μ (Iic m)).toReal ∧ 1 / 2 ≤ (μ (Ici m)).toReal := by
  let A : Set ℝ := {x | 1 / 2 ≤ cdf μ x}
  obtain ⟨lo, hlo⟩ := eventually_atBot.mp
    ((tendsto_order.mp (tendsto_cdf_atBot μ)).2 (1 / 2) (by norm_num))
  obtain ⟨hi, hhi⟩ := eventually_atTop.mp
    ((tendsto_order.mp (tendsto_cdf_atTop μ)).1 (1 / 2) (by norm_num))
  have hA : A.Nonempty := ⟨hi, (hhi hi le_rfl).le⟩
  have hB : BddBelow A := by
    refine ⟨lo, fun x hx => le_of_not_ge ?_⟩
    exact fun h => not_lt_of_ge hx (hlo x h)
  let m := sInf A
  have habove (x : ℝ) (hx : m < x) : 1 / 2 ≤ cdf μ x := by
    obtain ⟨y, hy, hyx⟩ := exists_lt_of_csInf_lt hA hx
    exact (show 1 / 2 ≤ cdf μ y from hy).trans (monotone_cdf μ hyx.le)
  have hbelow (x : ℝ) (hx : x < m) : cdf μ x < 1 / 2 := by
    exact lt_of_not_ge (fun h => not_lt_of_ge (csInf_le hB h) hx)
  refine ⟨m, ?_, ?_⟩
  · change 1 / 2 ≤ (μ.real (Iic m))
    rw [← cdf_eq_real μ, ← (cdf μ).iInf_Ioi_eq]
    exact le_ciInf (fun x : Ioi m => habove x x.property)
  · have hleft : Function.leftLim (cdf μ) m ≤ 1 / 2 := by
      apply le_of_tendsto ((monotone_cdf μ).tendsto_leftLim m)
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact (hbelow x hx).le
    rw [← measure_cdf μ, (cdf μ).measure_Ici (tendsto_cdf_atTop μ),
      ENNReal.toReal_ofReal (by linarith)]
    linarith

/-- For strictly positive marks, a real median in units of `log H / β`
exists for every positive `β`. -/
theorem exists_logMessage_median {β : ℝ} (hβ : 0 < β) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hpos : μ (Ioi 0) = 1) :
    ∃ b : ℝ, 1 / 2 ≤ (μ (Iic (Real.exp (β * b)))).toReal ∧
      1 / 2 ≤ (μ (Ici (Real.exp (β * b)))).toReal := by
  obtain ⟨m, hlo, hhi⟩ := exists_measure_median μ
  have hzero : μ (Iic 0) = 0 := by
    rw [← compl_Ioi, prob_compl_eq_one_sub measurableSet_Ioi, hpos, tsub_self]
  have hm : 0 < m := by
    by_contra! hm
    have hz : μ (Iic m) = 0 := le_antisymm
      ((measure_mono (Iic_subset_Iic.mpr hm)).trans_eq hzero) zero_le
    rw [hz, ENNReal.toReal_zero] at hlo
    norm_num at hlo
  refine ⟨Real.log m / β, ?_⟩
  have he : Real.exp (β * (Real.log m / β)) = m := by
    rw [show β * (Real.log m / β) = Real.log m by field_simp, Real.exp_log hm]
  rw [he]
  exact ⟨hlo, hhi⟩

end Certificate

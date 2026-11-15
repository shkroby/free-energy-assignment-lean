import Certificate.CavityCouplingCompact
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# An extremal coupling for the lower-orthant order

Using one uniform variate for both marginal quantiles maximizes the
measure of every lower orthant among all couplings of the marginals.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Certificate

/-- The quantile for a uniform input in the open unit interval. -/
noncomputable def measureQuantile (μ : Measure ℝ) (u : ℝ) : ℝ :=
  if u ∈ Ioo 0 1 then sInf {x | u ≤ cdf μ x} else 0

theorem measureQuantile_le_iff (μ : Measure ℝ) {u x : ℝ} (hu : u ∈ Ioo 0 1) :
    measureQuantile μ u ≤ x ↔ u ≤ cdf μ x := by
  let A : Set ℝ := {x | u ≤ cdf μ x}
  obtain ⟨lo, hlo⟩ := eventually_atBot.mp
    ((tendsto_order.mp (tendsto_cdf_atBot μ)).2 u hu.1)
  obtain ⟨hi, hhi⟩ := eventually_atTop.mp
    ((tendsto_order.mp (tendsto_cdf_atTop μ)).1 u hu.2)
  have hA : A.Nonempty := ⟨hi, (hhi hi le_rfl).le⟩
  have hB : BddBelow A := by
    refine ⟨lo, fun a ha ↦ le_of_not_ge ?_⟩
    exact fun hb ↦ not_lt_of_ge ha (hlo a hb)
  have hIn : u ≤ cdf μ (sInf A) := by
    rw [← (cdf μ).iInf_Ioi_eq]
    apply le_ciInf
    intro t
    obtain ⟨v, hv, hvt⟩ := exists_lt_of_csInf_lt hA t.property
    exact (show u ≤ cdf μ v from hv).trans (monotone_cdf μ hvt.le)
  rw [measureQuantile, if_pos hu]
  exact ⟨fun h ↦ hIn.trans (monotone_cdf μ h), fun hx ↦ csInf_le hB hx⟩

theorem measurable_measureQuantile (μ : Measure ℝ) : Measurable (measureQuantile μ) := by
  apply measurable_of_Iic
  intro x
  let A : Set ℝ := Ioo 0 1
  have H : measureQuantile μ ⁻¹' Iic x =
      (A ∩ Iic (cdf μ x)) ∪ (if 0 ≤ x then Aᶜ else ∅) := by
    ext u
    by_cases hu : u ∈ A
    · have h := measureQuantile_le_iff μ hu (x := x)
      by_cases hx : 0 ≤ x <;> simpa [A, hu, hx] using h
    · by_cases hx : 0 ≤ x <;> simp [measureQuantile, A, hu, hx]
  rw [H]
  apply (measurableSet_Ioo.inter measurableSet_Iic).union
  split
  · exact measurableSet_Ioo.compl
  · exact MeasurableSet.empty

private noncomputable def uniformUnit : Measure ℝ := volume.restrict (Ioo 0 1)

private theorem uniformUnit_isProbabilityMeasure : IsProbabilityMeasure uniformUnit := by
  constructor
  unfold uniformUnit
  rw [Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero, ENNReal.ofReal_one]

private theorem uniformUnit_le (r : ℝ) (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) :
    uniformUnit (Iic r) = ENNReal.ofReal r := by
  unfold uniformUnit
  rw [Measure.restrict_apply measurableSet_Iic]
  by_cases h : r = 1
  · subst r
    rw [inter_eq_right.mpr (show Ioo (0 : ℝ) 1 ⊆ Iic 1 from fun _ hx ↦ hx.2.le),
      Real.volume_Ioo, sub_zero]
  · have hr : r < 1 := lt_of_le_of_ne hr₁ h
    have H : Iic r ∩ Ioo 0 1 = Ioc 0 r := by
      ext x
      exact ⟨fun hx ↦ ⟨hx.2.1, hx.1⟩, fun hx ↦ ⟨hx.2, ⟨hx.1, hx.2.trans_lt hr⟩⟩⟩
    rw [H, Real.volume_Ioc, sub_zero]

private theorem uniformUnit_map_measureQuantile (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    uniformUnit.map (measureQuantile μ) = μ := by
  let : IsProbabilityMeasure uniformUnit := uniformUnit_isProbabilityMeasure
  let : IsProbabilityMeasure (uniformUnit.map (measureQuantile μ)) :=
    Measure.isProbabilityMeasure_map (measurable_measureQuantile μ).aemeasurable
  apply Measure.ext_of_Iic
  intro x
  rw [Measure.map_apply (measurable_measureQuantile μ) measurableSet_Iic]
  have H : measureQuantile μ ⁻¹' Iic x =ᵐ[uniformUnit] Iic (cdf μ x) := by
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioo : MeasurableSet (Ioo (0 : ℝ) 1))]
      with u hu
    exact propext (measureQuantile_le_iff μ hu)
  rw [measure_congr H, uniformUnit_le _ (cdf_nonneg μ x) (cdf_le_one μ x),
    cdf_eq_real, Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- A coupling with both messages obtained from a common uniform quantile. -/
noncomputable def commonQuantileCoupling (μ ν : ProbabilityMeasure ℝ) : ProbabilityMeasure (ℝ × ℝ) :=
  letI : IsProbabilityMeasure uniformUnit := uniformUnit_isProbabilityMeasure
  ⟨uniformUnit.map (fun u ↦ (measureQuantile μ u, measureQuantile ν u)),
    Measure.isProbabilityMeasure_map
      ((measurable_measureQuantile μ).prodMk (measurable_measureQuantile ν)).aemeasurable⟩

theorem commonQuantileCoupling_mem (μ ν : ProbabilityMeasure ℝ) :
    commonQuantileCoupling μ ν ∈ couplingLaws μ ν := by
  constructor
  · apply Subtype.ext
    change (uniformUnit.map _).map Prod.fst = (μ : Measure ℝ)
    rw [Measure.map_map measurable_fst ((measurable_measureQuantile μ).prodMk (measurable_measureQuantile ν))]
    exact uniformUnit_map_measureQuantile μ
  · apply Subtype.ext
    change (uniformUnit.map _).map Prod.snd = (ν : Measure ℝ)
    rw [Measure.map_map measurable_snd ((measurable_measureQuantile μ).prodMk (measurable_measureQuantile ν))]
    exact uniformUnit_map_measureQuantile ν

/-- The common-quantile coupling realizes the largest possible mass of
each lower orthant. -/
theorem commonQuantileCoupling_orthant (μ ν : ProbabilityMeasure ℝ) (x y : ℝ) :
    (commonQuantileCoupling μ ν : Measure (ℝ × ℝ)) (Iic x ×ˢ Iic y) =
      ENNReal.ofReal (min (cdf μ x) (cdf ν y)) := by
  change (uniformUnit.map (fun u ↦ (measureQuantile μ u, measureQuantile ν u))) (Iic x ×ˢ Iic y) = _
  rw [Measure.map_apply ((measurable_measureQuantile μ).prodMk (measurable_measureQuantile ν))
    (measurableSet_Iic.prod measurableSet_Iic)]
  have H : (fun u ↦ (measureQuantile μ u, measureQuantile ν u)) ⁻¹' (Iic x ×ˢ Iic y) =ᵐ[uniformUnit]
      Iic (min (cdf μ x) (cdf ν y)) := by
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioo : MeasurableSet (Ioo (0 : ℝ) 1))]
      with u hu
    apply propext
    exact (and_congr (measureQuantile_le_iff μ hu) (measureQuantile_le_iff ν hu)).trans le_min_iff.symm
  rw [measure_congr H]
  apply uniformUnit_le
  · exact le_min (cdf_nonneg μ _) (cdf_nonneg ν _)
  · exact (min_le_left _ _).trans (cdf_le_one μ _)

end Certificate

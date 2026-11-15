import Certificate.CavityTightness
import Certificate.CavityWeakLimit
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-! Weak compactness followed by passage through the marked recursion. -/

open Filter MeasureTheory Set
open scoped Topology ENNReal

namespace Certificate

/-- From a vanishing sequence of fugacities and soft laws with uniformly
tight logarithms and a common stretched upper tail, extract a positive
hard cavity law. -/
theorem exists_subseq_cavityLaw_of_compact_soft_logs {β d c K : ℝ}
    (hβ : 0 < β) (hd : 0 < d) (hc : 0 < c) (hK : 0 ≤ K)
    (z : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure ℝ)
    (hz : Tendsto z atTop (𝓝 0))
    (hpos : ∀ n, (μ n : Measure ℝ) (Ioi 0) = 1)
    (hsoft : ∀ n, (markedSpacings (μ n)).map (arrivalSoftOutput β d (z n)) = (μ n : Measure ℝ))
    (hC : IsCompact (closure (range (fun n ↦ (μ n).map Real.measurable_log.aemeasurable))))
    (htail : ∀ n, ∀ x > 0, (μ n : Measure ℝ) (Ioi (Real.exp (β * x / 2))) ≤
      ENNReal.ofReal (K * Real.exp (-(c * x ^ d)))) :
    ∃ (H : ProbabilityMeasure ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (μ ∘ φ) atTop (𝓝 H) ∧ IsCavityLaw β d (H : Measure ℝ) := by
  let logs (n : ℕ) := (μ n).map Real.measurable_log.aemeasurable
  obtain ⟨G, _, φ, hφm, hφ⟩ := hC.isSeqCompact
    (show ∀ n, logs n ∈ closure (range logs) from fun n ↦ subset_closure (mem_range_self n))
  let H := G.map Real.measurable_exp.aemeasurable
  have hback (n : ℕ) : (logs n).map Real.measurable_exp.aemeasurable = μ n := by
    apply Subtype.ext
    change Measure.map Real.exp ((μ n : Measure ℝ).map Real.log) = (μ n : Measure ℝ)
    rw [Measure.map_map Real.measurable_exp Real.measurable_log]
    have hpos' : ∀ᵐ h ∂(μ n : Measure ℝ), h ∈ Ioi (0 : ℝ) :=
      (mem_ae_iff_prob_eq_one measurableSet_Ioi).mpr (hpos n)
    have hm : Real.exp ∘ Real.log =ᵐ[(μ n : Measure ℝ)] id :=
      hpos'.mono fun h hh ↦ Real.exp_log hh
    rw [Measure.map_congr hm, Measure.map_id]
  have hp := exp_map_pos_and_tendsto hφ
  have hH : (H : Measure ℝ) (Ioi 0) = 1 := hp.1
  have hweak : Tendsto (μ ∘ φ) atTop (𝓝 H) := by
    change Tendsto (fun n ↦ μ (φ n)) atTop (𝓝 (G.map Real.measurable_exp.aemeasurable))
    simpa only [Function.comp_apply, hback] using hp.2
  have htail' (x : ℝ) (hx : 0 < x) : (H : Measure ℝ) (Ioi (Real.exp (β * x / 2))) ≤
      ENNReal.ofReal (K * Real.exp (-(c * x ^ d))) :=
    (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hweak isOpen_Ioi).trans
      (liminf_le_of_frequently_le' (Eventually.of_forall fun n ↦ htail (φ n) x hx).frequently)
  refine ⟨H, φ, hφm, hweak, isCavityLaw_of_weak_limit_of_log_tail hβ hd hc hK (z ∘ φ) (μ ∘ φ) H
    (hz.comp hφm.tendsto_atTop) hweak hH ?_ ?_ (fun n ↦ hsoft (φ n))⟩
  · intro ν hν
    have hν' : (ν : Measure ℝ) (Ioi 0) = 1 := by
      rcases mem_insert_iff.mp hν with rfl | ⟨n, rfl⟩
      · exact hH
      · exact hpos (φ n)
    have ha : ∀ᵐ h ∂(ν : Measure ℝ), h ∈ Ioi (0 : ℝ) :=
      (mem_ae_iff_prob_eq_one measurableSet_Ioi).mpr hν'
    exact ha.mono fun _ h ↦ (mem_Ioi.mp h).le
  · intro ν hν x hx
    rcases mem_insert_iff.mp hν with rfl | ⟨n, rfl⟩
    · exact htail' x hx
    · exact htail (φ n) x hx

end Certificate

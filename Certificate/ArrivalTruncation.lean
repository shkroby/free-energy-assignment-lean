import Certificate.ArrivalTails
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! An intensity and first-moment bound for truncating the canonical arrivals. -/

open MeasureTheory Set
open scoped ENNReal

namespace Certificate

/-- The sum of a nonnegative observable over the canonical marked arrivals. -/
noncomputable def arrivalSum (d : ℝ) (f : ℝ × ℝ → ℝ≥0∞)
    (ω : ArrivalConfiguration) : ℝ≥0∞ :=
  ∑' i, f (arrivalLength d ω.1 i, ω.2 i)

theorem measurable_arrivalSum (d : ℝ) {f : ℝ × ℝ → ℝ≥0∞} (hf : Measurable f) :
    Measurable (arrivalSum d f) := by
  apply Measurable.tsum
  intro i
  apply hf.comp
  unfold arrivalLength
  fun_prop

/-- A hit in a measurable set has probability bounded by its intensity. -/
theorem measure_arrival_hit_le {d : ℝ} (hd : 0 < d) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) :
    markedSpacings μ {ω | ∃ i, (arrivalLength d ω.1 i, ω.2 i) ∈ s} ≤
      ((intensity d).prod μ) s := by
  let f : ℝ × ℝ → ℝ≥0∞ := s.indicator 1
  have hf : Measurable f := measurable_const.indicator hs
  have hMecke : (∫⁻ ω, arrivalSum d f ω ∂markedSpacings μ) = ((intensity d).prod μ) s :=
    (canonical_marked_campbell hd μ f hf).trans (lintegral_indicator_one hs)
  have hMarkov := meas_ge_le_lintegral_div (μ := markedSpacings μ)
    (measurable_arrivalSum d hf).aemeasurable one_ne_zero ENNReal.one_ne_top
  rw [hMecke, div_one] at hMarkov
  refine (measure_mono ?_).trans hMarkov
  rintro ω ⟨i, hi⟩
  exact (show (1 : ℝ≥0∞) ≤ f (arrivalLength d ω.1 i, ω.2 i) by simp [f, hi]).trans
    (ENNReal.le_tsum i)

/-- Control a sum by the intensity of exceptional points and the expectation
of a deterministic majorant on the remaining points. -/
theorem measure_arrival_sum_gt_le_of_envelope {d : ℝ} (hd : 0 < d) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {f g : ℝ × ℝ → ℝ≥0∞} (hg : Measurable g)
    {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) (hfg : ∀ p ∉ s, f p ≤ g p)
    {ε : ℝ≥0∞} (hε₀ : ε ≠ 0) (hε : ε ≠ ∞) :
    markedSpacings μ {ω | ε < arrivalSum d f ω} ≤
      ((intensity d).prod μ) s + (∫⁻ p, g p ∂(intensity d).prod μ) / ε := by
  let P := markedSpacings μ
  let E : Set ArrivalConfiguration := {ω | ∃ i, (arrivalLength d ω.1 i, ω.2 i) ∈ s}
  have hsub : {ω | ε < arrivalSum d f ω} ⊆ E ∪ {ω | ε ≤ arrivalSum d g ω} := by
    intro ω hω
    by_cases h : ω ∈ E
    · exact Or.inl h
    · right
      exact (mem_ofPred_eq.mp hω).le.trans
        (ENNReal.tsum_le_tsum (fun i ↦ hfg _ (fun hi ↦ h ⟨i, hi⟩)))
  have hM := meas_ge_le_lintegral_div (μ := P) (measurable_arrivalSum d hg).aemeasurable hε₀ hε
  change P {ω | ε ≤ arrivalSum d g ω} ≤ (∫⁻ ω, arrivalSum d g ω ∂P) / ε at hM
  rw [show (∫⁻ ω, arrivalSum d g ω ∂P) = ∫⁻ p, g p ∂(intensity d).prod μ from
    canonical_marked_campbell hd μ g hg] at hM
  exact (measure_mono hsub).trans <| (measure_union_le _ _).trans <|
    add_le_add (measure_arrival_hit_le hd μ hs) hM

/-- The omitted weighted sum is bounded by the intensity of unusually large
marks plus the weighted length tail divided by the cutoff threshold. -/
theorem measure_arrival_weight_tail_gt_le {d β β₀ R : ℝ} (hd : 0 < d)
    (_hβ₀ : 0 < β₀) (hβ : β₀ ≤ β) (hR : 0 ≤ R)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {ε : ℝ≥0∞} (hε₀ : ε ≠ 0) (hε : ε ≠ ∞) :
    markedSpacings μ {ω | ε < arrivalSum d
      (fun p ↦ if R < p.1 then ENNReal.ofReal (Real.exp (-β * p.1) * p.2) else 0) ω} ≤
      (∫⁻ x in Ioi R, μ (Ioi (Real.exp (β * x / 2))) ∂intensity d) +
      (∫⁻ x in Ioi R, ENNReal.ofReal (Real.exp (-β₀ * x / 2)) ∂intensity d) / ε := by
  let s : Set (ℝ × ℝ) := {p | R < p.1 ∧ Real.exp (β * p.1 / 2) < p.2}
  let g : ℝ × ℝ → ℝ≥0∞ := fun p ↦ if R < p.1 then ENNReal.ofReal (Real.exp (-β₀ * p.1 / 2)) else 0
  have hs : MeasurableSet s := by
    apply MeasurableSet.inter
    · exact measurableSet_lt measurable_const measurable_fst
    · exact measurableSet_lt (by fun_prop) measurable_snd
  have hg : Measurable g := Measurable.ite
    (measurableSet_lt measurable_const measurable_fst) (by fun_prop) measurable_const
  have ht : ((intensity d).prod μ) s = ∫⁻ x in Ioi R, μ (Ioi (Real.exp (β * x / 2))) ∂intensity d := by
    rw [Measure.prod_apply hs, ← lintegral_indicator measurableSet_Ioi]
    apply lintegral_congr
    intro x
    by_cases hx : R < x
    · have H : Prod.mk x ⁻¹' s = Ioi (Real.exp (β * x / 2)) := by ext y; simp [s, hx]
      rw [H, Set.indicator_of_mem (show x ∈ Ioi R from hx)]
    · have H : Prod.mk x ⁻¹' s = ∅ := by ext y; simp [s, hx]
      rw [H, measure_empty, Set.indicator_of_notMem (show x ∉ Ioi R from hx)]
  have hG : (∫⁻ p, g p ∂(intensity d).prod μ) =
      ∫⁻ x in Ioi R, ENNReal.ofReal (Real.exp (-β₀ * x / 2)) ∂intensity d := by
    rw [lintegral_prod _ hg.aemeasurable, ← lintegral_indicator measurableSet_Ioi]
    apply lintegral_congr
    intro x
    simp only [g, lintegral_const, measure_univ, mul_one, Set.indicator_apply, mem_Ioi]
  rw [← ht, ← hG]
  apply measure_arrival_sum_gt_le_of_envelope hd μ hg hs _ hε₀ hε
  intro p hp
  by_cases hx : R < p.1
  · have hx₀ : 0 ≤ p.1 := hR.trans hx.le
    have hmark : p.2 ≤ Real.exp (β * p.1 / 2) := by
      by_contra H
      exact hp ⟨hx, lt_of_not_ge H⟩
    simp only [if_pos hx, g]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ Real.exp (-β * p.1) * Real.exp (β * p.1 / 2) :=
        mul_le_mul_of_nonneg_left hmark (Real.exp_nonneg _)
      _ = Real.exp (-β * p.1 / 2) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have h := mul_le_mul_of_nonneg_right hβ hx₀
        linarith
  · simp [g, hx]

end Certificate

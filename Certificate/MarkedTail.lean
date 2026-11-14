import Certificate.PoissonPWIT
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Truncating the marked series

A deleted tail is controlled by the chance of an exceptional mark and the
first moment of the deterministic exponential envelope. No moment of the
full positive message is assumed.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Certificate

/-- The Poisson sum of a nonnegative observable. -/
noncomputable def pwitSum (f : ℝ × ℝ → ℝ≥0∞)
    (ω : ℕ → PoissonBatch (ℝ × ℝ)) : ℝ≥0∞ :=
  ∑' j, poissonBatchSum (0, 0) f (ω j)

theorem measurable_pwitSum {f : ℝ × ℝ → ℝ≥0∞} (hf : Measurable f) :
    Measurable (pwitSum f) :=
  Measurable.tsum fun j ↦ (measurable_poissonBatchSum (0, 0) f hf).comp (measurable_pi_apply j)

theorem measure_pwit_hit_le {d : ℝ} (hd : 0 < d) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) :
    pwitBatchLaw d μ (poissonAvoid s)ᶜ ≤ ((intensity d).prod μ) s := by
  let P := pwitBatchLaw d μ
  let : IsProbabilityMeasure P := pwitBatchLaw_isProbabilityMeasure hd μ
  let a := ((intensity d).prod μ) s
  by_cases ha : a = ∞
  · change _ ≤ a
    rw [ha]
    exact le_top
  · change P (poissonAvoid s)ᶜ ≤ a
    rw [prob_compl_eq_one_sub (measurableSet_poissonAvoid hs)]
    have hv : P (poissonAvoid s) = ENNReal.ofReal (Real.exp (-a.toReal)) :=
      pwit_void hd μ hs ha
    rw [hv, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (Real.exp_nonneg _)]
    have h : 1 - Real.exp (-a.toReal) ≤ a.toReal := by
      linarith [Real.add_one_le_exp (-a.toReal)]
    exact (ENNReal.ofReal_le_ofReal h).trans_eq (ENNReal.ofReal_toReal ha)

/-- A Poisson sum is unlikely to exceed a given threshold when each
nonexceptional summand has an integrable deterministic majorant. -/
theorem measure_pwit_sum_gt_le_of_envelope {d : ℝ} (hd : 0 < d) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {f g : ℝ × ℝ → ℝ≥0∞} (hg : Measurable g)
    {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) (hfg : ∀ p ∉ s, f p ≤ g p)
    {ε : ℝ≥0∞} (hε₀ : ε ≠ 0) (hε : ε ≠ ∞) :
    pwitBatchLaw d μ {ω | ε < pwitSum f ω} ≤
      ((intensity d).prod μ) s + (∫⁻ p, g p ∂(intensity d).prod μ) / ε := by
  let P := pwitBatchLaw d μ
  have hsub : {ω | ε < pwitSum f ω} ⊆ (poissonAvoid s)ᶜ ∪ {ω | ε ≤ pwitSum g ω} := by
    intro ω hω
    by_cases h : ω ∈ poissonAvoid s
    · right
      exact (mem_ofPred_eq.mp hω).le.trans <| by
        unfold pwitSum
        apply ENNReal.tsum_le_tsum
        intro j
        rw [poissonBatchSum_eq_sum, poissonBatchSum_eq_sum]
        exact Finset.sum_le_sum fun i _ ↦ hfg _ (h j (mem_univ j) i)
    · exact Or.inl h
  have hM := meas_ge_le_lintegral_div (μ := P) (measurable_pwitSum hg).aemeasurable hε₀ hε
  change P {ω | ε ≤ pwitSum g ω} ≤ (∫⁻ ω, pwitSum g ω ∂P) / ε at hM
  rw [show (∫⁻ ω, pwitSum g ω ∂P) = ∫⁻ p, g p ∂(intensity d).prod μ from
    pwit_campbell hd μ g hg] at hM
  exact (measure_mono hsub).trans <| (measure_union_le _ _).trans <|
    add_le_add (measure_pwit_hit_le hd μ hs) hM

/-- The omitted weighted sum is bounded by the intensity of unusually large
marks plus the weighted length tail divided by the cutoff threshold. -/
theorem measure_pwit_weight_tail_gt_le {d β β₀ R : ℝ} (hd : 0 < d)
    (_hβ₀ : 0 < β₀) (hβ : β₀ ≤ β) (hR : 0 ≤ R)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {ε : ℝ≥0∞} (hε₀ : ε ≠ 0) (hε : ε ≠ ∞) :
    pwitBatchLaw d μ {ω | ε < pwitSum
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
  apply measure_pwit_sum_gt_le_of_envelope hd μ hg hs _ hε₀ hε
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

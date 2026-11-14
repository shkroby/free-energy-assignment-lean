import Certificate.Model
import Mathlib.Analysis.PSeries
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.StrongLaw

/-!
# Summability on the exponential arrival model

The strong law applied to spacings longer than one bounds the arrival times
from below by a positive linear function. This yields almost-sure summability
of the outgoing exponential weights for every positive pseudo-dimension.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace Certificate

/-- The spacings are strictly positive almost surely. -/
theorem ae_expSpacing_pos :
    ∀ᵐ E ∂exponentialSpacings, ∀ i, 0 < E i := by
  let : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure zero_lt_one
  have hh : expMeasure 1 (Iic 0) = 0 := by
    rw [← ofReal_cdf, cdf_expMeasure_eq zero_lt_one]
    norm_num
  apply ae_all_iff.mpr
  intro i
  rw [ae_iff]
  simp only [not_lt]
  change exponentialSpacings ((fun E : ℕ → ℝ ↦ E i) ⁻¹' Iic (0 : ℝ)) = 0
  rw [← Measure.map_apply (measurable_pi_apply i) measurableSet_Iic,
    show exponentialSpacings.map (fun E ↦ E i) = expMeasure 1 from
      Measure.infinitePi_map_eval (fun _ : ℕ ↦ expMeasure 1) i, hh]

/-- A deterministic positive lower linear rate holds eventually for almost
every realization of the exponential arrival sequence. -/
theorem ae_arrival_partial_sum_linear :
    ∃ c : ℝ, 0 < c ∧ ∀ᵐ E ∂exponentialSpacings, ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ≤ ∑ j ∈ Finset.range n, E j := by
  let : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure zero_lt_one
  let : IsProbabilityMeasure exponentialSpacings := isProbabilityMeasure_exponentialSpacings
  let I : ℝ → ℝ := (Ioi 1).indicator (fun _ ↦ 1)
  let X (i : ℕ) (E : ℕ → ℝ) : ℝ := I (E i)
  have hIm : Measurable I := measurable_const.indicator measurableSet_Ioi
  have hX (i : ℕ) : Measurable (X i) := hIm.comp (measurable_pi_apply i)
  have hI (x : ℝ) : I x ∈ Icc 0 1 := by
    by_cases h : x ∈ Ioi (1 : ℝ)
    · simp [I, h]
    · simp [I, h]
  have hXi : Integrable (X 0) exponentialSpacings :=
    memLp_one_iff_integrable.mp <|
      memLp_of_bounded (.of_forall fun (E : ℕ → ℝ) ↦ hI (E 0)) (hX 0).aestronglyMeasurable 1
  have hind : iIndepFun X exponentialSpacings :=
    iIndepFun_infinitePi (X := fun _ ↦ I) fun _ ↦ hIm
  have hmap (i : ℕ) : exponentialSpacings.map (X i) = (expMeasure 1).map I := by
    rw [show X i = I ∘ (fun E ↦ E i) from rfl, ← Measure.map_map hIm (measurable_pi_apply i)]
    rw [show exponentialSpacings.map (fun E ↦ E i) = expMeasure 1 from
      Measure.infinitePi_map_eval (fun _ : ℕ ↦ expMeasure 1) i]
  have hid (i : ℕ) : IdentDistrib (X i) (X 0) exponentialSpacings exponentialSpacings :=
    ⟨(hX i).aemeasurable, (hX 0).aemeasurable, (hmap i).trans (hmap 0).symm⟩
  let m := ∫ E, X 0 E ∂exponentialSpacings
  have hmform : m = Real.exp (-1) := by
    have hmap0 : exponentialSpacings.map (fun E ↦ E 0) = expMeasure 1 :=
      Measure.infinitePi_map_eval (fun _ : ℕ ↦ expMeasure 1) 0
    have hm := integral_map (μ := exponentialSpacings)
      (measurable_pi_apply (0 : ℕ)).aemeasurable hIm.aestronglyMeasurable
    rw [hmap0] at hm
    change (∫ E, I (E 0) ∂exponentialSpacings) = _
    rw [← hm]
    unfold I
    rw [integral_indicator measurableSet_Ioi, setIntegral_const, smul_eq_mul, mul_one]
    have hC := cdf_expMeasure_eq (r := 1) zero_lt_one 1
    rw [cdf_eq_real] at hC
    rw [show Ioi (1 : ℝ) = (Iic (1 : ℝ))ᶜ by ext t; simp,
      measureReal_compl measurableSet_Iic, probReal_univ]
    norm_num at hC
    linarith
  have hm : 0 < m := hmform ▸ Real.exp_pos _
  refine ⟨m / 2, half_pos hm, ?_⟩
  filter_upwards [ae_expSpacing_pos, strong_law_ae_real X hXi (fun _ _ ↦ hind.indepFun) hid]
    with E hE hL
  have hgood := (tendsto_order.mp hL).1 (m / 2) (by linarith)
  filter_upwards [hgood, eventually_gt_atTop (0 : ℕ)] with n hn hn0
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn0
  refine (lt_of_le_of_lt (by rfl) ((lt_div_iff₀ hn').mp hn)).le.trans ?_
  exact Finset.sum_le_sum fun i _ ↦ by
    by_cases h : E i ∈ Ioi (1 : ℝ)
    · simpa [X, I, h] using (le_of_lt h : 1 ≤ E i)
    · simpa [X, I, h] using (hE i).le

/-- A stretched exponential sampled at natural numbers is summable for every
positive exponent. -/
theorem summable_nat_stretchedExp {c p : ℝ} (hc : 0 < c) (hp : 0 < p) :
    Summable (fun n : ℕ ↦ Real.exp (-(c * (n : ℝ) ^ p))) := by
  have hPow : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ p) atTop atTop :=
    (tendsto_rpow_atTop hp).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hratio := (tendsto_exp_mul_div_rpow_atTop (2 / p) c hc).comp hPow
  have hComp : Summable (fun n : ℕ ↦ (n : ℝ) ^ (-2 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  refine hComp.of_norm_bounded_eventually_nat ?_
  filter_upwards [hratio.eventually_ge_atTop 1, eventually_gt_atTop (0 : ℕ)] with n hn hn'
  have hnp : 0 < (n : ℝ) := Nat.cast_pos.mpr hn'
  have h₂ : ((n : ℝ) ^ p) ^ (2 / p : ℝ) = (n : ℝ) ^ (2 : ℝ) := by
    rw [← Real.rpow_mul hnp.le, mul_div_cancel₀ _ hp.ne']
  change 1 ≤ Real.exp (c * (n : ℝ) ^ p) / ((n : ℝ) ^ p) ^ (2 / p : ℝ) at hn
  rw [h₂, one_le_div (Real.rpow_pos_of_pos hnp _)] at hn
  rw [Real.norm_of_nonneg (Real.exp_nonneg _), Real.exp_neg, Real.rpow_neg hnp.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos hnp _) hn

/-- The actual arrival process from the statement has finite total edge weight
almost surely at every positive temperature and pseudo-dimension. -/
theorem ae_summable_arrival_weights {d β : ℝ} (hd : 0 < d) (hβ : 0 < β) :
    ∀ᵐ E ∂exponentialSpacings, Summable (fun i ↦ Real.exp (-β * arrivalLength d E i)) := by
  obtain ⟨c, hc, hlin⟩ := ae_arrival_partial_sum_linear
  filter_upwards [hlin] with E hE
  let p := 1 / d
  have hp : 0 < p := one_div_pos.mpr hd
  let a := β * c ^ p
  have ha : 0 < a := mul_pos hβ (Real.rpow_pos_of_pos hc _)
  refine (summable_nat_stretchedExp ha hp).of_norm_bounded_eventually_nat ?_
  have hh := (tendsto_add_atTop_nat 1).eventually hE
  filter_upwards [hh] with n hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hcl : c * (n : ℝ) ≤ ∑ j ∈ Finset.range (n + 1), E j :=
    (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_succ n) hc.le).trans hn
  have hr := Real.rpow_le_rpow (mul_nonneg hc.le hn0) hcl hp.le
  rw [Real.mul_rpow hc.le hn0] at hr
  rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
  apply Real.exp_le_exp.mpr
  have hm := mul_le_mul_of_nonneg_left hr hβ.le
  change -β * ((∑ j ∈ Finset.range (n + 1), E j) ^ p) ≤ -(a * (n : ℝ) ^ p)
  dsimp [a]
  nlinarith only [hm]

/-- Bounded nonnegative marks on the same arrivals yield an almost-sure
summable marked series. -/
theorem ae_summable_cavityTerm_of_bounded_marks {d β M : ℝ} (hd : 0 < d) (hβ : 0 < β)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hM : ∀ᵐ x ∂μ, x ∈ Icc 0 M) :
    ∀ᵐ ω ∂markedSpacings μ, Summable (cavityTerm β d ω) := by
  let : IsProbabilityMeasure exponentialSpacings := isProbabilityMeasure_exponentialSpacings
  have hmarks : ∀ᵐ marks ∂Measure.infinitePi (fun _ : ℕ ↦ μ), ∀ i, marks i ∈ Icc 0 M := by
    refine ae_all_iff.mpr fun i ↦ ?_
    have hmap := Measure.infinitePi_map_eval (fun _ : ℕ ↦ μ) i
    have hm : AEMeasurable (fun marks : ℕ → ℝ ↦ marks i)
        (Measure.infinitePi (fun _ : ℕ ↦ μ)) := (measurable_pi_apply i).aemeasurable
    exact (ae_map_iff hm (measurableSet_Icc (a := (0 : ℝ)) (b := M))).mp (by rwa [hmap])
  have hfst : ∀ᵐ ω ∂markedSpacings μ,
      Summable (fun i ↦ Real.exp (-β * arrivalLength d ω.1 i)) :=
    (Measure.quasiMeasurePreserving_fst (μ := exponentialSpacings)
      (ν := Measure.infinitePi (fun _ : ℕ ↦ μ))).tendsto_ae.eventually
      (ae_summable_arrival_weights hd hβ)
  have hsnd : ∀ᵐ ω ∂markedSpacings μ, ∀ i, ω.2 i ∈ Icc 0 M :=
    (Measure.quasiMeasurePreserving_snd (μ := exponentialSpacings)
      (ν := Measure.infinitePi (fun _ : ℕ ↦ μ))).tendsto_ae.eventually hmarks
  filter_upwards [hfst, hsnd] with ω hw hm
  refine (hw.mul_right M).of_nonneg_of_le ?_ ?_
  · exact fun i ↦ mul_nonneg (Real.exp_nonneg _) (hm i).1
  · exact fun i ↦ mul_le_mul_of_nonneg_left (hm i).2 (Real.exp_nonneg _)

/-- The actual weighted series is almost-everywhere measurable whenever it is
almost surely summable. -/
theorem aemeasurable_cavityMap_of_summable {β d : ℝ} (μ : Measure ℝ)
    (hs : ∀ᵐ ω ∂markedSpacings μ, Summable (cavityTerm β d ω)) :
    AEMeasurable (cavityMap β d) (markedSpacings μ) := by
  have hl : AEMeasurable (fun ω ↦ ∑' i, cavityTerm β d ω i) (markedSpacings μ) := by
    apply aemeasurable_of_tendsto_metrizable_ae' (f := fun n ω ↦ ∑ i ∈ Finset.range n, cavityTerm β d ω i)
    · intro n
      apply Measurable.aemeasurable
      unfold cavityTerm arrivalLength
      fun_prop
    · exact hs.mono fun _ h ↦ h.hasSum.tendsto_sum_nat
  exact hl.inv

end Certificate

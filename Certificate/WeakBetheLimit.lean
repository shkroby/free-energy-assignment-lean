import Certificate.WeakExpectations
import Certificate.BetheEdgeTail
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Weak convergence in the Bethe formula

The scaled log laws determine both integrands. A common second-moment
bound gives convergence of the vertex term and of the edge term at each
fixed length. A common stretched upper tail on the sum of the scaled log
messages supplies the integrable edge envelope.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace Certificate

private theorem measurable_scaledLog (β : ℝ) : Measurable (fun h : ℝ => Real.log h / β) := by
  fun_prop

/-- The law of the inverse-temperature-scaled log message. -/
noncomputable def scaledLogLaw (β : ℝ) (μ : ProbabilityMeasure ℝ) : ProbabilityMeasure ℝ :=
  μ.map (measurable_scaledLog β).aemeasurable

private theorem continuous_add_pair : Continuous (fun p : ℝ × ℝ => p.1 + p.2) := by fun_prop

/-- The law of the sum of two independent scaled log messages. -/
noncomputable def scaledLogSumLaw (ν : ProbabilityMeasure ℝ) : ProbabilityMeasure ℝ :=
  (ν.prod ν).map continuous_add_pair.measurable.aemeasurable

private theorem tendsto_scaledLogSumLaw {ν : ℕ → ProbabilityMeasure ℝ}
    {ν₀ : ProbabilityMeasure ℝ} (h : Tendsto ν atTop (𝓝 ν₀)) :
    Tendsto (fun n => scaledLogSumLaw (ν n)) atTop (𝓝 (scaledLogSumLaw ν₀)) := by
  have hprod : Tendsto (fun n => (ν n).prod (ν n)) atTop (𝓝 (ν₀.prod ν₀)) :=
    ProbabilityMeasure.continuous_prod.continuousAt.tendsto.comp (h.prodMk_nhds h)
  exact (ProbabilityMeasure.continuous_map continuous_add_pair).continuousAt.tendsto.comp hprod

private noncomputable def edgeSoftplus (β x s : ℝ) : ℝ :=
  Real.log (1 + Real.exp (β * (s - x)))

private theorem continuous_edgeSoftplus (β x : ℝ) : Continuous (edgeSoftplus β x) := by
  unfold edgeSoftplus
  exact (continuous_const.add (Real.continuous_exp.comp
    (continuous_const.mul (continuous_id.sub continuous_const)))).log
    (fun s => ne_of_gt (add_pos zero_lt_one (Real.exp_pos _)))

private theorem edgeSoftplus_nonneg (β x s : ℝ) : 0 ≤ edgeSoftplus β x s := by
  unfold edgeSoftplus
  exact Real.log_nonneg (le_add_of_nonneg_right (Real.exp_nonneg _))

private theorem edgeSoftplus_le {β x : ℝ} (hβ : 0 ≤ β) (hx : 0 ≤ x) (s : ℝ) :
    edgeSoftplus β x s ≤ Real.log 2 + β * max s 0 := by
  have hsm : s - x ≤ max s 0 := (sub_le_self s hx).trans (le_max_left _ _)
  have hE := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsm hβ)
  have hE' := Real.one_le_exp (mul_nonneg hβ (le_max_right s 0))
  unfold edgeSoftplus
  calc
    _ ≤ Real.log (2 * Real.exp (β * max s 0)) :=
      Real.log_le_log (by positivity) (by linarith)
    _ = _ := by rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp]

private theorem integral_log_eq_scaled {β : ℝ} (hβ : 0 < β) (μ : ProbabilityMeasure ℝ) :
    (∫ h, Real.log h ∂(μ : Measure ℝ)) =
      β * ∫ s, s ∂(scaledLogLaw β μ : Measure ℝ) := by
  rw [scaledLogLaw, ProbabilityMeasure.toMeasure_map]
  have hMap : (∫ s : ℝ, s ∂(μ : Measure ℝ).map (fun h => Real.log h / β)) =
      ∫ h : ℝ, Real.log h / β ∂(μ : Measure ℝ) :=
    integral_map (measurable_scaledLog β).aemeasurable
      (show Measurable (fun s : ℝ => s) from measurable_id).aestronglyMeasurable
  rw [hMap, ← integral_const_mul]
  apply integral_congr_ae
  exact .of_forall fun s => by
    change Real.log s = β * (Real.log s / β)
    field_simp [hβ.ne']

private theorem edgeLogCorrection_eq_scaledSoftplus {β : ℝ} (hβ : 0 < β)
    (μ : ProbabilityMeasure ℝ) (hμ : (μ : Measure ℝ) (Ioi 0) = 1) (x : ℝ) :
    edgeLogCorrection β (μ : Measure ℝ) x =
      ∫ s, edgeSoftplus β x s ∂(scaledLogSumLaw (scaledLogLaw β μ) : Measure ℝ) := by
  have hm := measurable_scaledLog β
  have he := (continuous_edgeSoftplus β x).measurable
  simp only [scaledLogSumLaw, scaledLogLaw, ProbabilityMeasure.toMeasure_map,
    ProbabilityMeasure.toMeasure_prod]
  rw [Measure.map_prod_map _ _ hm hm]
  rw [integral_map continuous_add_pair.measurable.aemeasurable he.aestronglyMeasurable]
  have hePair : Measurable (fun p : ℝ × ℝ => edgeSoftplus β x (p.1 + p.2)) :=
    he.comp continuous_add_pair.measurable
  rw [integral_map (hm.prodMap hm).aemeasurable hePair.aestronglyMeasurable]
  have hp : ∀ᵐ h ∂(μ : Measure ℝ), 0 < h :=
    (mem_ae_iff_prob_eq_one (measurableSet_Ioi (a := (0 : ℝ)))).mpr hμ
  have hf : ∀ᵐ p ∂((μ : Measure ℝ).prod (μ : Measure ℝ)), 0 < p.1 :=
    measurePreserving_fst.quasiMeasurePreserving.tendsto_ae.eventually hp
  have hs : ∀ᵐ p ∂((μ : Measure ℝ).prod (μ : Measure ℝ)), 0 < p.2 :=
    measurePreserving_snd.quasiMeasurePreserving.tendsto_ae.eventually hp
  apply integral_congr_ae
  filter_upwards [hf, hs] with p hp₁ hp₂
  change Real.log (1 + Real.exp (-β * x) * p.1 * p.2) =
    Real.log (1 + Real.exp (β * ((Real.log p.1 / β + Real.log p.2 / β) - x)))
  have hE : β * (Real.log p.1 / β + Real.log p.2 / β - x) =
      -β * x + Real.log p.1 + Real.log p.2 := by
    field_simp [hβ.ne']
    ring
  rw [hE, Real.exp_add, Real.exp_add, Real.exp_log hp₁, Real.exp_log hp₂]

private theorem ae_intensity_nonneg (d : ℝ) : ∀ᵐ x ∂intensity d, 0 ≤ x := by
  unfold intensity
  exact (ae_withDensity_iff (by fun_prop)).mpr <|
    (ae_restrict_mem measurableSet_Ioi).mono (fun _ h _ => le_of_lt h)

/-- Convergence of the Bethe formula from weak convergence of the
scaled log laws, with common second moments and a stretched upper tail
for the sum of two independent scaled log messages. -/
theorem tendsto_bethePressure_of_scaledLogLaw {β d c K B M : ℝ}
    (hβ : 0 < β) (hd : 0 < d) (hc : 0 < c) (hK : 0 ≤ K) (hB : 0 ≤ B) (hM : 0 ≤ M)
    {μ : ℕ → ProbabilityMeasure ℝ} {μ₀ : ProbabilityMeasure ℝ}
    (hμ : ∀ n, (μ n : Measure ℝ) (Ioi 0) = 1) (hμ₀ : (μ₀ : Measure ℝ) (Ioi 0) = 1)
    (hweak : Tendsto (fun n => scaledLogLaw β (μ n)) atTop (𝓝 (scaledLogLaw β μ₀)))
    (hlog : ∀ q ∈ insert μ₀ (range μ), MemLp id 2 (scaledLogLaw β q : Measure ℝ))
    (hlogM : ∀ q ∈ insert μ₀ (range μ),
      (∫ s, s^2 ∂(scaledLogLaw β q : Measure ℝ)) ≤ B)
    (hsum : ∀ q ∈ insert μ₀ (range μ),
      MemLp (fun s : ℝ => Real.log 2 + β * max s 0) 2
        (scaledLogSumLaw (scaledLogLaw β q) : Measure ℝ))
    (hsumM : ∀ q ∈ insert μ₀ (range μ),
      (∫ s, (Real.log 2 + β * max s 0)^2 ∂(scaledLogSumLaw (scaledLogLaw β q) : Measure ℝ)) ≤ M)
    (htail : ∀ n s, 0 ≤ s → (scaledLogSumLaw (scaledLogLaw β (μ n)) : Measure ℝ).real (Ioi s) ≤
        K * Real.exp (-c * s^d)) :
    Tendsto (fun n => bethePressure β d (μ n : Measure ℝ)) atTop
      (𝓝 (bethePressure β d (μ₀ : Measure ℝ))) := by
  have hq (n : ℕ) : μ n ∈ insert μ₀ (range μ) := mem_insert_of_mem _ (mem_range_self n)
  have hq₀ : μ₀ ∈ insert μ₀ (range μ) := mem_insert _ _
  have hv := tendsto_integral_of_weak_of_secondMoment hweak continuous_id
    (fun n => hlog _ (hq n)) (hlog _ hq₀) hB (fun n => hlogM _ (hq n)) (hlogM _ hq₀)
  have hvert : Tendsto (fun n => ∫ h, Real.log h ∂(μ n : Measure ℝ)) atTop
      (𝓝 (∫ h, Real.log h ∂(μ₀ : Measure ℝ))) := by
    simp_rw [integral_log_eq_scaled hβ]
    exact hv.const_mul β
  let D := M ^ (1 / 2 : ℝ) * K ^ (1 / 2 : ℝ)
  let c' := c / 2 / (2 : ℝ)^d
  have hc' : 0 < c' := by dsimp [c']; positivity
  apply tendsto_bethePressure hvert (integrable_edge_envelope (K := D) hd hβ hc')
  · intro n
    have hj : Measurable (fun p : ℝ × (ℝ × ℝ) =>
        Real.log (1 + Real.exp (-β * p.1) * p.2.1 * p.2.2)) := by fun_prop
    exact hj.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
  · intro n
    filter_upwards [ae_intensity_nonneg d] with x hx
    let ν := scaledLogSumLaw (scaledLogLaw β (μ n))
    have hE := integral_softplus_le_of_tail hβ hK hx (hsum _ (hq n))
      (htail n (x/2) (div_nonneg hx (by norm_num)))
    rw [edgeLogCorrection_eq_scaledSoftplus hβ _ (hμ n)]
    have hnonneg : 0 ≤ ∫ s, edgeSoftplus β x s ∂(ν : Measure ℝ) :=
      integral_nonneg (edgeSoftplus_nonneg β x)
    rw [Real.norm_of_nonneg hnonneg]
    refine hE.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)))
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hK _)
    exact Real.rpow_le_rpow (integral_nonneg (fun _ => sq_nonneg _)) (hsumM _ (hq n)) (by norm_num)
  · filter_upwards [ae_intensity_nonneg d] with x hx
    simp_rw [edgeLogCorrection_eq_scaledSoftplus hβ _ (hμ _)]
    rw [edgeLogCorrection_eq_scaledSoftplus hβ _ hμ₀]
    have hm (q : ProbabilityMeasure ℝ) (hq' : q ∈ insert μ₀ (range μ)) :
        MemLp (edgeSoftplus β x) 2 (scaledLogSumLaw (scaledLogLaw β q) : Measure ℝ) :=
      (hsum _ hq').of_le (continuous_edgeSoftplus β x).measurable.aestronglyMeasurable
        (.of_forall fun s => by
          rw [Real.norm_of_nonneg (edgeSoftplus_nonneg β x s),
            Real.norm_of_nonneg (add_nonneg (Real.log_nonneg (by norm_num))
              (mul_nonneg hβ.le (le_max_right s 0)))]
          exact edgeSoftplus_le hβ.le hx s)
    have hM' (q : ProbabilityMeasure ℝ) (hq' : q ∈ insert μ₀ (range μ)) :
        (∫ s, edgeSoftplus β x s ^ 2 ∂(scaledLogSumLaw (scaledLogLaw β q) : Measure ℝ)) ≤ M := by
      apply le_trans _ (hsumM q hq')
      have hSq {f : ℝ → ℝ} {m : Measure ℝ} (hF : MemLp f 2 m) :
          Integrable (fun s => f s ^ 2) m := by
        simpa only [Real.norm_eq_abs, sq_abs] using hF.integrable_norm_pow (p := 2) (by decide)
      exact integral_mono (hSq (hm _ hq')) (hSq (hsum _ hq'))
        (fun s => pow_le_pow_left₀ (edgeSoftplus_nonneg _ _ _) (edgeSoftplus_le hβ.le hx s) 2)
    exact tendsto_integral_of_weak_of_secondMoment (tendsto_scaledLogSumLaw hweak)
      (continuous_edgeSoftplus β x) (fun n => hm _ (hq n)) (hm _ hq₀) hM
      (fun n => hM' _ (hq n)) (hM' _ hq₀)

end Certificate

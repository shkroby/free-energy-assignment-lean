import Certificate.HardLogMoment
import Certificate.BetheEdgeTail
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Integrability of the hard Bethe edge correction

The sum of two independent scaled log messages has a stretched upper
tail and a second moment. Applied to the edge softplus, these give an
integrable envelope for every positive pseudodimension and inverse
temperature.
-/

open Filter MeasureTheory Set
open scoped ENNReal

namespace Certificate

private noncomputable def edgeScaledLogSum (β : ℝ) (p : ℝ × ℝ) : ℝ :=
  (Real.log p.1 + Real.log p.2) / β

private theorem measurable_edgeScaledLogSum (β : ℝ) : Measurable (edgeScaledLogSum β) := by
  unfold edgeScaledLogSum
  fun_prop

private noncomputable def edgeScaledLogLaw (β : ℝ) (μ : Measure ℝ) : Measure ℝ :=
  (μ.prod μ).map (edgeScaledLogSum β)

private theorem ae_hard_positive_pair {β d : ℝ} {μ : Measure ℝ} (h : IsCavityLaw β d μ) :
    ∀ᵐ p ∂(μ.prod μ), 0 < p.1 ∧ 0 < p.2 := by
  let : IsProbabilityMeasure μ := h.1
  have hp : ∀ᵐ x ∂μ, 0 < x :=
    (mem_ae_iff_prob_eq_one (measurableSet_Ioi (a := (0 : ℝ)))).mpr h.2.1
  have hfst : ∀ᵐ p ∂(μ.prod μ), 0 < p.1 :=
    (measurePreserving_fst (μ := μ) (ν := μ)).quasiMeasurePreserving.tendsto_ae.eventually hp
  have hsnd : ∀ᵐ p ∂(μ.prod μ), 0 < p.2 :=
    (measurePreserving_snd (μ := μ) (ν := μ)).quasiMeasurePreserving.tendsto_ae.eventually hp
  exact hfst.and hsnd

private theorem edgeScaledLogLaw_memLp {β d : ℝ} (hd : 0 < d) (hβ : 0 < β)
    {μ : Measure ℝ} (h : IsCavityLaw β d μ) : MemLp id 2 (edgeScaledLogLaw β μ) := by
  let : IsProbabilityMeasure μ := h.1
  have hlog := hard_cavity_log_memLp_two hd hβ h
  have hf := hlog.comp_measurePreserving (measurePreserving_fst (μ := μ) (ν := μ))
  have hs := hlog.comp_measurePreserving (measurePreserving_snd (μ := μ) (ν := μ))
  have hm : MemLp (edgeScaledLogSum β) 2 (μ.prod μ) := by
    have hm' := (hf.add hs).const_mul β⁻¹
    change MemLp (fun p : ℝ × ℝ => β⁻¹ * (Real.log p.1 + Real.log p.2)) 2 (μ.prod μ) at hm'
    have hsums : edgeScaledLogSum β = (fun p : ℝ × ℝ =>
        β⁻¹ * (Real.log p.1 + Real.log p.2)) := by
      funext p
      change (Real.log p.1 + Real.log p.2) / β = β⁻¹ * (Real.log p.1 + Real.log p.2)
      exact div_eq_inv_mul (Real.log p.1 + Real.log p.2) β
    exact hsums ▸ hm'
  exact (memLp_map_measure_iff measurable_id.aestronglyMeasurable
    (measurable_edgeScaledLogSum β).aemeasurable).mpr hm

private noncomputable def edgeHardSoftplus (β x s : ℝ) : ℝ :=
  Real.log (1 + Real.exp (β * (s - x)))

private theorem softplus_le_log_two_add_abs (u : ℝ) :
    Real.log (1 + Real.exp u) ≤ Real.log 2 + |u| := by
  have h₁ : 1 ≤ Real.exp |u| := Real.one_le_exp (abs_nonneg _)
  have h₂ : Real.exp u ≤ Real.exp |u| := Real.exp_le_exp.mpr (le_abs_self _)
  calc
    _ ≤ Real.log (2 * Real.exp |u|) :=
      Real.log_le_log (by positivity) (by linarith)
    _ = _ := by rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp]

private theorem edgeHardSoftplus_integrable (β x : ℝ) {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hm : MemLp (id : ℝ → ℝ) 2 ν) : Integrable (edgeHardSoftplus β x) ν := by
  have hi := hm.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have he := (integrable_const (Real.log 2)).add ((hi.sub (integrable_const x)).const_mul β).norm
  have hmeas : Measurable (edgeHardSoftplus β x) := by unfold edgeHardSoftplus; fun_prop
  refine he.mono' hmeas.aestronglyMeasurable (.of_forall fun s => ?_)
  change ‖Real.log (1 + Real.exp (β * (s - x)))‖ ≤ Real.log 2 + ‖β * (s - x)‖
  have hn : 0 ≤ Real.log (1 + Real.exp (β * (s - x))) :=
    Real.log_nonneg (le_add_of_nonneg_right (Real.exp_nonneg _))
  rw [Real.norm_of_nonneg hn, Real.norm_eq_abs]
  exact softplus_le_log_two_add_abs (β * (s - x))

private theorem edgeHardSoftplus_ae {β d : ℝ} (hβ : 0 < β)
    {μ : Measure ℝ} (h : IsCavityLaw β d μ) (x : ℝ) :
    (fun p : ℝ × ℝ => Real.log (1 + Real.exp (-β * x) * p.1 * p.2)) =ᵐ[μ.prod μ]
      edgeHardSoftplus β x ∘ edgeScaledLogSum β := by
  filter_upwards [ae_hard_positive_pair h] with p hp
  have he : β * ((Real.log p.1 + Real.log p.2) / β - x) =
      -β * x + Real.log p.1 + Real.log p.2 := by
    field_simp [hβ.ne']
    ring
  simp only [Function.comp_apply, edgeHardSoftplus, edgeScaledLogSum, he,
    Real.exp_add, Real.exp_log hp.1, Real.exp_log hp.2]

/-- The edge integrand is integrable over the two independent hard messages
for every fixed length. -/
theorem hard_edge_integrand_integrable {β d : ℝ} (hd : 0 < d) (hβ : 0 < β)
    {μ : Measure ℝ} (h : IsCavityLaw β d μ) (x : ℝ) :
    Integrable (fun p : ℝ × ℝ => Real.log (1 + Real.exp (-β * x) * p.1 * p.2)) (μ.prod μ) := by
  let : IsProbabilityMeasure μ := h.1
  let : IsProbabilityMeasure (edgeScaledLogLaw β μ) :=
    Measure.isProbabilityMeasure_map (measurable_edgeScaledLogSum β).aemeasurable
  have hi := edgeHardSoftplus_integrable β x (edgeScaledLogLaw_memLp hd hβ h)
  exact (hi.comp_measurable (measurable_edgeScaledLogSum β)).congr
    (edgeHardSoftplus_ae hβ h x).symm

private theorem edgeLogCorrection_as_softplus {β d : ℝ} (hd : 0 < d) (hβ : 0 < β)
    {μ : Measure ℝ} (h : IsCavityLaw β d μ) (x : ℝ) :
    edgeLogCorrection β μ x = ∫ s, edgeHardSoftplus β x s ∂edgeScaledLogLaw β μ := by
  let : IsProbabilityMeasure μ := h.1
  let : IsProbabilityMeasure (edgeScaledLogLaw β μ) :=
    Measure.isProbabilityMeasure_map (measurable_edgeScaledLogSum β).aemeasurable
  have hi := edgeHardSoftplus_integrable β x (edgeScaledLogLaw_memLp hd hβ h)
  exact (integral_congr_ae (edgeHardSoftplus_ae hβ h x)).trans
    (integral_map (measurable_edgeScaledLogSum β).aemeasurable hi.aestronglyMeasurable).symm

private theorem edgeScaledLogLaw_tail {β d : ℝ} (hd : 0 < d) (hβ : 0 < β)
    {μ : Measure ℝ} (h : IsCavityLaw β d μ) :
    ∃ K ≥ 0, ∀ s ≥ 0, (edgeScaledLogLaw β μ).real (Ioi s) ≤
      K * Real.exp (-(1 / (2 * (4 : ℝ)^d)) * s^d) := by
  let : IsProbabilityMeasure μ := h.1
  obtain ⟨K, hK, hTail⟩ := hard_cavity_log_upperTail hd hβ h
  have hK₀ : 0 ≤ K := zero_le_one.trans hK
  refine ⟨2 * K, mul_nonneg (by norm_num) hK₀, fun s hs => ?_⟩
  let T := Ioi (Real.exp (β * (s / 2)))
  have hsubset : (μ.prod μ) (edgeScaledLogSum β ⁻¹' Ioi s) ≤
      (μ.prod μ) (Prod.fst ⁻¹' T ∪ Prod.snd ⁻¹' T) := by
    apply measure_mono_ae
    filter_upwards [ae_hard_positive_pair h] with p hp hlarge
    have hsum : s * β < Real.log p.1 + Real.log p.2 := (lt_div_iff₀ hβ).mp hlarge
    by_cases hleft : β * (s / 2) < Real.log p.1
    · exact Or.inl ((Real.lt_log_iff_exp_lt hp.1).mp hleft)
    · exact Or.inr ((Real.lt_log_iff_exp_lt hp.2).mp
        (by linarith only [hsum, le_of_not_gt hleft]))
  have hT : MeasurableSet T := measurableSet_Ioi
  have hf : (μ.prod μ) (Prod.fst ⁻¹' T) = μ T := by
    rw [← Measure.map_apply measurable_fst hT, measurePreserving_fst.map_eq]
  have hg : (μ.prod μ) (Prod.snd ⁻¹' T) = μ T := by
    rw [← Measure.map_apply measurable_snd hT, measurePreserving_snd.map_eq]
  have he : ((s/2)/2)^d/2 = (1 / (2 * (4 : ℝ)^d)) * s^d := by
    rw [show (s/2)/2 = s/4 by ring, Real.div_rpow hs (by norm_num)]
    field_simp [(Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 4) d).ne']
  let a := K * Real.exp (-(((s/2)/2)^d/2))
  have ha : 0 ≤ a := mul_nonneg hK₀ (Real.exp_nonneg _)
  have hν : (edgeScaledLogLaw β μ) (Ioi s) ≤ ENNReal.ofReal (a + a) := by
    rw [edgeScaledLogLaw, Measure.map_apply (measurable_edgeScaledLogSum β) measurableSet_Ioi,
      ENNReal.ofReal_add ha ha]
    apply hsubset.trans ((measure_union_le _ _).trans ?_)
    rw [hf, hg]
    have ht := hTail (s/2) (div_nonneg hs (by norm_num))
    exact add_le_add ht ht
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hν
  rw [ENNReal.toReal_ofReal (add_nonneg ha ha)] at hr
  dsimp [a] at hr
  rw [he] at hr
  rw [neg_mul]
  simpa only [measureReal_def, two_mul, add_mul] using hr

/-- The hard Bethe edge correction has a finite absolute integral against
the full pseudodimensional intensity. -/
theorem hard_edgeLogCorrection_integrable {β d : ℝ} (hd : 0 < d) (hβ : 0 < β)
    {μ : Measure ℝ} (h : IsCavityLaw β d μ) :
    Integrable (edgeLogCorrection β μ) (intensity d) := by
  let : IsProbabilityMeasure μ := h.1
  let ν := edgeScaledLogLaw β μ
  let : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map (measurable_edgeScaledLogSum β).aemeasurable
  obtain ⟨K, hK, hTail⟩ := edgeScaledLogLaw_tail hd hβ h
  have hId : MemLp (id : ℝ → ℝ) 2 ν := edgeScaledLogLaw_memLp hd hβ h
  have hMax : MemLp (fun s : ℝ => max s 0) 2 ν :=
    hId.of_le (by fun_prop : Measurable (fun s : ℝ => max s 0)).aestronglyMeasurable
      (.of_forall fun s => by
        simp only [id_eq, Real.norm_eq_abs, abs_of_nonneg (le_max_right s 0)]
        exact max_le (le_abs_self _) (abs_nonneg _))
  have hMom : MemLp (fun s : ℝ => Real.log 2 + β * max s 0) 2 ν :=
    (memLp_const (Real.log 2)).add (hMax.const_mul β)
  let C := ((∫ s, (Real.log 2 + β * max s 0) ^ (2 : ℕ) ∂ν) ^ (1 / 2 : ℝ)) *
    K ^ (1 / 2 : ℝ)
  let c := (1 / (2 * (4 : ℝ)^d) : ℝ) / 2 / (2 : ℝ)^d
  have hc : 0 < c := by dsimp [c]; positivity
  have hsimple : Integrable (fun x : ℝ => Real.exp (-((β / 2) * x))) (intensity d) := by
    refine ⟨(by fun_prop : Measurable _).aestronglyMeasurable, hasFiniteIntegral_iff_enorm.mpr ?_⟩
    simp_rw [Real.enorm_eq_ofReal (Real.exp_nonneg _)]
    exact lintegral_exp_intensity_lt_top hd (half_pos hβ)
  have hstretch : Integrable (fun x : ℝ => Real.exp (-c * x^d)) (intensity d) := by
    refine ⟨(by fun_prop : Measurable _).aestronglyMeasurable, hasFiniteIntegral_iff_enorm.mpr ?_⟩
    simp_rw [Real.enorm_eq_ofReal (Real.exp_nonneg _)]
    exact lintegral_stretched_intensity_lt_top hd hc
  have hmeas : StronglyMeasurable (edgeLogCorrection β μ) := by
    have hj : Measurable (fun p : ℝ × (ℝ × ℝ) =>
        Real.log (1 + Real.exp (-β * p.1) * p.2.1 * p.2.2)) := by fun_prop
    exact hj.stronglyMeasurable.integral_prod_right'
  have hpos : ∀ᵐ x ∂intensity d, 0 < x := by
    apply ae_iff.mpr
    have he : {x : ℝ | ¬ 0 < x} = Iic 0 := by ext x; simp
    rw [he, intensity_Iic_zero]
  refine (hsimple.add (hstretch.const_mul C)).mono' hmeas.aestronglyMeasurable ?_
  filter_upwards [hpos] with x hx
  have hnonneg : 0 ≤ ∫ s, edgeHardSoftplus β x s ∂edgeScaledLogLaw β μ :=
    integral_nonneg fun s => by
      unfold edgeHardSoftplus
      exact Real.log_nonneg (le_add_of_nonneg_right (Real.exp_nonneg _))
  rw [edgeLogCorrection_as_softplus hd hβ h x, Real.norm_of_nonneg hnonneg]
  have he : -β * x / 2 = -((β / 2) * x) := by ring
  have hb := integral_softplus_le_of_tail hβ hK hx.le hMom (hTail (x/2) (div_nonneg hx.le (by norm_num)))
  rw [he] at hb
  exact hb

end Certificate

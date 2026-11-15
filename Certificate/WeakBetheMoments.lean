import Certificate.WeakBetheLimit
import Certificate.WeakReciprocal
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Bethe convergence from one-message bounds

Both the second moment and the stretched upper tail of a sum of two
independent scaled logs follow from their one-message bounds.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace Certificate

private theorem integrable_sq_of_memLp {α : Type*} [MeasurableSpace α]
    {m : Measure α} {f : α → ℝ} (hf : MemLp f 2 m) :
    Integrable (fun a => f a ^ 2) m := by
  simpa only [Real.norm_eq_abs, sq_abs] using hf.integrable_norm_pow (p := 2) (by decide)

private theorem sumLog_memLp (ν : ProbabilityMeasure ℝ) (hν : MemLp id 2 (ν : Measure ℝ)) :
    MemLp id 2 (scaledLogSumLaw ν : Measure ℝ) := by
  let P := (ν : Measure ℝ).prod (ν : Measure ℝ)
  have hfst : MemLp Prod.fst 2 P := hν.comp_measurePreserving measurePreserving_fst
  have hsnd : MemLp Prod.snd 2 P := hν.comp_measurePreserving measurePreserving_snd
  have hm : Measurable (fun p : ℝ × ℝ => p.1 + p.2) := by fun_prop
  change MemLp id 2 (P.map (fun p : ℝ × ℝ => p.1 + p.2))
  exact (memLp_map_measure_iff measurable_id.aestronglyMeasurable hm.aemeasurable).mpr
    (hfst.add hsnd)

private theorem sumLog_secondMoment (ν : ProbabilityMeasure ℝ) (hν : MemLp id 2 (ν : Measure ℝ))
    {B : ℝ} (hB : (∫ s : ℝ, s^2 ∂(ν : Measure ℝ)) ≤ B) :
    (∫ s, s^2 ∂(scaledLogSumLaw ν : Measure ℝ)) ≤ 4 * B := by
  let P := (ν : Measure ℝ).prod (ν : Measure ℝ)
  have hfst : MemLp Prod.fst 2 P := hν.comp_measurePreserving measurePreserving_fst
  have hsnd : MemLp Prod.snd 2 P := hν.comp_measurePreserving measurePreserving_snd
  have hsum : MemLp (fun p : ℝ × ℝ => p.1 + p.2) 2 P := hfst.add hsnd
  have hmq : Measurable (fun s : ℝ => s^2) := by fun_prop
  have hm : Measurable (fun p : ℝ × ℝ => p.1 + p.2) := by fun_prop
  have hf := integrable_sq_of_memLp hfst
  have hs := integrable_sq_of_memLp hsnd
  have hF : (∫ p, p.1^2 ∂P) = ∫ s : ℝ, s^2 ∂(ν : Measure ℝ) := by
    have hmap := integral_map (μ := P) measurable_fst.aemeasurable hmq.aestronglyMeasurable
    rw [(measurePreserving_fst (μ := (ν : Measure ℝ)) (ν := (ν : Measure ℝ))).map_eq] at hmap
    exact hmap.symm
  have hS : (∫ p, p.2^2 ∂P) = ∫ s : ℝ, s^2 ∂(ν : Measure ℝ) := by
    have hmap := integral_map (μ := P) measurable_snd.aemeasurable hmq.aestronglyMeasurable
    rw [(measurePreserving_snd (μ := (ν : Measure ℝ)) (ν := (ν : Measure ℝ))).map_eq] at hmap
    exact hmap.symm
  change (∫ s, s^2 ∂P.map (fun p : ℝ × ℝ => p.1 + p.2)) ≤ 4 * B
  rw [integral_map hm.aemeasurable hmq.aestronglyMeasurable]
  calc
    _ ≤ ∫ p, (2 * p.1^2 + 2 * p.2^2) ∂P :=
      integral_mono (integrable_sq_of_memLp hsum) ((hf.const_mul 2).add (hs.const_mul 2))
        (fun p => by nlinarith [sq_nonneg (p.1-p.2)])
    _ = 2 * (∫ s : ℝ, s^2 ∂(ν : Measure ℝ)) + 2 * (∫ s : ℝ, s^2 ∂(ν : Measure ℝ)) := by
      rw [integral_add (hf.const_mul 2) (hs.const_mul 2), integral_const_mul,
        integral_const_mul, hF, hS]
    _ ≤ _ := by linarith

private theorem majorant_memLp {β : ℝ} (ν : ProbabilityMeasure ℝ)
    (hν : MemLp id 2 (ν : Measure ℝ)) :
    MemLp (fun s : ℝ => Real.log 2 + β * max s 0) 2 (scaledLogSumLaw ν : Measure ℝ) := by
  have hMax : MemLp (fun s : ℝ => max s 0) 2 (scaledLogSumLaw ν : Measure ℝ) :=
    (sumLog_memLp ν hν).of_le (by fun_prop : Measurable (fun s : ℝ => max s 0)).aestronglyMeasurable
      (.of_forall fun s => by
        simp only [id_eq, Real.norm_eq_abs, abs_of_nonneg (le_max_right s 0)]
        exact max_le (le_abs_self _) (abs_nonneg _))
  exact (memLp_const (Real.log 2)).add (hMax.const_mul β)

private theorem majorant_secondMoment (β : ℝ) (ν : ProbabilityMeasure ℝ)
    (hν : MemLp id 2 (ν : Measure ℝ)) {B : ℝ} (hB : (∫ s : ℝ, s^2 ∂(ν : Measure ℝ)) ≤ B) :
    (∫ s, (Real.log 2 + β * max s 0)^2 ∂(scaledLogSumLaw ν : Measure ℝ)) ≤
      2 * (Real.log 2)^2 + 8 * β^2 * B := by
  have hi : Integrable (fun s : ℝ => s^2) (scaledLogSumLaw ν : Measure ℝ) :=
    integrable_sq_of_memLp (sumLog_memLp ν hν)
  have hmax (s : ℝ) : (max s 0)^2 ≤ s^2 := by
    by_cases h : 0 ≤ s
    · rw [max_eq_left h]
    · rw [max_eq_right (le_of_not_ge h), zero_pow (by decide : (2 : ℕ) ≠ 0)]
      exact sq_nonneg s
  calc
    _ ≤ ∫ s, (2 * (Real.log 2)^2 + (2 * β^2) * s^2) ∂(scaledLogSumLaw ν : Measure ℝ) :=
      integral_mono (integrable_sq_of_memLp (majorant_memLp ν hν))
        ((integrable_const _).add (hi.const_mul _)) (fun s => by
          have hh := mul_le_mul_of_nonneg_left (hmax s) (sq_nonneg β)
          nlinarith only [hh, sq_nonneg (Real.log 2 - β * max s 0)])
    _ = 2 * (Real.log 2)^2 + (2 * β^2) *
        (∫ s, s^2 ∂(scaledLogSumLaw ν : Measure ℝ)) := by
      rw [integral_add (integrable_const _) (hi.const_mul _), integral_const,
        probReal_univ, one_smul, integral_const_mul]
    _ ≤ _ := by
      rw [show 8 * β^2 * B = (2 * β^2) * (4 * B) by ring]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (sumLog_secondMoment ν hν hB)
        (mul_nonneg (by norm_num) (sq_nonneg β)))

private theorem sumLog_upperTail (ν : ProbabilityMeasure ℝ) {c d K : ℝ}
    (h : ∀ s, 0 ≤ s → (ν : Measure ℝ).real (Ioi s) ≤ K * Real.exp (-c * s^d))
    (s : ℝ) (hs : 0 ≤ s) :
    (scaledLogSumLaw ν : Measure ℝ).real (Ioi s) ≤
      (2 * K) * Real.exp (-(c / (2 : ℝ)^d) * s^d) := by
  let P := (ν : Measure ℝ).prod (ν : Measure ℝ)
  let T := Ioi (s / 2)
  have hm : Measurable (fun p : ℝ × ℝ => p.1 + p.2) := by fun_prop
  have hT : MeasurableSet T := measurableSet_Ioi
  have hsub : (fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' Ioi s ⊆
      Prod.fst ⁻¹' T ∪ Prod.snd ⁻¹' T := by
    intro p hp
    change s < p.1 + p.2 at hp
    by_cases hfst : s / 2 < p.1
    · exact Or.inl hfst
    · exact Or.inr (show s / 2 < p.2 by linarith only [hp, le_of_not_gt hfst])
  have hf : P.real (Prod.fst ⁻¹' T) = (ν : Measure ℝ).real T := by
    rw [measureReal_def, ← Measure.map_apply measurable_fst hT, measurePreserving_fst.map_eq]
    rfl
  have hg : P.real (Prod.snd ⁻¹' T) = (ν : Measure ℝ).real T := by
    rw [measureReal_def, ← Measure.map_apply measurable_snd hT, measurePreserving_snd.map_eq]
    rfl
  have hbound := h (s/2) (div_nonneg hs (by norm_num))
  change (P.map (fun p : ℝ × ℝ => p.1 + p.2)).real (Ioi s) ≤ _
  rw [measureReal_def, Measure.map_apply hm measurableSet_Ioi]
  calc
    _ ≤ P.real (Prod.fst ⁻¹' T ∪ Prod.snd ⁻¹' T) := measureReal_mono hsub
    _ ≤ P.real (Prod.fst ⁻¹' T) + P.real (Prod.snd ⁻¹' T) := measureReal_union_le _ _
    _ ≤ _ := by
      rw [hf, hg]
      change (ν : Measure ℝ).real (Ioi (s / 2)) + (ν : Measure ℝ).real (Ioi (s / 2)) ≤ _
      rw [Real.div_rpow hs (by norm_num)] at hbound
      have hE : -c * (s ^ d / (2 : ℝ)^d) = -(c / (2 : ℝ)^d) * s^d := by ring
      rw [hE] at hbound
      linarith only [hbound]

/-- The Bethe pressure passes through weak convergence of positive
message laws when their scaled log messages have common second
moments and a common stretched upper tail. -/
theorem tendsto_bethePressure_of_logBounds {β d c K B : ℝ}
    (hβ : 0 < β) (hd : 0 < d) (hc : 0 < c) (hK : 0 ≤ K) (hB : 0 ≤ B)
    {μ : ℕ → ProbabilityMeasure ℝ} {μ₀ : ProbabilityMeasure ℝ}
    (hμ : ∀ n, (μ n : Measure ℝ) (Ioi 0) = 1) (hμ₀ : (μ₀ : Measure ℝ) (Ioi 0) = 1)
    (hweak : Tendsto μ atTop (𝓝 μ₀))
    (hlog : ∀ q ∈ insert μ₀ (range μ), MemLp id 2 (scaledLogLaw β q : Measure ℝ))
    (hlogM : ∀ q ∈ insert μ₀ (range μ),
      (∫ s, s^2 ∂(scaledLogLaw β q : Measure ℝ)) ≤ B)
    (htail : ∀ n s, 0 ≤ s → (scaledLogLaw β (μ n) : Measure ℝ).real (Ioi s) ≤
      K * Real.exp (-c * s^d)) :
    Tendsto (fun n => bethePressure β d (μ n : Measure ℝ)) atTop
      (𝓝 (bethePressure β d (μ₀ : Measure ℝ))) := by
  have hpos : ∀ᵐ h ∂(μ₀ : Measure ℝ), 0 < h :=
    (mem_ae_iff_prob_eq_one (measurableSet_Ioi (a := (0 : ℝ)))).mpr hμ₀
  have hm : Measurable (fun h : ℝ => Real.log h / β) := by fun_prop
  have hcont : ContinuousOn (fun h : ℝ => Real.log h / β) (Ioi 0) :=
    (Real.continuousOn_log.mono (fun _ hh => ne_of_gt hh)).div_const _
  have hweakLog : Tendsto (fun n => scaledLogLaw β (μ n)) atTop (𝓝 (scaledLogLaw β μ₀)) :=
    tendsto_probabilityMeasure_map_of_ae_pos hweak hpos hm hcont
  have hc' : 0 < c / (2 : ℝ)^d := by positivity
  apply tendsto_bethePressure_of_scaledLogLaw hβ hd hc' (show 0 ≤ 2 * K from mul_nonneg (by norm_num) hK) hB
    (show 0 ≤ 2 * (Real.log 2)^2 + 8 * β^2 * B by positivity)
    hμ hμ₀ hweakLog hlog hlogM
  · exact fun q hq => majorant_memLp (scaledLogLaw β q) (hlog q hq)
  · exact fun q hq => majorant_secondMoment β (scaledLogLaw β q) (hlog q hq) (hlogM q hq)
  · exact fun n => fun s hs => sumLog_upperTail (scaledLogLaw β (μ n)) (htail n) s hs

private theorem scaledLog_memLp (β : ℝ) (μ : ProbabilityMeasure ℝ)
    (h : MemLp Real.log 2 (μ : Measure ℝ)) :
    MemLp id 2 (scaledLogLaw β μ : Measure ℝ) := by
  have hf : Measurable (fun x : ℝ => Real.log x / β) := by fun_prop
  have hs : MemLp (fun x : ℝ => β⁻¹ * Real.log x) 2 (μ : Measure ℝ) := h.const_mul β⁻¹
  have hS : MemLp (fun x : ℝ => Real.log x / β) 2 (μ : Measure ℝ) := by
    simpa only [div_eq_inv_mul] using hs
  change MemLp id 2 ((μ : Measure ℝ).map (fun x : ℝ => Real.log x / β))
  exact (memLp_map_measure_iff measurable_id.aestronglyMeasurable hf.aemeasurable).mpr hS

private theorem scaledLog_secondMoment_of_eLpNorm {β B : ℝ} (hB : 0 ≤ B)
    (μ : ProbabilityMeasure ℝ) (h : eLpNorm Real.log 2 (μ : Measure ℝ) ≤ ENNReal.ofReal B) :
    (∫ s : ℝ, s^2 ∂(scaledLogLaw β μ : Measure ℝ)) ≤ (B / β)^2 := by
  have hn := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rw [ENNReal.toReal_ofReal hB, toReal_eLpNorm Real.measurable_log.aestronglyMeasurable,
    lpNorm_eq_integral_norm_rpow_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by simp)
      Real.measurable_log.aestronglyMeasurable] at hn
  have hN : Real.sqrt (∫ x : ℝ, (Real.log x)^2 ∂(μ : Measure ℝ)) ≤ B := by
    rw [Real.sqrt_eq_rpow]
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs, one_div] using hn
  have hnq : (∫ x : ℝ, (Real.log x)^2 ∂(μ : Measure ℝ)) ≤ B^2 := by
    have hs := pow_le_pow_left₀ (Real.sqrt_nonneg _) hN 2
    rwa [Real.sq_sqrt (integral_nonneg (fun _ => sq_nonneg _))] at hs
  have hf : Measurable (fun x : ℝ => Real.log x / β) := by fun_prop
  have hsq : Measurable (fun x : ℝ => x^2) := by fun_prop
  change (∫ s : ℝ, s^2 ∂(μ : Measure ℝ).map (fun x : ℝ => Real.log x / β)) ≤ _
  rw [integral_map hf.aemeasurable hsq.aestronglyMeasurable]
  simp only [div_pow, integral_div]
  exact div_le_div_of_nonneg_right hnq (sq_nonneg β)

private theorem scaledLog_tail {β c d K : ℝ} (hβ : 0 < β) (hK : 0 ≤ K)
    (μ : ProbabilityMeasure ℝ) (hpos : (μ : Measure ℝ) (Ioi 0) = 1)
    (s : ℝ) (h : (μ : Measure ℝ) (Ioi (Real.exp (β*s))) ≤
      ENNReal.ofReal (K * Real.exp (-c * s^d))) :
    (scaledLogLaw β μ : Measure ℝ).real (Ioi s) ≤ K * Real.exp (-c * s^d) := by
  have hp : ∀ᵐ x ∂(μ : Measure ℝ), 0 < x :=
    (mem_ae_iff_prob_eq_one (measurableSet_Ioi (a := (0 : ℝ)))).mpr hpos
  have hf : Measurable (fun x : ℝ => Real.log x / β) := by fun_prop
  have hset : ((fun x : ℝ => Real.log x / β) ⁻¹' Ioi s) =ᵐ[(μ : Measure ℝ)]
      Ioi (Real.exp (β*s)) := by
    filter_upwards [hp] with x hx
    apply propext

    change (s < Real.log x / β) ↔ Real.exp (β*s) < x
    rw [lt_div_iff₀ hβ, mul_comm s β, Real.lt_log_iff_exp_lt hx]
  change ((μ : Measure ℝ).map (fun x : ℝ => Real.log x / β)).real (Ioi s) ≤ _
  rw [measureReal_def, Measure.map_apply hf measurableSet_Ioi, measure_congr hset]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans_eq
    (ENNReal.toReal_ofReal (mul_nonneg hK (Real.exp_nonneg _)))

/-- Bethe pressures converge for weakly convergent positive message
laws with a common log (L^2) norm and stretched upper tail. -/
theorem tendsto_bethePressure_of_uniform_logBounds {β d c K B : ℝ}
    (hβ : 0 < β) (hd : 0 < d) (hc : 0 < c) (hK : 0 ≤ K) (hB : 0 ≤ B)
    {μ : ℕ → ProbabilityMeasure ℝ} {μ₀ : ProbabilityMeasure ℝ}
    (hμ : ∀ n, (μ n : Measure ℝ) (Ioi 0) = 1) (hμ₀ : (μ₀ : Measure ℝ) (Ioi 0) = 1)
    (hweak : Tendsto μ atTop (𝓝 μ₀))
    (hlog : ∀ q ∈ insert μ₀ (range μ),
      eLpNorm Real.log 2 (q : Measure ℝ) ≤ ENNReal.ofReal B)
    (htail : ∀ n s, 0 ≤ s → (μ n : Measure ℝ) (Ioi (Real.exp (β*s))) ≤
      ENNReal.ofReal (K * Real.exp (-c * s^d))) :
    Tendsto (fun n => bethePressure β d (μ n : Measure ℝ)) atTop
      (𝓝 (bethePressure β d (μ₀ : Measure ℝ))) := by
  apply tendsto_bethePressure_of_logBounds hβ hd hc hK (sq_nonneg (B / β)) hμ hμ₀ hweak
  · exact fun q hq => scaledLog_memLp β q
      ⟨Real.measurable_log.aestronglyMeasurable, (hlog q hq).trans_lt ENNReal.ofReal_lt_top⟩
  · exact fun q hq => scaledLog_secondMoment_of_eLpNorm hB q (hlog q hq)
  · exact fun n s hs => scaledLog_tail hβ hK (μ n) (hμ n) s (htail n s hs)

end Certificate

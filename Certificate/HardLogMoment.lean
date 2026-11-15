import Certificate.HardLogLowerTail
import Certificate.TailMoment
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Logarithmic second moments of a hard cavity law

The two logarithmic tails imply an eventual cubic power bound. Rescaling
lets the layer-cake second-moment estimate start at one.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace Certificate

private theorem eventually_stretched_le_cubic (K : ℝ) {c p : ℝ}
    (hc : 0 < c) (hp : 0 < p) :
    ∀ᶠ t : ℝ in atTop, K * Real.exp (-c*t^p) ≤ (1/3) * t^(-3:ℝ) := by
  have hl : Tendsto (fun t : ℝ => (t^p)^(3/p:ℝ) * Real.exp (-c*t^p))
      atTop (𝓝 0) :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (3/p) c hc).comp (tendsto_rpow_atTop hp)
  have hK : Tendsto (fun t : ℝ => K * ((t^p)^(3/p:ℝ) * Real.exp (-c*t^p)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hl
  have hsmall := (tendsto_order.mp hK).2 (1/3) (by norm_num)
  filter_upwards [hsmall, eventually_gt_atTop (0:ℝ)] with t ht ht₀
  have hpow : (t^p)^(3/p:ℝ) = t^(3:ℝ) := by
    rw [← Real.rpow_mul ht₀.le, mul_div_cancel₀ _ hp.ne']
  rw [Real.rpow_neg ht₀.le, ← div_eq_mul_inv]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos ht₀ _)).mpr
  rw [hpow] at ht
  simpa only [mul_comm, mul_assoc, mul_left_comm] using ht.le

private theorem rpow_div_div_eq {t L M p : ℝ} (ht : 0 ≤ t) (hL : 0 < L) (hM : 0 < M) :
    (t/L)^p / M = (1 / (M * L^p)) * t^p := by
  rw [Real.div_rpow ht hL.le]
  field_simp [(Real.rpow_pos_of_pos hL p).ne', hM.ne']

/-- The scaled absolute logarithmic tail is bounded by the two message tails. -/
theorem absolute_log_div_tail_le_union {β : ℝ} (hβ : 0 < β)
    (μ : Measure ℝ) (hp : ∀ᵐ x ∂μ, 0 < x) (t : ℝ) :
    μ {x | t < |Real.log x| / β} ≤
      μ (Ioi (Real.exp (β*t))) + μ (Iio (Real.exp (-β*t))) := by
  refine (measure_mono_ae ?_).trans (measure_union_le _ _)
  filter_upwards [hp] with x hx hxt
  have hlt : t*β < |Real.log x| := (lt_div_iff₀ hβ).mp hxt
  by_cases hneg : 0 ≤ Real.log x
  · rw [abs_of_nonneg hneg] at hlt
    exact Or.inl ((Real.lt_log_iff_exp_lt hx).mp (by linarith only [hlt]))
  · rw [abs_of_nonpos (le_of_not_ge hneg)] at hlt
    exact Or.inr ((Real.log_lt_iff_lt_exp hx).mp (by linarith only [hlt]))

/-- An upper stretched exponential and a lower stretched-exponential plus
exponential tail envelope are eventually dominated by a cubic power. -/
theorem eventually_log_tail_envelope_le_cubic {β d K C₁ C₂ : ℝ}
    (hd : 0 < d) (hβ : 0 < β) (hK₀ : 0 ≤ K) (h₁ : 0 ≤ C₁) (h₂ : 0 ≤ C₂) :
    ∀ᶠ t : ℝ in atTop, 0 ≤ t ∧
      ENNReal.ofReal (K*Real.exp (-((t/2)^d/2))) +
        ENNReal.ofReal (C₁*Real.exp (-((t/4)^d/4)) + C₂*Real.exp (-(β*t/2))) ≤
      ENNReal.ofReal (t^(-3:ℝ)) := by
  let c₁ : ℝ := 1/(2*(2:ℝ)^d)
  let c₂ : ℝ := 1/(4*(4:ℝ)^d)
  have hc₁ : 0 < c₁ := div_pos zero_lt_one
    (mul_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _))
  have hc₂ : 0 < c₂ := div_pos zero_lt_one
    (mul_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _))
  filter_upwards [eventually_stretched_le_cubic K hc₁ hd,
    eventually_stretched_le_cubic C₁ hc₂ hd,
    eventually_stretched_le_cubic C₂ (half_pos hβ) zero_lt_one,
    eventually_ge_atTop (0:ℝ)] with t ht₁ ht₂ ht₃ ht
  have he₁ : (t/2)^d/2 = c₁*t^d :=
    rpow_div_div_eq ht (by norm_num) (by norm_num)
  have he₂ : (t/4)^d/4 = c₂*t^d :=
    rpow_div_div_eq ht (by norm_num) (by norm_num)
  have he₃ : -(β/2)*t^(1:ℝ) = -(β*t/2) := by rw [Real.rpow_one]; ring
  rw [neg_mul, ← he₁] at ht₁
  rw [neg_mul, ← he₂] at ht₂
  rw [he₃] at ht₃
  have hU₀ : 0 ≤ K*Real.exp (-((t/2)^d/2)) := mul_nonneg hK₀ (Real.exp_nonneg _)
  have hL₀ : 0 ≤ C₁*Real.exp (-((t/4)^d/4)) + C₂*Real.exp (-(β*t/2)) :=
    add_nonneg (mul_nonneg h₁ (Real.exp_nonneg _)) (mul_nonneg h₂ (Real.exp_nonneg _))
  refine ⟨ht, ?_⟩
  rw [← ENNReal.ofReal_add hU₀ hL₀]
  exact ENNReal.ofReal_le_ofReal (by linarith only [ht₁,ht₂,ht₃])

/-- Eventually the absolute scaled logarithm is dominated by a cubic
probability tail. -/
theorem hard_cavity_absolute_log_power_tail {β d : ℝ} (hd : 0 < d) (hβ : 0 < β)
    {μ : Measure ℝ} (h : IsCavityLaw β d μ) :
    ∀ᶠ t : ℝ in atTop, μ {x | t < |Real.log x| / β} ≤ ENNReal.ofReal (t^(-3:ℝ)) := by
  let : IsProbabilityMeasure μ := h.1
  have hp : ∀ᵐ x ∂μ, 0 < x :=
    (mem_ae_iff_prob_eq_one (measurableSet_Ioi (a := (0:ℝ)))).mpr h.2.1
  obtain ⟨K, hK, hu⟩ := hard_cavity_log_upperTail hd hβ h
  obtain ⟨C₁, C₂, h₁, h₂, hl⟩ := hard_cavity_log_lowerTail hd hβ h
  filter_upwards [eventually_log_tail_envelope_le_cubic hd hβ
    (zero_le_one.trans hK) h₁ h₂] with t ht
  exact ((absolute_log_div_tail_le_union hβ μ hp t).trans
    (add_le_add (hu t ht.1) (hl t ht.1))).trans ht.2

/-- A cubic tail for the scaled log above a threshold controls its L²
seminorm explicitly. -/
theorem eLpNorm_two_log_le_of_power_tail_after {β M : ℝ} (hβ : 0 < β)
    (hM₁ : 1 ≤ M) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hT : ∀ t ≥ M, μ {x | t < |Real.log x| / β} ≤ ENNReal.ofReal (t^(-3:ℝ))) :
    eLpNorm Real.log 2 μ ≤ ENNReal.ofReal (β * M * (3 : ℝ)^(1 / 2 : ℝ)) := by
  have hM : 0 < M := zero_lt_one.trans_le hM₁
  let F := fun x : ℝ => |Real.log x| / β
  let G := fun x : ℝ => F x / M
  have hG : Measurable G := by dsimp [G,F]; fun_prop
  have hG₀ : 0 ≤ᵐ[μ] G :=
    Filter.Eventually.of_forall (fun x => div_nonneg (div_nonneg (abs_nonneg _) hβ.le) hM.le)
  have hTail (t : ℝ) (ht : 1 < t) : μ {x | t < G x} ≤ ENNReal.ofReal (t^(-3:ℝ)) := by
    have hx : {x | t < G x} = {x | t*M < |Real.log x|/β} := by
      ext x
      exact lt_div_iff₀ hM
    have hMt : M ≤ t*M := by nlinarith [mul_pos (sub_pos.mpr ht) hM]
    have htM : t ≤ t*M := by nlinarith [mul_nonneg (sub_nonneg.mpr hM₁) (zero_lt_one.trans ht).le]
    rw [hx]
    exact (hT _ hMt).trans
      (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans ht)
        htM (by norm_num)))
  have hGnorm : eLpNorm G 2 μ ≤ ENNReal.ofReal ((3 : ℝ)^(1 / 2 : ℝ)) := by
    simpa only [show (3 : ℝ)/(3 - 2) = 3 by norm_num] using
      eLpNorm_two_le_of_power_tail μ hG hG₀ (by norm_num : (2:ℝ)<3) hTail
  have hGscale : (β * M) • G = (fun x : ℝ => ‖Real.log x‖) := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs]
    dsimp [G,F]
    field_simp [hβ.ne', hM.ne']
  rw [← eLpNorm_norm Real.log, ← hGscale, eLpNorm_const_smul,
    Real.enorm_of_nonneg (mul_nonneg hβ.le hM.le), ENNReal.ofReal_mul (mul_nonneg hβ.le hM.le)]
  gcongr

/-- Every positive finite hard cavity law has square-integrable logarithm. -/
theorem hard_cavity_log_memLp_two {β d : ℝ} (hd : 0 < d) (hβ : 0 < β)
    {μ : Measure ℝ} (h : IsCavityLaw β d μ) : MemLp Real.log 2 μ := by
  let : IsProbabilityMeasure μ := h.1
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hard_cavity_absolute_log_power_tail hd hβ h)
  have hnorm := eLpNorm_two_log_le_of_power_tail_after hβ (le_max_right T 1) μ
    (fun t ht => hT t ((le_max_left T 1).trans ht))
  exact ⟨Real.measurable_log.aestronglyMeasurable, hnorm.trans_lt ENNReal.ofReal_lt_top⟩

/-- The logarithm in the hard Bethe pressure is integrable. -/
theorem hard_cavity_log_integrable {β d : ℝ} (hd : 0 < d) (hβ : 0 < β)
    {μ : Measure ℝ} (h : IsCavityLaw β d μ) : Integrable Real.log μ := by
  let : IsProbabilityMeasure μ := h.1
  exact (hard_cavity_log_memLp_two hd hβ h).integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)

/-- An invariant coupling between hard cavity laws has equal marginals.
Both log second moments follow from the cavity laws. -/
theorem hard_cavity_law_marginals_eq_of_fixed_coupling {β d : ℝ} (hd : 0 < d) (hβ : 0 < β)
    (ρ : Measure (ℝ × ℝ)) [IsProbabilityMeasure ρ]
    (h₁ : IsCavityLaw β d (ρ.map Prod.fst)) (h₂ : IsCavityLaw β d (ρ.map Prod.snd))
    (hinv : (markedArrivalSequenceLaw ρ).map (pairedHardRoot β d) = ρ) :
    ρ.map Prod.fst = ρ.map Prod.snd :=
  hard_cavity_law_marginals_eq_of_invariant hd ρ h₁ h₂ hinv
    (hard_cavity_log_memLp_two hd hβ h₁) (hard_cavity_log_memLp_two hd hβ h₂)

end Certificate

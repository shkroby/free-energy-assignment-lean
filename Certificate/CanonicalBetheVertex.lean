import Certificate.CanonicalDerivative
import Certificate.CanonicalSoftRegularity
import Certificate.PressureFormula
import Certificate.SoftBethe

/-! The differentiated vertex contribution on the coupled canonical tree. -/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace Certificate.CanonicalTree

theorem ae_lower_logFugacity_recursion {β d : ℝ} (hβ : 0 < β) (hd : 0 < d) :
    ∀ᵐ ω ∂law, ∀ t : ℝ, ∀ v,
      0 < lower β d (Real.exp t) v ω ∧
      lower β d (Real.exp t) v ω ≤ (Real.exp t)⁻¹ ∧
      lower β d (Real.exp t) v ω = TreeBoundary.update (Real.exp t) (weight β d ω v)
        (fun i => lower β d (Real.exp t) (child v i) ω) := by
  filter_upwards [ae_summable_weight hβ hd, ae_extremal_eq_all_logFugacities hβ hd] with ω hω heq
  intro t v
  have h := boundary_limits_of_summable_weight (Real.exp_pos t) hω v
  exact ⟨h.2.2.1, h.2.2.2.1.trans h.2.2.2.2.1,
    h.2.2.2.2.2.1.trans (congrArg _ (funext fun i => (heq t (child v i)).symm))⟩

theorem logMessageDerivative_branch (β d : ℝ) (v : Vertex) (t : ℝ) (ω : Environment) (i : ℕ) :
    logMessageDerivative β d v t (branch i ω) = logMessageDerivative β d (i :: v) t ω := by
  have h : (fun s => Real.log (lower β d (Real.exp s) v (branch i ω))) =
      fun s => Real.log (lower β d (Real.exp s) (i :: v) ω) := by
    funext s
    rw [lower_branch]
  unfold logMessageDerivative parameterDerivative
  rw [h]

/-- The derivative of the log cavity message is determined by the local vacancy
and the weighted derivatives of the child messages. -/
theorem ae_ae_logMessageDerivative_recursion {β d : ℝ} (hβ : 0 < β) (hd : 0 < d) :
    ∀ᵐ t : ℝ ∂volume, ∀ᵐ ω ∂law, ∀ v,
      logMessageDerivative β d v t ω = -(Real.exp t * lower β d (Real.exp t) v ω +
        ∑' i, weight β d ω v i * lower β d (Real.exp t) (child v i) ω *
          lower β d (Real.exp t) v ω * logMessageDerivative β d (child v i) t ω) := by
  filter_upwards [ae_ae_hasDerivAt_logMessage hβ hd] with t ht
  filter_upwards [ht, ae_lower_logFugacity_recursion hβ hd, ae_extremal_logLipschitz hβ hd,
    ae_summable_weight hβ hd] with ω hder hrec hreg hw
  intro v
  let H (i : ℕ) (s : ℝ) := lower β d (Real.exp s) (child v i) ω
  have hH₀ (i : ℕ) (s : ℝ) : 0 < H i s := (hrec s (child v i)).1
  have hH₁ (i : ℕ) (s : ℝ) : H i s ≤ Real.exp (-s) := by
    rw [Real.exp_neg]
    exact (hrec s (child v i)).2.1
  have hR := hasDerivAt_log_cavityUpdate (hw v) (weight_nonneg β d ω v) hH₀ hH₁
    (fun i => (hreg (child v i)).2.1) (fun i => hder (child v i))
  dsimp only at hR
  have heq (s : ℝ) : TreeBoundary.update (Real.exp s) (weight β d ω v) (fun i => H i s)
      = lower β d (Real.exp s) v ω := (hrec s v).2.2.symm
  simp only [heq, H] at hR
  exact (hder v).unique hR

private theorem lintegral_root_weight {β d : ℝ} (hd : 0 < d) :
    (∫⁻ ω, ∑' i, ENNReal.ofReal (weight β d ω [] i) ∂law) =
      ∫⁻ x, ENNReal.ofReal (Real.exp (-β * x)) ∂intensity d := by
  let μ := Measure.dirac ()
  let : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  let : IsProbabilityMeasure exponentialSpacings := isProbabilityMeasure_exponentialSpacings
  let : IsProbabilityMeasure (markedArrivalSequenceLaw μ) :=
    isProbabilityMeasure_markedArrivalSequenceLaw μ
  let g : (ℝ × Unit) × (Spacings × (ℕ → Unit)) → ℝ≥0∞ :=
    fun p => ENNReal.ofReal (Real.exp (-β * p.1.1))
  have hg : Measurable g := by dsimp [g]; fun_prop
  have hinsert := canonical_iid_marked_arrival_insertion hd μ g hg
  have h := (measurable_pi_apply ([] : Vertex) :
    Measurable (fun ω : Environment => ω [])).aemeasurable (μ := law)
  have hmap : law.map (fun ω : Environment => ω []) = exponentialSpacings := by
    exact Measure.infinitePi_map_eval (fun _ : Vertex => exponentialSpacings) []
  calc
    _ = ∫⁻ e, ∑' i, ENNReal.ofReal (Real.exp (-β * arrivalLength d e i)) ∂exponentialSpacings := by
      rw [← hmap, lintegral_map' (by unfold arrivalLength; fun_prop) h]
      rfl
    _ = ∫⁻ ω, ∑' i, g ((arrivalLength d ω.1 i, ω.2 i),
        (eraseArrivalGap i ω.1, eraseSequence i ω.2)) ∂markedArrivalSequenceLaw μ := by
      unfold markedArrivalSequenceLaw g
      rw [lintegral_prod _ (by unfold arrivalLength; fun_prop)]
      simp
    _ = _ := by
      rw [hinsert, lintegral_prod _ hg.aemeasurable]
      simp only [g, lintegral_const, measure_univ, mul_one]
      rw [lintegral_prod _ (by fun_prop)]
      simp

theorem integrable_root_totalWeight {β d : ℝ} (hβ : 0 < β) (hd : 0 < d) :
    Integrable (fun ω => ∑' i, weight β d ω [] i) law := by
  have hnn : ∀ᵐ ω ∂law, 0 ≤ ∑' i, weight β d ω [] i :=
    Eventually.of_forall fun ω => tsum_nonneg (weight_nonneg β d ω [])
  refine ⟨(Measurable.tsum fun i => measurable_weight β d [] i).aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal hnn).2 ?_⟩
  calc
    _ = ∫⁻ ω, ∑' i, ENNReal.ofReal (weight β d ω [] i) ∂law :=
      lintegral_congr_ae ((ae_summable_weight hβ hd).mono fun ω hω =>
        ENNReal.ofReal_tsum_of_nonneg (weight_nonneg β d ω []) (hω []))
    _ = ∫⁻ x, ENNReal.ofReal (Real.exp (-β * x)) ∂intensity d := lintegral_root_weight hd
    _ < ∞ := by
      have hi := integrable_intensity_exp_rpow hd zero_lt_one hβ
      simp only [Real.rpow_one] at hi
      exact (hasFiniteIntegral_iff_ofReal
        (Eventually.of_forall fun _ => Real.exp_nonneg _)).mp hi.2

/-- The root log correction and vacancy deficit both decay at least as the
total incident weight times the inverse squared fugacity. -/
theorem ae_logFugacity_gap_bounds {β d : ℝ} (hβ : 0 < β) (hd : 0 < d) (t : ℝ) :
    ∀ᵐ ω ∂law,
      ‖Real.log (lower β d (Real.exp t) [] ω) + t‖ ≤
        Real.exp (-2 * t) * (∑' i, weight β d ω [] i) ∧
      1 - Real.exp t * lower β d (Real.exp t) [] ω ∈
        Icc 0 (Real.exp (-2 * t) * (∑' i, weight β d ω [] i)) := by
  filter_upwards [ae_lower_logFugacity_recursion hβ hd, ae_summable_weight hβ hd] with ω hω hw
  let W := ∑' i, weight β d ω [] i
  let S := ∑' i, weight β d ω [] i * lower β d (Real.exp t) (child [] i) ω
  have hw₀ := weight_nonneg β d ω []
  have hs₀ (i : ℕ) : 0 ≤ weight β d ω [] i * lower β d (Real.exp t) (child [] i) ω :=
    mul_nonneg (hw₀ i) (hω t (child [] i)).1.le
  have hs₁ (i : ℕ) : weight β d ω [] i * lower β d (Real.exp t) (child [] i) ω
      ≤ weight β d ω [] i * Real.exp (-t) := by
    rw [Real.exp_neg]
    exact mul_le_mul_of_nonneg_left (hω t (child [] i)).2.1 (hw₀ i)
  have hs : 0 ≤ S := tsum_nonneg hs₀
  have hSW : S ≤ W * Real.exp (-t) := by
    rw [← tsum_mul_right]
    exact (Summable.of_nonneg_of_le hs₀ hs₁ ((hw []).mul_right _)).tsum_le_tsum hs₁
      ((hw []).mul_right _)
  have hsum : Real.exp t + S = Real.exp t * (1 + S * Real.exp (-t)) := by
    rw [Real.exp_neg]
    have hzt := (Real.exp_pos t).ne'
    field_simp
  have hlog₀ : 0 ≤ Real.log (1 + S * Real.exp (-t)) := Real.log_nonneg (le_add_of_nonneg_right (mul_nonneg hs (Real.exp_nonneg _)))
  have hlog₁ : Real.log (1 + S * Real.exp (-t)) ≤ S * Real.exp (-t) := by
    linarith only [Real.log_le_sub_one_of_pos
      (show 0 < 1 + S * Real.exp (-t) by positivity)]
  have hbound : S * Real.exp (-t) ≤ Real.exp (-2 * t) * W := by
    have hh := mul_le_mul_of_nonneg_right hSW (Real.exp_nonneg (-t))
    rw [show -2 * t = -t + -t by ring, Real.exp_add]
    nlinarith only [hh]
  constructor
  · rw [(hω t []).2.2]
    change ‖Real.log (Real.exp t + S)⁻¹ + t‖ ≤ Real.exp (-2 * t) * W
    rw [Real.log_inv, hsum, Real.log_mul (Real.exp_pos t).ne' (by positivity), Real.log_exp,
      show -(t + Real.log (1 + S * Real.exp (-t))) + t =
        -Real.log (1 + S * Real.exp (-t)) by ring, norm_neg, Real.norm_of_nonneg hlog₀]
    exact hlog₁.trans hbound
  · rw [(hω t []).2.2]
    change 1 - Real.exp t * (Real.exp t + S)⁻¹ ∈ Icc 0 (Real.exp (-2 * t) * W)
    have hz := Real.exp_pos t
    have hden : 0 < Real.exp t + S := by positivity
    have hq : 1 - Real.exp t * (Real.exp t + S)⁻¹ = S / (Real.exp t + S) := by
      field_simp
      ring
    rw [hq]
    refine ⟨div_nonneg hs hden.le, ?_⟩
    have hdiv := div_le_div_of_nonneg_left hs hz (le_add_of_nonneg_right hs)
    exact hdiv.trans (by simpa only [div_eq_mul_inv, Real.exp_neg] using hbound)

/-- The root's logarithm is integrable at each positive fugacity. -/
theorem integrable_logMessage_root {β d : ℝ} (hβ : 0 < β) (hd : 0 < d) (t : ℝ) :
    Integrable (fun ω => Real.log (lower β d (Real.exp t) [] ω)) law := by
  let : IsProbabilityMeasure law := isProbabilityMeasure_law
  have hi := ((integrable_root_totalWeight hβ hd).const_mul (Real.exp (-2 * t))).add
    (integrable_const (μ := law) ‖t‖)
  refine hi.mono' (measurable_lower β d (Real.exp t) []).log.aestronglyMeasurable ?_
  filter_upwards [ae_logFugacity_gap_bounds hβ hd t] with ω hω
  calc
    _ = ‖(Real.log (lower β d (Real.exp t) [] ω) + t) - t‖ := by rw [add_sub_cancel_right]
    _ ≤ ‖Real.log (lower β d (Real.exp t) [] ω) + t‖ + ‖t‖ := norm_sub_le _ _
    _ ≤ _ := add_le_add hω.1 le_rfl

/-- Differentiation commutes with expectation for the vertex log message. -/
theorem ae_hasDerivAt_expected_logMessage {β d : ℝ} (hβ : 0 < β) (hd : 0 < d) :
    ∀ᵐ t : ℝ ∂volume,
      HasDerivAt (fun s => ∫ ω, Real.log (lower β d (Real.exp s) [] ω) ∂law)
        (∫ ω, logMessageDerivative β d [] t ω ∂law) t := by
  let : IsProbabilityMeasure law := isProbabilityMeasure_law
  filter_upwards [ae_ae_hasDerivAt_logMessage hβ hd] with t ht
  apply hasDerivAt_integral_of_slope_envelope (integrable_logMessage_root hβ hd)
    (integrable_const (1 : ℝ)) (ht.mono fun _ h => h [])
  filter_upwards [self_mem_nhdsWithin] with s hs
  filter_upwards [ae_extremal_logLipschitz hβ hd] with ω hω
  have hst : s ≠ t := hs
  have hb := lipschitzWith_iff_dist_le_mul.mp (hω []).2.1 s t
  simp only [NNReal.coe_one, one_mul, dist_eq_norm] at hb
  rw [slope_def_field, norm_div, div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hst)), one_mul]
  exact hb

end Certificate.CanonicalTree

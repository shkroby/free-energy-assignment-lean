import Certificate.CanonicalTreeRegularity
import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.Topology.Instances.Real.Lemmas

/-! Jointly measurable derivatives along the log-fugacity parameter. -/

open MeasureTheory Filter Set
open scoped Topology

namespace Certificate

section Parameter

variable {Ω : Type*} [MeasurableSpace Ω]

private noncomputable def derivativeStep (n : ℕ) : ℝ := 1 / (n + 1 : ℝ)

private theorem derivativeStep_pos (n : ℕ) : 0 < derivativeStep n := by
  unfold derivativeStep
  positivity

private noncomputable def incrementSlope (f : ℝ → ℝ) (t u : ℝ) : ℝ :=
  u⁻¹ * (f (t + u) - f t)

/-- A jointly measurable choice of derivative where the sample path is differentiable. -/
noncomputable def parameterDerivative (F : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  limUnder atTop (fun n => incrementSlope (fun s => F s ω) t (derivativeStep n))

private theorem measurable_incrementSlope {F : ℝ → Ω → ℝ}
    (hF : Measurable (Function.uncurry F)) (u : ℝ) :
    Measurable (fun p : ℝ × Ω => incrementSlope (fun s => F s p.2) p.1 u) :=
  measurable_const.mul
    ((hF.comp ((measurable_fst.add_const u).prodMk measurable_snd)).sub hF)

theorem measurable_parameterDerivative {F : ℝ → Ω → ℝ}
    (hF : Measurable (Function.uncurry F)) :
    Measurable (Function.uncurry (parameterDerivative F)) :=
  (StronglyMeasurable.limUnder
    (l := (atTop : Filter ℕ))
    (fun n => (measurable_incrementSlope hF (derivativeStep n)).stronglyMeasurable)).measurable

omit [MeasurableSpace Ω] in
theorem parameterDerivative_eq {F : ℝ → Ω → ℝ} {t a : ℝ} {ω : Ω}
    (h : HasDerivAt (fun s => F s ω) a t) : parameterDerivative F t ω = a := by
  have ht : Tendsto derivativeStep atTop (𝓝[≠] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun n => (derivativeStep_pos n).ne'⟩
  have hs : Tendsto (incrementSlope (fun s => F s ω) t) (𝓝[≠] (0 : ℝ)) (𝓝 a) := by
    change Tendsto (fun u : ℝ => u⁻¹ * (F (t + u) ω - F t ω)) (𝓝[≠] (0 : ℝ)) (𝓝 a)
    simpa only [smul_eq_mul] using h.tendsto_slope_zero
  exact (hs.comp ht).limUnder_eq

private def rationalDerivative (f : ℝ → ℝ) (t a : ℝ) : Prop :=
  ∀ m : ℕ, ∃ n : ℕ, ∀ q : ℚ,
    0 < |(q : ℝ)| → |(q : ℝ)| < derivativeStep n →
      |incrementSlope f t q - a| ≤ derivativeStep m

private theorem rationalDerivative_of_hasDerivAt {f : ℝ → ℝ} {t a : ℝ}
    (h : HasDerivAt f a t) : rationalDerivative f t a := by
  have hs : Tendsto (incrementSlope f t) (𝓝[≠] (0 : ℝ)) (𝓝 a) := by
    change Tendsto (fun u : ℝ => u⁻¹ * (f (t + u) - f t)) (𝓝[≠] (0 : ℝ)) (𝓝 a)
    simpa only [smul_eq_mul] using h.tendsto_slope_zero
  intro m
  obtain ⟨δ, hδ, hbound⟩ := Metric.tendsto_nhdsWithin_nhds.mp hs
    (derivativeStep m) (derivativeStep_pos m)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  refine ⟨n, fun q hq hqn => ?_⟩
  have hq₀ : (q : ℝ) ∈ ({0}ᶜ : Set ℝ) := (abs_pos.mp hq)
  have hqδ : dist (q : ℝ) 0 < δ := by
    rw [Real.dist_eq, sub_zero]
    exact hqn.trans hn
  exact (by simpa only [Real.dist_eq] using (hbound hq₀ hqδ).le)

private theorem hasDerivAt_of_rationalDerivative {f : ℝ → ℝ} {t a : ℝ}
    (hf : Continuous f) (h : rationalDerivative f t a) : HasDerivAt f a t := by
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  change Tendsto (incrementSlope f t) (𝓝[≠] (0 : ℝ)) (𝓝 a)
  apply Metric.tendsto_nhdsWithin_nhds.mpr
  intro ε hε
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  obtain ⟨n, hn⟩ := h m
  refine ⟨derivativeStep n, derivativeStep_pos n, fun x hx hxn => ?_⟩
  have hx₀ : x ≠ 0 := hx
  have hx₁ : |x| < derivativeStep n := by simpa only [Real.dist_eq, sub_zero] using hxn
  obtain ⟨q, _, _, hq⟩ := Real.exists_seq_rat_strictMono_tendsto x
  have hnz : ∀ᶠ y : ℝ in 𝓝 x, y ≠ 0 := compl_singleton_mem_nhds hx₀
  have hq₀ : ∀ᶠ j in atTop, 0 < |(q j : ℝ)| :=
    (hq.eventually hnz).mono fun _ hj => abs_pos.mpr hj
  have hq₁ : ∀ᶠ j in atTop, |(q j : ℝ)| < derivativeStep n :=
    hq.eventually (continuous_abs.continuousAt.preimage_mem_nhds (Iio_mem_nhds hx₁))
  have hq₂ : ∀ᶠ j in atTop, |incrementSlope f t (q j) - a| ≤ derivativeStep m :=
    (hq₀.and hq₁).mono fun j hj => hn (q j) hj.1 hj.2
  have hcont : ContinuousAt (fun y => |incrementSlope f t y - a|) x := by
    unfold incrementSlope
    exact ((continuousAt_id.inv₀ hx₀).mul
      ((hf.comp (continuous_const.add continuous_id)).continuousAt.sub
        continuousAt_const)).sub_const a |>.abs
  rw [Real.dist_eq]
  exact (le_of_tendsto (hcont.tendsto.comp hq) hq₂).trans_lt hm

private theorem measurableSet_rationalDerivative {F : ℝ → Ω → ℝ}
    (hF : Measurable (Function.uncurry F)) :
    MeasurableSet {p : ℝ × Ω |
      rationalDerivative (fun s => F s p.2) p.1 (parameterDerivative F p.1 p.2)} := by
  unfold rationalDerivative
  simp only [Set.ofPred_forall, Set.ofPred_exists]
  refine MeasurableSet.iInter fun m => MeasurableSet.iUnion fun n =>
    MeasurableSet.iInter fun q => ?_
  by_cases hq : 0 < |(q : ℝ)|
  · by_cases hqn : |(q : ℝ)| < derivativeStep n
    · simp only [hq, hqn, Set.iInter_true]
      exact measurableSet_le
        (continuous_abs.measurable.comp
          ((measurable_incrementSlope hF q).sub (measurable_parameterDerivative hF)))
        measurable_const
    · simp [hqn]
  · simp [hq]

/-- Almost every deterministic parameter has almost surely differentiable sample paths. -/
theorem ae_ae_hasDerivAt_parameterDerivative {μ : Measure Ω} [SFinite μ]
    {F : ℝ → Ω → ℝ} (hF : Measurable (Function.uncurry F))
    (hLip : ∀ᵐ ω ∂μ, LipschitzWith 1 (fun t => F t ω)) :
    ∀ᵐ t : ℝ ∂volume, ∀ᵐ ω ∂μ, HasDerivAt (fun s => F s ω) (parameterDerivative F t ω) t := by
  have hpath : ∀ᵐ ω ∂μ, ∀ᵐ t : ℝ ∂volume,
      rationalDerivative (fun s => F s ω) t (parameterDerivative F t ω) := by
    filter_upwards [hLip] with ω hω
    filter_upwards [hω.ae_differentiableAt_real] with t ht
    rw [parameterDerivative_eq ht.hasDerivAt]
    exact rationalDerivative_of_hasDerivAt ht.hasDerivAt
  have hdet := (Measure.ae_ae_comm (measurableSet_rationalDerivative hF)).mpr hpath
  filter_upwards [hdet] with t ht
  filter_upwards [ht, hLip] with ω hω hL
  exact hasDerivAt_of_rationalDerivative hL.continuous hω

end Parameter

namespace CanonicalTree

/-- Log-fugacity derivative of the logarithm of the canonical cavity message. -/
noncomputable def logMessageDerivative (β d : ℝ) (v : Vertex) (t : ℝ) (ω : Environment) : ℝ :=
  parameterDerivative (fun s env => Real.log (lower β d (Real.exp s) v env)) t ω

theorem measurable_logMessageDerivative (β d : ℝ) (v : Vertex) :
    Measurable (fun p : ℝ × Environment => logMessageDerivative β d v p.1 p.2) :=
  measurable_parameterDerivative (measurable_lower_logFugacity β d v).log

theorem ae_ae_hasDerivAt_logMessage {β d : ℝ} (hβ : 0 < β) (hd : 0 < d) :
    ∀ᵐ t : ℝ ∂volume, ∀ᵐ ω ∂law, ∀ v : Vertex,
      HasDerivAt (fun s => Real.log (lower β d (Real.exp s) v ω))
        (logMessageDerivative β d v t ω) t := by
  let : IsProbabilityMeasure law := isProbabilityMeasure_law
  have hv (v : Vertex) :
      ∀ᵐ t : ℝ ∂volume, ∀ᵐ ω ∂law,
        HasDerivAt (fun s => Real.log (lower β d (Real.exp s) v ω))
          (logMessageDerivative β d v t ω) t :=
    ae_ae_hasDerivAt_parameterDerivative (measurable_lower_logFugacity β d v).log
      ((ae_extremal_logLipschitz hβ hd).mono fun _ h => (h v).2.1)
  filter_upwards [ae_all_iff.mpr hv] with t ht
  exact ae_all_iff.mpr ht

end CanonicalTree
end Certificate

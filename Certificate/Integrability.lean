import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The final L¹ transfer

A bounded L² part and an exceptional error with vanishing L¹ norm suffice
to upgrade almost-sure convergence. For the assignment pressure the stochastic
estimates proving these two bounds are separate, unproved inputs.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace Certificate

/-- A uniform L² bound gives uniform absolute continuity of the L¹ norms on sets. -/
theorem unifIntegrable_one_of_uniform_two {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : ι → Ω → ℝ} (h : ∀ i, AEStronglyMeasurable (f i) μ)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ i, eLpNorm (f i) 2 μ ≤ ENNReal.ofReal C) :
    UnifIntegrable f 1 μ := by
  intro ε hε
  let t := ε / (C + 1)
  have hC1 : 0 < C + 1 := by linarith
  have ht : 0 < t := div_pos hε hC1
  refine ⟨t ^ 2, sq_pos_of_pos ht, ?_⟩
  intro i s hs hμs
  have hmoment := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (p := 1) (q := 2) (by norm_num : (1 : ℝ≥0∞) ≤ 2) ((h i).restrict : AEStronglyMeasurable (f i) (μ.restrict s))
  rw [Measure.restrict_apply_univ] at hmoment
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]
  have h₂ : eLpNorm (f i) 2 (μ.restrict s) ≤ ENNReal.ofReal C := by
    rw [← eLpNorm_indicator_eq_eLpNorm_restrict hs]
    exact (eLpNorm_indicator_le (f i)).trans (hbound i)
  have hpow : ENNReal.ofReal (t ^ 2) ^ (1 / 2 : ℝ) = ENNReal.ofReal t := by
    rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg t) (by norm_num),
      ← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    norm_num
  have hδ : μ s ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal t := by
    rw [← hpow]
    exact ENNReal.rpow_le_rpow hμs (by norm_num)
  calc
    eLpNorm (f i) 1 (μ.restrict s) ≤
        eLpNorm (f i) 2 (μ.restrict s) * μ s ^ (1 / 2 : ℝ) := by
      convert hmoment using 2
      norm_num
    _ ≤ ENNReal.ofReal C * ENNReal.ofReal t := mul_le_mul' h₂ hδ
    _ ≤ ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_mul hC]
      apply ENNReal.ofReal_le_ofReal
      have hte : t * (C + 1) = ε := div_mul_cancel₀ _ hC1.ne'
      nlinarith [ht.le]

/-- Almost-sure convergence gives convergence in mean absolute error if the
sequence splits into a uniformly L²-bounded part and an L¹-negligible part. -/
theorem tendsto_L1_of_ae_of_L2_add_small_L1 {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f g : ℕ → Ω → ℝ} {limit : ℝ} {C : ℝ}
    (hC : 0 ≤ C)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hbound : ∀ n, eLpNorm (f n) 2 μ ≤ ENNReal.ofReal C)
    (hg : ∀ n, MemLp (g n) 1 μ)
    (hg₀ : Tendsto (fun n ↦ eLpNorm (g n) 1 μ) atTop (𝓝 0))
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ f n ω + g n ω) atTop (𝓝 limit)) :
    Tendsto (fun n ↦ ∫ ω, |f n ω + g n ω - limit| ∂μ) atTop (𝓝 0) := by
  have hm (n : ℕ) : AEStronglyMeasurable ((f + g) n) μ := (hf n).add (hg n).1
  have huf := unifIntegrable_one_of_uniform_two hf hC hbound
  have hug := unifIntegrable_of_tendsto_Lp_zero le_rfl ENNReal.one_ne_top hg hg₀
  have hu := huf.add hug le_rfl hf (fun n ↦ (hg n).1)
  have hLp := tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top hm
    (memLp_const limit) hu hlim
  have ht := (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp hLp
  simp only [Function.comp_def, ENNReal.toReal_zero] at ht
  refine ht.congr' (.of_forall fun n ↦ ?_)
  rw [eLpNorm_one_eq_lintegral_enorm,
    ← integral_norm_eq_lintegral_enorm ((hm n).sub aestronglyMeasurable_const)]
  simp only [Pi.sub_apply, Pi.add_apply, Real.norm_eq_abs]

end Certificate

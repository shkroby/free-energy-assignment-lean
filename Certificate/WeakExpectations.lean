import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Convergence of expectations under common second moments

Clipping a real continuous test makes weak convergence applicable.
The second moments uniformly control the discarded tails.
-/

open Filter MeasureTheory
open scoped ENNReal Topology BoundedContinuousFunction

namespace Certificate

private def clipReal (R x : ℝ) : ℝ := min R (max (-R) x)

private theorem abs_clipReal_le {R : ℝ} (hR : 0 ≤ R) (x : ℝ) :
    |clipReal R x| ≤ R := by
  apply abs_le.mpr
  exact ⟨le_min (by linarith) (le_max_left _ _), min_le_left _ _⟩

private theorem abs_sub_clipReal_le {R : ℝ} (hR : 0 < R) (x : ℝ) :
    |x - clipReal R x| ≤ x^2 / R := by
  by_cases hu : R ≤ x
  · have h₁ : -R ≤ x := by linarith
    rw [clipReal, max_eq_right h₁, min_eq_left hu, abs_of_nonneg (sub_nonneg.mpr hu)]
    apply (le_div_iff₀ hR).mpr
    nlinarith [sq_nonneg (x-R), mul_nonneg hR.le (sub_nonneg.mpr hu), sq_nonneg R]
  by_cases hl : x ≤ -R
  · have h₁ : -R ≤ R := by linarith
    rw [clipReal, max_eq_left hl, min_eq_right h₁,
      abs_of_nonpos (sub_nonpos.mpr hl)]
    apply (le_div_iff₀ hR).mpr
    nlinarith [sq_nonneg (x+R), mul_nonneg hR.le (sub_nonneg.mpr hl), sq_nonneg R]
  · rw [clipReal, max_eq_right (le_of_not_ge hl), min_eq_right (le_of_not_ge hu), sub_self, abs_zero]
    positivity

private theorem integral_sub_clip_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : Measurable f)
    (hfi : Integrable f μ) (hfs : Integrable (fun x => f x^2) μ) {R : ℝ} (hR : 0 < R) :
    |(∫ x, f x ∂μ) - ∫ x, clipReal R (f x) ∂μ| ≤ (∫ x, f x^2 ∂μ) / R := by
  have hclip : Measurable (clipReal R) := by unfold clipReal; fun_prop
  have hbi : Integrable (fun x => clipReal R (f x)) μ :=
    Integrable.of_bound (hclip.comp hf).aestronglyMeasurable R
      (.of_forall fun x => by rw [Real.norm_eq_abs]; exact abs_clipReal_le hR.le (f x))
  rw [← integral_sub hfi hbi]
  calc
    _ ≤ ∫ x, |f x - clipReal R (f x)| ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun x => f x - clipReal R (f x))
    _ ≤ ∫ x, f x^2 / R ∂μ :=
      integral_mono ((hfi.sub hbi).abs) (hfs.div_const R)
        (fun x => abs_sub_clipReal_le hR (f x))
    _ = _ := integral_div _ _

/-- Weak convergence plus a uniform second moment for a real continuous
test implies convergence of its expectations. -/
theorem tendsto_integral_of_weak_of_secondMoment
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]
    {μ : ℕ → ProbabilityMeasure Ω} {ν : ProbabilityMeasure Ω}
    (hμ : Tendsto μ atTop (𝓝 ν)) {f : Ω → ℝ} (hf : Continuous f)
    (hfm : ∀ n, MemLp f 2 (μ n : Measure Ω)) (hfn : MemLp f 2 (ν : Measure Ω))
    {B : ℝ} (hB : 0 ≤ B)
    (h₂ : ∀ n, (∫ x, f x^2 ∂(μ n : Measure Ω)) ≤ B)
    (h₂ν : (∫ x, f x^2 ∂(ν : Measure Ω)) ≤ B) :
    Tendsto (fun n => ∫ x, f x ∂(μ n : Measure Ω)) atTop
      (𝓝 (∫ x, f x ∂(ν : Measure Ω))) := by
  have hI {m : Measure Ω} [IsFiniteMeasure m] (hm : MemLp f 2 m) : Integrable f m := by
    apply hm.integrable
    norm_num
  have hS {m : Measure Ω} (hm : MemLp f 2 m) : Integrable (fun x => f x^2) m := by
    simpa only [Real.norm_eq_abs, sq_abs] using hm.integrable_norm_pow (p := 2) (by decide)
  rw [Metric.tendsto_atTop]
  intro ε hε
  let R := (4 * B + 1) / ε
  have hR : 0 < R := by dsimp [R]; positivity
  have hsmall : B / R < ε / 4 := by
    apply (div_lt_iff₀ hR).mpr
    dsimp [R]
    field_simp [hε.ne']
    linarith
  let g : Ω →ᵇ ℝ := BoundedContinuousFunction.mkOfBound
    ⟨fun x => clipReal R (f x), by unfold clipReal; fun_prop⟩ (2 * R) (fun x y => by
      change dist (clipReal R (f x)) (clipReal R (f y)) ≤ 2 * R
      rw [Real.dist_eq]
      calc
        _ ≤ |clipReal R (f x)| + |clipReal R (f y)| := abs_sub _ _
        _ ≤ _ := by linarith [abs_clipReal_le hR.le (f x), abs_clipReal_le hR.le (f y)])
  have hg := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ g
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hg (ε / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hn' := hN n hn
  rw [Real.dist_eq] at hn' ⊢
  change |(∫ x, clipReal R (f x) ∂(μ n : Measure Ω)) -
      (∫ x, clipReal R (f x) ∂(ν : Measure Ω))| < ε / 2 at hn'
  have h₁ := (integral_sub_clip_le hf.measurable (hI (hfm n)) (hS (hfm n)) hR).trans
    (div_le_div_of_nonneg_right (h₂ n) hR.le)
  have h₃ := (integral_sub_clip_le hf.measurable (hI hfn) (hS hfn) hR).trans
    (div_le_div_of_nonneg_right h₂ν hR.le)
  let a := ∫ x, f x ∂(μ n : Measure Ω)
  let b := ∫ x, clipReal R (f x) ∂(μ n : Measure Ω)
  let c := ∫ x, clipReal R (f x) ∂(ν : Measure Ω)
  let d := ∫ x, f x ∂(ν : Measure Ω)
  change |a-d| < ε
  change |a-b| ≤ B/R at h₁
  change |b-c| < ε/2 at hn'
  change |d-c| ≤ B/R at h₃
  have ht : |a - d| ≤ |a-b| + |b-c| + |d-c| := by
    rw [show a - d = (a-b) + (b-c) + (c-d) by ring, abs_sub_comm d c]
    exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  linarith

end Certificate

import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.IdentDistrib

/-!
# Cavity comparison at the two endpoints of an inserted edge

This closes the algebra and the final probability argument of the uniqueness proof
once the two occupation vectors have been shown to agree. The fixed point and
Poisson exchange arguments connecting these hypotheses to the PWIT remain separate.
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace Certificate

noncomputable def edgeOccupation (w A B : ℝ) : ℝ := w * A * B / (1 + w * A * B)

noncomputable def fullEndpoint (w A B : ℝ) : ℝ := A / (1 + w * A * B)

theorem edgeOccupation_swap (w A B : ℝ) :
    edgeOccupation w A B = edgeOccupation w B A := by
  unfold edgeOccupation
  ring

theorem edgeOccupation_pos {w A B : ℝ} (hw : 0 < w) (hA : 0 < A) (hB : 0 < B) :
    0 < edgeOccupation w A B := by
  unfold edgeOccupation
  positivity

theorem edgeOccupation_lt_one {w A B : ℝ} (hw : 0 < w) (hA : 0 < A) (hB : 0 < B) :
    edgeOccupation w A B < 1 := by
  unfold edgeOccupation
  rw [div_lt_one (by positivity)]
  linarith

theorem fullEndpoint_pos {w A B : ℝ} (hw : 0 < w) (hA : 0 < A) (hB : 0 < B) :
    0 < fullEndpoint w A B := by
  unfold fullEndpoint
  positivity

/-- Equation (endpoint-factorization) before taking logarithms. -/
theorem occupation_factorization {w A B : ℝ} (hw : 0 < w) (hA : 0 < A) (hB : 0 < B) :
    edgeOccupation w A B * (1 - edgeOccupation w A B) =
      w * fullEndpoint w A B * fullEndpoint w B A := by
  have hu : 1 + w * A * B ≠ 0 := (show 0 < 1 + w * A * B by positivity).ne'
  have hu' : 1 + w * B * A ≠ 0 := (show 0 < 1 + w * B * A by positivity).ne'
  unfold edgeOccupation fullEndpoint
  field_simp
  ring

/-- The common edge weight cancels from the logarithmic difference. -/
theorem occupation_log_ratio {w A B A' B' : ℝ} (hw : 0 < w)
    (hA : 0 < A) (hB : 0 < B) (hA' : 0 < A') (hB' : 0 < B') :
    Real.log ((edgeOccupation w A B * (1 - edgeOccupation w A B)) /
      (edgeOccupation w A' B' * (1 - edgeOccupation w A' B'))) =
      (Real.log (fullEndpoint w A B) - Real.log (fullEndpoint w A' B')) +
      (Real.log (fullEndpoint w B A) - Real.log (fullEndpoint w B' A')) := by
  rw [occupation_factorization hw hA hB, occupation_factorization hw hA' hB']
  have p := (fullEndpoint_pos hw hA hB).ne'
  have q := (fullEndpoint_pos hw hB hA).ne'
  have p' := (fullEndpoint_pos hw hA' hB').ne'
  have q' := (fullEndpoint_pos hw hB' hA').ne'
  rw [Real.log_div (mul_ne_zero (mul_ne_zero hw.ne' p) q)
      (mul_ne_zero (mul_ne_zero hw.ne' p') q'),
    Real.log_mul (mul_ne_zero hw.ne' p) q, Real.log_mul (mul_ne_zero hw.ne' p') q',
    Real.log_mul hw.ne' p, Real.log_mul hw.ne' p']
  ring

/-- Equality of the two edge choices forces the root and child cavity log
differences to sum to zero. -/
theorem log_differences_cancel {w a b a' b' : ℝ} (hw : 0 < w)
    (ha : 0 < a) (hb : 0 < b) (ha' : 0 < a') (hb' : 0 < b')
    (h : w * a * b = w * a' * b') :
    (Real.log a - Real.log a') + (Real.log b - Real.log b') = 0 := by
  have hp : a * b = a' * b' := mul_left_cancel₀ hw.ne'
    (by simpa only [mul_assoc] using h)
  have hlog := congrArg Real.log hp
  rw [Real.log_mul ha.ne' hb.ne', Real.log_mul ha'.ne' hb'.ne'] at hlog
  linarith

/-- Recover equality of the root messages after occupational equality.
The first two child log differences are independent and square integrable;
invariance identifies the law of the root difference with that of the first child. -/
theorem ae_root_log_difference_zero {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {R X Y : Ω → ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hi : X ⟂ᵢ[μ] Y)
    (hinv : IdentDistrib R X μ μ)
    (h₀ : ∀ᵐ ω ∂μ, X ω = -R ω) (h₁ : ∀ᵐ ω ∂μ, Y ω = -R ω) :
    ∀ᵐ ω ∂μ, R ω = 0 := by
  have hXY : (fun ω ↦ X ω - Y ω) =ᵐ[μ] 0 := by
    filter_upwards [h₀, h₁] with ω h hx
    change X ω - Y ω = 0
    rw [h, hx, sub_self]
  have hv : Var[fun ω ↦ X ω - Y ω; μ] = 0 := by
    rw [variance_congr hXY, variance_zero]
  rw [variance_fun_sub hX hY, hi.covariance_eq_zero hX hY] at hv
  have hvX : Var[X; μ] = 0 := by
    linarith [variance_nonneg (X := X) (μ := μ), variance_nonneg (X := Y) (μ := μ)]
  have hconst := ae_eq_integral_of_variance_eq_zero hX hvX
  have hR : R =ᵐ[μ] (fun _ ↦ -(∫ ω, X ω ∂μ)) := by
    filter_upwards [hconst, h₀] with ω hx hr
    linarith
  have hintR := integral_congr_ae hR
  rw [integral_const] at hintR
  have hmean := hinv.integral_eq
  have hzero : (∫ ω, X ω ∂μ) = 0 := by
    simp at hintR
    linarith
  filter_upwards [hR] with ω hω
  simpa [hzero] using hω

/-- Positive a.e. equal-log random variables have identical laws. -/
theorem map_eq_of_ae_log_difference_zero {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {H H' : Ω → ℝ}
    (hp : ∀ᵐ ω ∂μ, 0 < H ω ∧ 0 < H' ω)
    (h : ∀ᵐ ω ∂μ, Real.log (H ω) - Real.log (H' ω) = 0) :
    μ.map H = μ.map H' := by
  apply Measure.map_congr
  filter_upwards [hp, h] with ω hω he
  exact Real.strictMonoOn_log.injOn hω.1 hω.2 (sub_eq_zero.mp he)

end Certificate

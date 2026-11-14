import Certificate.Model
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Gamma

/-!
# Limits in the vertex and edge terms

The exponential envelope in the manuscript is integrable against the pseudo-dimension
intensity. The final dominated-convergence step is checked separately from the random
message estimates that are needed to establish its hypotheses.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace Certificate

/-- `exp(-b * x^p)` is integrable against `d * x^(d-1) dx` for positive parameters. -/
theorem integrable_intensity_exp_rpow {d p b : ℝ} (hd : 0 < d) (hp : 0 < p)
    (hb : 0 < b) : Integrable (fun x : ℝ ↦ Real.exp (-b * x ^ p)) (intensity d) := by
  have hpow : IntegrableOn (fun x : ℝ ↦ x ^ (d - 1) * Real.exp (-b * x ^ p)) (Ioi 0) := by
    by_contra hh
    have hi := integral_undef hh
    rw [integral_rpow_mul_exp_neg_mul_rpow hp (by linarith) hb] at hi
    have hG : 0 < Real.Gamma ((d - 1 + 1) / p) :=
      Real.Gamma_pos_of_pos (div_pos (by linarith) hp)
    have hpositive : 0 < b ^ (-(d - 1 + 1) / p) * (1 / p) *
        Real.Gamma ((d - 1 + 1) / p) := by positivity
    exact hpositive.ne' hi
  unfold intensity
  refine (integrable_withDensity_iff (by fun_prop) (by simp)).mpr ?_
  refine (hpow.const_mul d).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x (hx : 0 < x)
  simp only [ENNReal.toReal_ofReal (mul_nonneg hd.le (Real.rpow_nonneg hx.le _))]
  ring

/-- The integrability of the precise envelope in the final pressure calculation. -/
theorem integrable_edge_envelope {d β c K : ℝ} (hd : 0 < d) (hβ : 0 < β) (hc : 0 < c) :
    Integrable (fun x : ℝ ↦ Real.exp (-β * x / 2) + K * Real.exp (-c * x ^ d))
      (intensity d) := by
  have h₁ := integrable_intensity_exp_rpow hd zero_lt_one (show 0 < β / 2 by positivity)
  have h₂ := (integrable_intensity_exp_rpow hd hd hc).const_mul K
  have h₁' : Integrable (fun x : ℝ ↦ Real.exp (-(β / 2) * x)) (intensity d) := by
    simpa only [Real.rpow_one] using h₁
  refine (h₁'.add h₂).congr (.of_forall fun x ↦ ?_)
  dsimp
  rw [show -(β / 2) * x = -β * x / 2 by ring]

/-- Limit passage in the full two-term expression once the expected log message
and the dominated expectations of the edge corrections are known to converge. -/
theorem tendsto_bethePressure {β d : ℝ} {H : ℕ → Measure ℝ} {H₀ : Measure ℝ}
    (hvertex : Tendsto (fun n ↦ ∫ h, Real.log h ∂H n) atTop (𝓝 (∫ h, Real.log h ∂H₀)))
    {bound : ℝ → ℝ} (hbound : Integrable bound (intensity d))
    (hedge_meas : ∀ n, AEStronglyMeasurable (edgeLogCorrection β (H n)) (intensity d))
    (hedge_bound : ∀ n, ∀ᵐ x ∂intensity d, ‖edgeLogCorrection β (H n) x‖ ≤ bound x)
    (hedge_lim : ∀ᵐ x ∂intensity d, Tendsto (fun n ↦ edgeLogCorrection β (H n) x)
      atTop (𝓝 (edgeLogCorrection β H₀ x))) :
    Tendsto (fun n ↦ bethePressure β d (H n)) atTop (𝓝 (bethePressure β d H₀)) := by
  have hedge := tendsto_integral_of_dominated_convergence bound
    hedge_meas hbound hedge_bound hedge_lim
  exact (hvertex.const_mul (-2)).sub hedge

end Certificate

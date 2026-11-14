import Certificate.Model
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Probability.Distributions.Poisson.PoissonLimitThm

/-!
# Rare short edges

The small-cost assumption implies the correct first-order edge probability,
and hence the scalar Poisson limit for the binomial neighbor count. This does
not assert joint convergence of rooted marked neighborhoods.
-/

open Filter ProbabilityTheory Set MeasureTheory
open scoped Topology

namespace Certificate

/-- Retention probability of one edge in the graph truncated at length `x`. -/
noncomputable def shortEdgeProbability (μ : Measure ℝ) (d κ x : ℝ) (n : ℕ) : ℝ :=
  cdf μ (x / lengthScale d κ n)

/-- The finite-size edge intensity converges to the cumulative PWIT intensity. -/
theorem tendsto_scaled_shortEdgeProbability {μ : Measure ℝ} {d κ x : ℝ}
    (hd : 0 < d) (hκ : 0 < κ) (hx : 0 < x) (h : SmallCostTail μ κ d) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * shortEdgeProbability μ d κ x n) atTop (𝓝 (x ^ d)) := by
  have hscale : Tendsto (lengthScale d κ) atTop atTop :=
    (tendsto_rpow_atTop (one_div_pos.mpr hd)).comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hκ)
  have harg : Tendsto (fun n : ℕ ↦ x / lengthScale d κ n) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (hscale.const_div_atTop x) ?_
    filter_upwards [hscale.eventually_gt_atTop 0] with n hn
    exact div_pos hx hn
  have hmain := (h.2.comp harg).const_mul (x ^ d)
  simp only [mul_one] at hmain
  refine hmain.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  change x ^ d * (cdf μ (x / lengthScale d κ n) /
    (κ * (x / lengthScale d κ n) ^ d)) = _
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnκ : 0 < κ * (n : ℝ) := mul_pos hκ hn'
  have hscale_pos : 0 < lengthScale d κ n := Real.rpow_pos_of_pos hnκ _
  have hscale_pow : lengthScale d κ n ^ d = κ * n := by
    rw [lengthScale, ← Real.rpow_mul hnκ.le, one_div_mul_cancel hd.ne', Real.rpow_one]
  rw [Real.div_rpow hx.le hscale_pos.le, hscale_pow]
  unfold shortEdgeProbability
  have hxd : 0 < x ^ d := Real.rpow_pos_of_pos hx d
  field_simp

/-- For any fixed neighbor count, the binomial mass converges to the Poisson mass
with mean `x^d`. -/
theorem tendsto_shortEdge_binomial_mass {μ : Measure ℝ} {d κ x : ℝ} (k : ℕ)
    (hd : 0 < d) (hκ : 0 < κ) (hx : 0 < x) (h : SmallCostTail μ κ d) :
    Tendsto
      (fun n : ℕ ↦ (n.choose k : ℝ) * (shortEdgeProbability μ d κ x n) ^ k *
        (1 - shortEdgeProbability μ d κ x n) ^ (n - k))
      atTop (𝓝 (Real.exp (-(x ^ d)) * (x ^ d) ^ k / k.factorial)) :=
  tendsto_choose_mul_pow_of_tendsto_mul_atTop k (tendsto_scaled_shortEdgeProbability hd hκ hx h)

end Certificate

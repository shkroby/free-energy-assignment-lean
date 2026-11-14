import Certificate.SoftLogLipschitz
import Certificate.Endpoints
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.BoundedVariation
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Differentiating the weighted cavity recursion

The slope form of differentiability and dominated convergence for series
justify termwise differentiation at any point where all child log messages
are differentiable. We also check the derivative for an inserted edge and
the cancellation of the two endpoint contributions.
-/

open Filter Set
open scoped Topology

namespace Certificate

private theorem hasDerivAt_tsum_of_slope_bound {g : ℕ → ℝ → ℝ} {g' bound : ℕ → ℝ} {t : ℝ}
    (hs : ∀ x, Summable (fun i => g i x)) (hbound : Summable bound)
    (hg : ∀ i, HasDerivAt (g i) (g' i) t)
    (hb : ∀ᶠ x in 𝓝[≠] t, ∀ i, ‖slope (g i) t x‖ ≤ bound i) :
    HasDerivAt (fun x => ∑' i, g i x) (∑' i, g' i) t := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  refine (tendsto_tsum_of_dominated_convergence hbound
    (fun i => (hg i).tendsto_slope) hb).congr ?_
  intro x
  simp only [slope_def_field, tsum_div_const, (hs x).tsum_sub (hs t)]

private theorem hasDerivAt_of_log {f : ℝ → ℝ} {q t : ℝ}
    (hp : ∀ x, 0 < f x) (hf : HasDerivAt (fun x => Real.log (f x)) q t) :
    HasDerivAt f (f t * q) t := by
  simpa only [Function.comp_def, Real.exp_log (hp _)] using (Real.hasDerivAt_exp (Real.log (f t))).comp t hf

private theorem norm_exp_sub_exp_le {a b B : ℝ} (ha : a ≤ B) (hb : b ≤ B) :
    ‖Real.exp a - Real.exp b‖ ≤ Real.exp B * ‖a - b‖ := by
  refine (convex_Iic B).norm_image_sub_le_of_norm_deriv_le (fun x _ => (Real.hasDerivAt_exp x).differentiableAt)
    (fun x hx => ?_) hb ha
  rw [(Real.hasDerivAt_exp x).deriv, Real.norm_of_nonneg (Real.exp_nonneg _)]
  exact Real.exp_le_exp.mpr hx

private theorem norm_sub_message_le {f : ℝ → ℝ} {x t : ℝ}
    (hp : ∀ s, 0 < f s) (hu : ∀ s, f s ≤ Real.exp (-s))
    (hLip : LipschitzWith 1 (fun s => Real.log (f s))) (hx : t - 1 < x) :
    ‖f x - f t‖ ≤ Real.exp (1 - t) * ‖x - t‖ := by
  have h (s : ℝ) (hs : t - 1 ≤ s) : Real.log (f s) ≤ 1 - t := by
    calc
      _ ≤ Real.log (Real.exp (-s)) := Real.log_le_log (hp s) (hu s)
      _ ≤ 1 - t := by rw [Real.log_exp]; linarith only [hs]
  have hLog := lipschitzWith_iff_dist_le_mul.mp hLip x t
  simp only [NNReal.coe_one, one_mul, dist_eq_norm] at hLog
  calc
    ‖f x - f t‖ = ‖Real.exp (Real.log (f x)) - Real.exp (Real.log (f t))‖ := by
      rw [Real.exp_log (hp x), Real.exp_log (hp t)]
    _ ≤ Real.exp (1-t) * ‖Real.log (f x) - Real.log (f t)‖ :=
      norm_exp_sub_exp_le (h x hx.le) (h t (by linarith))
    _ ≤ Real.exp (1-t) * ‖x - t‖ := mul_le_mul_of_nonneg_left hLog (Real.exp_nonneg _)

/-- The differentiated log-cavity equation for a weighted countable family
of children whose log messages are 1-Lipschitz in log fugacity. -/
theorem hasDerivAt_log_cavityUpdate {w : ℕ → ℝ} (hw : Summable w)
    (hw₀ : ∀ i, 0 ≤ w i) {H : ℕ → ℝ → ℝ} {D : ℕ → ℝ} {t : ℝ}
    (hH₀ : ∀ i s, 0 < H i s) (hH₁ : ∀ i s, H i s ≤ Real.exp (-s))
    (hLip : ∀ i, LipschitzWith 1 (fun s => Real.log (H i s)))
    (hD : ∀ i, HasDerivAt (fun s => Real.log (H i s)) (D i) t) :
    let R := TreeBoundary.update (Real.exp t) w (fun i => H i t)
    HasDerivAt (fun s => Real.log (TreeBoundary.update (Real.exp s) w (fun i => H i s)))
      (-(Real.exp t * R + ∑' i, w i * H i t * R * D i)) t := by
  let G (i : ℕ) (s : ℝ) := w i * H i s
  have hG (s : ℝ) : Summable (fun i => G i s) :=
    Summable.of_nonneg_of_le (fun i => mul_nonneg (hw₀ i) (hH₀ i s).le)
      (fun i => mul_le_mul_of_nonneg_left (hH₁ i s) (hw₀ i))
      (hw.mul_right (Real.exp (-s)))
  have hDerivative (i : ℕ) : HasDerivAt (G i) (w i * (H i t * D i)) t :=
    (hasDerivAt_of_log (hH₀ i) (hD i)).const_mul (w i)
  have hSlope : ∀ᶠ s in 𝓝[≠] t, ∀ i, ‖slope (G i) t s‖ ≤ w i * Real.exp (1 - t) := by
    have hnear : ∀ᶠ s in 𝓝[≠] t, t - 1 < s :=
      nhdsWithin_le_nhds (Ioi_mem_nhds (by linarith : t - 1 < t))
    filter_upwards [hnear, self_mem_nhdsWithin] with s hs hsne
    intro i
    have hsne' : s ≠ t := hsne
    have hsub : 0 < ‖s - t‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hsne')
    rw [slope_def_field, norm_div, div_le_iff₀ hsub]
    have heq : G i s - G i t = w i * (H i s - H i t) := by dsimp only [G]; ring
    rw [heq, norm_mul, Real.norm_of_nonneg (hw₀ i), mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (norm_sub_message_le (hH₀ i) (hH₁ i) (hLip i) hs) (hw₀ i)
  have hsum := hasDerivAt_tsum_of_slope_bound hG (hw.mul_right (Real.exp (1 - t))) hDerivative hSlope
  have hden := (Real.hasDerivAt_exp t).fun_add hsum
  have hpos : 0 < Real.exp t + ∑' i, G i t :=
    add_pos_of_pos_of_nonneg (Real.exp_pos _) (tsum_nonneg fun i => mul_nonneg (hw₀ i) (hH₀ i t).le)
  have hroot := (hden.log hpos.ne').fun_neg
  simp only [TreeBoundary.update]
  simp_rw [Real.log_inv]
  refine hroot.congr_deriv ?_
  dsimp only [G]
  rw [div_eq_mul_inv, add_mul, ← tsum_mul_right]
  congr 2
  exact tsum_congr fun i => by ring

/-- The derivative of a single edge's log correction, with both endpoint log
derivatives made explicit. -/
theorem hasDerivAt_edge_logCorrection {w : ℝ} (hw : 0 ≤ w)
    {A B : ℝ → ℝ} {a b t : ℝ} (hA : ∀ x, 0 < A x) (hB : ∀ x, 0 < B x)
    (ha : HasDerivAt (fun x => Real.log (A x)) a t)
    (hb : HasDerivAt (fun x => Real.log (B x)) b t) :
    HasDerivAt (fun x => Real.log (1 + w * A x * B x))
      (edgeOccupation w (A t) (B t) * (a + b)) t := by
  have h := (((hasDerivAt_of_log hA ha).const_mul w).fun_mul (hasDerivAt_of_log hB hb)).const_add 1
  have hpos : 0 < 1 + w * A t * B t :=
    add_pos_of_pos_of_nonneg one_pos (mul_nonneg (mul_nonneg hw (hA t).le) (hB t).le)
  refine (h.log hpos.ne').congr_deriv ?_
  rw [edgeOccupation]
  ring

/-- After averaging the differentiated recursion and exchanging the two edge
endpoints, their derivative terms cancel in the vertex-minus-edge pressure. -/
theorem hasDerivAt_bethe_after_endpoint_exchange {vertex edge : ℝ → ℝ}
    {dv J₁ J₂ m t : ℝ} (hv : HasDerivAt vertex dv t)
    (he : HasDerivAt edge (J₁ + J₂) t)
    (hrec : -dv = m + J₂) (hswap : J₁ = J₂) :
    HasDerivAt (fun s => -2 * vertex s - edge s) (2 * m) t := by
  refine ((hv.const_mul (-2)).fun_sub he).congr_deriv ?_
  linarith only [hrec, hswap]

open MeasureTheory

/-- Almost every log fugacity admits the termwise formula simultaneously
for the countable child family. -/
theorem ae_hasDerivAt_log_cavityUpdate {w : ℕ → ℝ} (hw : Summable w)
    (hw₀ : ∀ i, 0 ≤ w i) {H : ℕ → ℝ → ℝ}
    (hH₀ : ∀ i s, 0 < H i s) (hH₁ : ∀ i s, H i s ≤ Real.exp (-s))
    (hLip : ∀ i, LipschitzWith 1 (fun s => Real.log (H i s))) :
    ∀ᵐ t : ℝ ∂volume,
      let R := TreeBoundary.update (Real.exp t) w (fun i => H i t)
      HasDerivAt (fun s => Real.log (TreeBoundary.update (Real.exp s) w (fun i => H i s)))
        (-(Real.exp t * R + ∑' i, w i * H i t * R * deriv (fun s => Real.log (H i s)) t)) t := by
  have hd : ∀ᵐ t : ℝ ∂volume, ∀ i, DifferentiableAt ℝ (fun s => Real.log (H i s)) t :=
    ae_all_iff.mpr (fun i => (hLip i).ae_differentiableAt_real)
  filter_upwards [hd] with t ht
  exact hasDerivAt_log_cavityUpdate hw hw₀ hH₀ hH₁ hLip (fun i => (ht i).hasDerivAt)

/-- A local slope envelope justifies differentiation under the expectation
at individual deterministic fugacities with almost sure sample derivatives.
No assumption of everywhere sample differentiability is needed. -/
theorem hasDerivAt_integral_of_slope_envelope {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : ℝ → Ω → ℝ} {f' envelope : Ω → ℝ} {t : ℝ}
    (hf : ∀ s, Integrable (f s) μ) (henv : Integrable envelope μ)
    (hderiv : ∀ᵐ ω ∂μ, HasDerivAt (fun s => f s ω) (f' ω) t)
    (hbound : ∀ᶠ s in 𝓝[≠] t, ∀ᵐ ω ∂μ, ‖slope (fun u => f u ω) t s‖ ≤ envelope ω) :
    HasDerivAt (fun s => ∫ ω, f s ω ∂μ) (∫ ω, f' ω ∂μ) t := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  have hm (s : ℝ) : AEStronglyMeasurable (fun ω => slope (fun u => f u ω) t s) μ := by
    simp only [slope_def_field]
    exact (((hf s).sub (hf t)).div_const (s - t)).aestronglyMeasurable
  have hl :
      Tendsto (fun s => ∫ ω, slope (fun u => f u ω) t s ∂μ) (𝓝[≠] t) (𝓝 (∫ ω, f' ω ∂μ)) :=
    tendsto_integral_filter_of_dominated_convergence envelope (.of_forall hm) hbound henv
      (hderiv.mono fun _ h => h.tendsto_slope)
  refine hl.congr fun s => ?_
  simp only [slope_def_field, integral_div, integral_sub (hf s) (hf t)]

/-- The Bethe function and the integrated local monomer formula agree once
endpoint cancellation supplies the almost-everywhere derivative and the
empty-matching normalization holds at infinity. -/
theorem bethe_eq_pressure_integral_of_ae_deriv {φ m : ℝ → ℝ} (t : ℝ)
    (hAC : ∀ a b : ℝ, AbsolutelyContinuousOnInterval φ a b)
    (hderiv : ∀ᵐ s : ℝ ∂volume, HasDerivAt φ (2 * m s) s)
    (hint : IntegrableOn (fun s => 1 - m s) (Ioi t))
    (htop : Tendsto (fun s => φ s - 2 * s) atTop (𝓝 0)) :
    φ t = 2 * t + 2 * ∫ s in Ioi t, (1 - m s) := by
  let ψ (s : ℝ) := 2 * s - φ s
  have hlinear : LipschitzWith 2 (fun s : ℝ => 2 * s) := by
    apply lipschitzWith_iff_dist_le_mul.mpr
    intro a b
    rw [dist_eq_norm, dist_eq_norm, ← mul_sub, norm_mul]
    norm_num
  have hψ (a b : ℝ) : AbsolutelyContinuousOnInterval ψ a b :=
    hlinear.lipschitzOnWith.absolutelyContinuousOnInterval.sub (hAC a b)
  have hψderiv : ∀ᵐ s : ℝ ∂volume, deriv ψ s = 2 * (1 - m s) := by
    filter_upwards [hderiv] with s hs
    have hlin : HasDerivAt (fun x : ℝ => 2 * x) 2 s := by
      simpa using (hasDerivAt_id s).const_mul 2
    have h := (hlin.fun_sub hs).deriv
    change deriv ψ s = _ at h
    rw [h]
    ring
  have hfinite (u : ℝ) : (∫ s in t..u, 2 * (1 - m s)) = ψ u - ψ t := by
    rw [← (hψ t u).integral_deriv_eq_sub]
    exact intervalIntegral.integral_congr_ae (hψderiv.mono fun _ h _ => h.symm)
  have h1 := intervalIntegral_tendsto_integral_Ioi t (hint.const_mul 2) tendsto_id
  have h2 : Tendsto (fun s => ψ s - ψ t) atTop (𝓝 (0 - ψ t)) := by
    have hlimit : Tendsto ψ atTop (𝓝 0) := by simpa only [ψ, neg_sub, neg_zero] using htop.neg
    exact hlimit.sub_const _
  have heq := tendsto_nhds_unique h1 (h2.congr fun u => (hfinite u).symm)
  rw [integral_const_mul] at heq
  dsimp [ψ] at heq
  linarith only [heq]

end Certificate

import Mathlib.MeasureTheory.Integral.Prod

/-!
# Endpoint exchange for positive monomer fugacity

In the manuscript's positive-fugacity uniqueness proof, Poisson insertion gives
two cross identities, one for each extremal message. This module verifies the
endpoint exchange and the deduction that the extrema agree almost surely.
-/

open MeasureTheory
open scoped MeasureTheory

namespace Certificate.SoftUniqueness

variable {Ω X : Type*} [MeasurableSpace Ω]

/-- Expected occupation between two independent environments, with one using
the lower message and the other the upper message. -/
noncomputable def crossOccupation (μ : Measure Ω) (w : X → ℝ) (L U : Ω → ℝ) (x : X) : ℝ :=
  ∫ p : Ω × Ω, (w x * L p.1 * U p.2) / (1 + w x * L p.1 * U p.2) ∂(μ.prod μ)

/-- The two independent environments have the same underlying law, so interchanging
their roles preserves expected occupation. -/
theorem crossOccupation_swap (μ : Measure Ω) [SFinite μ]
    (w : X → ℝ) (L U : Ω → ℝ) :
    crossOccupation μ w L U = crossOccupation μ w U L := by
  funext x
  unfold crossOccupation
  rw [← integral_prod_swap (μ := μ) (ν := μ) (fun p : Ω × Ω =>
    (w x * L p.1 * U p.2) / (1 + w x * L p.1 * U p.2))]
  apply integral_congr_ae
  filter_upwards with p
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [mul_right_comm (w x) (L p.2) (U p.1)]

variable [MeasurableSpace X]

/-- Two ordered positive-fugacity messages agree almost surely once the cross
occupation identities have been established by Poisson insertion. -/
theorem ae_eq_of_crossOccupation_identities
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure X)
    (w : X → ℝ) (L U : Ω → ℝ) {z : ℝ} (hz : 0 < z)
    (hLm : AEMeasurable L μ) (hUm : AEMeasurable U μ)
    (hL₀ : 0 ≤ᵐ[μ] L) (hLU : L ≤ᵐ[μ] U) (hUmax : U ≤ᵐ[μ] fun _ => z⁻¹)
    (hL : 1 - z * (∫ a, L a ∂μ) = ∫ x, crossOccupation μ w L U x ∂ν)
    (hU : 1 - z * (∫ a, U a ∂μ) = ∫ x, crossOccupation μ w U L x ∂ν) :
    L =ᵐ[μ] U := by
  have hLi : Integrable L μ := by
    apply Integrable.of_bound hLm.aestronglyMeasurable z⁻¹
    filter_upwards [hL₀, hLU, hUmax] with a ha hb hc
    rw [Real.norm_eq_abs, abs_of_nonneg ha]
    exact hb.trans hc
  have hUi : Integrable U μ := by
    apply Integrable.of_bound hUm.aestronglyMeasurable z⁻¹
    filter_upwards [hL₀, hLU, hUmax] with a ha hb hc
    rw [Real.norm_eq_abs, abs_of_nonneg (ha.trans hb)]
    exact hc
  rw [crossOccupation_swap μ w L U] at hL
  apply (integral_eq_iff_of_ae_le hLi hUi hLU).mp
  apply mul_left_cancel₀ hz.ne'
  linarith

end Certificate.SoftUniqueness

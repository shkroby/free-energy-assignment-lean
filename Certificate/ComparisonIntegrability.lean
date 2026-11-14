import Certificate.Comparison
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Absolute integrability in the coupled comparison

The nonnegative exchange identity transfers an absolute first-moment bound
from the root to the child endpoints. The construction of the marked process
and its exchange identity are inputs to this result.
-/

open MeasureTheory
open scoped ENNReal

namespace Certificate

variable {Ω : Type*} [MeasurableSpace Ω]

private theorem weighted_root_bound {a b : ℕ → ℝ} {D : ℝ}
    (ha : HasSum a 1) (hb : HasSum b 1)
    (hap : ∀ i, 0 ≤ a i) (hbp : ∀ i, 0 ≤ b i) :
    (∑' i, ‖(a i - b i) * D‖ₑ) ≤ ‖(2 : ℝ) * D‖ₑ := by
  have hab (i : ℕ) : 0 ≤ (a i + b i) * |D| :=
    mul_nonneg (add_nonneg (hap i) (hbp i)) (abs_nonneg _)
  have hs : HasSum (fun i => (a i + b i) * |D|) ((2 : ℝ) * |D|) := by
    have h : (1 + 1 : ℝ) = 2 := by norm_num
    rw [← h]
    exact (ha.add hb).mul_right _
  rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num),
    ← hs.tsum_eq, ENNReal.ofReal_tsum_of_nonneg hab hs.summable]
  refine ENNReal.tsum_le_tsum (fun i => ?_)
  rw [Real.enorm_eq_ofReal_abs, abs_mul]
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  calc
    |a i - b i| ≤ |a i| + |b i| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (a i) (-b i)
    _ = a i + b i := by rw [abs_of_nonneg (hap i), abs_of_nonneg (hbp i)]

private theorem root_absolute_integral_lt_top
    {μ : Measure Ω} {a b : Ω → ℕ → ℝ} {D : Ω → ℝ}
    (hprob : ∀ᵐ ω ∂μ, HasSum (a ω) 1 ∧ HasSum (b ω) 1 ∧
      (∀ i, 0 ≤ a ω i) ∧ (∀ i, 0 ≤ b ω i))
    (hD : Integrable D μ) :
    (∫⁻ ω, ∑' i, ‖(a ω i - b ω i) * D ω‖ₑ ∂μ) < ∞ := by
  have hroot : (∫⁻ ω, ‖(2 : ℝ) * D ω‖ₑ ∂μ) < ∞ := by
    have h := (hD.const_mul (2 : ℝ)).hasFiniteIntegral
    simpa only [hasFiniteIntegral_iff_enorm] using h
  have hle : (fun ω => ∑' i, ‖(a ω i - b ω i) * D ω‖ₑ) ≤ᵐ[μ]
      (fun ω => ‖(2 : ℝ) * D ω‖ₑ) := by
    filter_upwards [hprob] with ω h
    exact weighted_root_bound h.1 h.2.1 h.2.2.1 h.2.2.2
  exact (lintegral_mono_ae hle).trans_lt hroot

/-- Under the nonnegative endpoint exchange, an integrable root log difference
makes the child comparison absolutely summable almost everywhere and its sum
integrable. The root side is bounded in absolute first moment by twice that
of the root log difference. -/
theorem comparison_integrable_of_abs_exchange
    {μ : Measure Ω} {a b Δ : Ω → ℕ → ℝ} {D : Ω → ℝ}
    (hprob : ∀ᵐ ω ∂μ, HasSum (a ω) 1 ∧ HasSum (b ω) 1 ∧
      (∀ i, 0 ≤ a ω i) ∧ (∀ i, 0 ≤ b ω i))
    (hD : Integrable D μ)
    (hmeas : ∀ i, AEStronglyMeasurable (fun ω => (a ω i - b ω i) * Δ ω i) μ)
    (habs :
      (∫⁻ ω, ∑' i, ‖(a ω i - b ω i) * Δ ω i‖ₑ ∂μ) =
        ∫⁻ ω, ∑' i, ‖(a ω i - b ω i) * D ω‖ₑ ∂μ) :
    (∀ᵐ ω ∂μ, Summable (fun i => |(a ω i - b ω i) * Δ ω i|)) ∧
      Integrable (fun ω => ∑' i, (a ω i - b ω i) * Δ ω i) μ := by
  have hroot := root_absolute_integral_lt_top hprob hD
  have hchild : (∫⁻ ω, ∑' i, ‖(a ω i - b ω i) * Δ ω i‖ₑ ∂μ) < ∞ := by
    rw [habs]
    exact hroot
  have hsum_aemeas : AEMeasurable
      (fun ω => ∑' i, ‖(a ω i - b ω i) * Δ ω i‖ₑ) μ :=
    AEMeasurable.tsum (fun i => (hmeas i).enorm)
  constructor
  · filter_upwards [ae_lt_top' hsum_aemeas hchild.ne] with ω hω
    simpa only [Real.norm_eq_abs] using tsum_enorm_ne_top_iff_summable_norm.mp hω.ne
  · refine ⟨(AEMeasurable.tsum fun i => (hmeas i).aemeasurable).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    exact (lintegral_mono fun ω => enorm_tsum_le_tsum_enorm (f := fun i =>
      (a ω i - b ω i) * Δ ω i)).trans_lt hchild

/-- Equal occupations follow from the signed and nonnegative exchange identities
and the integrable root log difference. The absolute summability and
integrability used by the signed comparison follow from the nonnegative
identity. -/
theorem ae_occupations_eq_of_abs_and_signed_exchange
    {μ : Measure Ω} {a b Δ : Ω → ℕ → ℝ} {D : Ω → ℝ}
    (hprob : ∀ᵐ ω ∂μ, HasSum (a ω) 1 ∧ HasSum (b ω) 1 ∧
      (∀ i, 0 < a ω i) ∧ (∀ i, 0 < b ω i))
    (hfactor : ∀ᵐ ω ∂μ, ∀ i,
      simplexTerm (a ω) (b ω) i = (a ω i - b ω i) * (D ω + Δ ω i))
    (hD : Integrable D μ)
    (hmeas : ∀ i, AEStronglyMeasurable (fun ω => (a ω i - b ω i) * Δ ω i) μ)
    (habs : (∫⁻ ω, ∑' i, ‖(a ω i - b ω i) * Δ ω i‖ₑ ∂μ) =
      ∫⁻ ω, ∑' i, ‖(a ω i - b ω i) * D ω‖ₑ ∂μ)
    (hsigned : (∫ ω, ∑' i, (a ω i - b ω i) * Δ ω i ∂μ) =
      ∫ ω, (∑' i, (a ω i - b ω i)) * D ω ∂μ) :
    ∀ᵐ ω ∂μ, a ω = b ω := by
  have hprob₀ : ∀ᵐ ω ∂μ, HasSum (a ω) 1 ∧ HasSum (b ω) 1 ∧
      (∀ i, 0 ≤ a ω i) ∧ (∀ i, 0 ≤ b ω i) := by
    filter_upwards [hprob] with ω h
    exact ⟨h.1, h.2.1, fun i => (h.2.2.1 i).le, fun i => (h.2.2.2 i).le⟩
  obtain ⟨hchild, hint⟩ := comparison_integrable_of_abs_exchange hprob₀ hD hmeas habs
  exact ae_occupations_eq_of_exchange hprob hfactor
    (hchild.mono (fun _ h => h.of_abs)) hint hsigned

private theorem integral_tsum_eq_parts {μ : Measure Ω} {f : ℕ → Ω → ℝ}
    (hmeas : ∀ i, AEStronglyMeasurable (f i) μ)
    (hfin : (∫⁻ ω, ∑' i, ‖f i ω‖ₑ ∂μ) < ∞) :
    (∫ ω, ∑' i, f i ω ∂μ) =
      (∫⁻ ω, ∑' i, ENNReal.ofReal (f i ω) ∂μ).toReal -
        (∫⁻ ω, ∑' i, ENNReal.ofReal (-f i ω) ∂μ).toReal := by
  let N := fun i => ∫⁻ ω, ‖f i ω‖ₑ ∂μ
  let P := fun i => ∫⁻ ω, ENNReal.ofReal (f i ω) ∂μ
  let M := fun i => ∫⁻ ω, ENNReal.ofReal (-f i ω) ∂μ
  rw [lintegral_tsum (fun i => (hmeas i).enorm)] at hfin
  have hfi (i : ℕ) : Integrable (f i) μ := by
    refine ⟨hmeas i, hasFiniteIntegral_iff_enorm.mpr ?_⟩
    exact (ENNReal.le_tsum (f := N) i).trans_lt hfin
  have p_le (i : ℕ) : P i ≤ N i := lintegral_mono (fun ω => Real.ofReal_le_enorm (f i ω))
  have m_le (i : ℕ) : M i ≤ N i := by
    apply lintegral_mono
    intro ω
    simpa only [enorm_neg] using Real.ofReal_le_enorm (-f i ω)
  have p_fin : (∑' i, P i) ≠ ∞ := ((ENNReal.tsum_le_tsum p_le).trans_lt hfin).ne
  have m_fin : (∑' i, M i) ≠ ∞ := ((ENNReal.tsum_le_tsum m_le).trans_lt hfin).ne
  rw [integral_tsum hmeas hfin.ne,
    lintegral_tsum (fun i => (hmeas i).aemeasurable.ennreal_ofReal),
    lintegral_tsum (f := fun i ω => ENNReal.ofReal (-f i ω))
      (fun i => (hmeas i).aemeasurable.neg.ennreal_ofReal)]
  change (∑' i, ∫ ω, f i ω ∂μ) =
    (∑' i, P i).toReal - (∑' i, M i).toReal
  rw [ENNReal.tsum_toReal_eq (ENNReal.ne_top_of_tsum_ne_top p_fin),
    ENNReal.tsum_toReal_eq (ENNReal.ne_top_of_tsum_ne_top m_fin),
    ← (ENNReal.summable_toReal p_fin).tsum_sub (ENNReal.summable_toReal m_fin)]
  apply tsum_congr
  intro i
  exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hfi i)

/-- A single nonnegative endpoint exchange covers the absolute first moment and
the positive and negative parts of the signed comparison. -/
theorem ae_occupations_eq_of_nonnegative_exchange
    {μ : Measure Ω} {a b Δ : Ω → ℕ → ℝ} {D : Ω → ℝ}
    (hprob : ∀ᵐ ω ∂μ, HasSum (a ω) 1 ∧ HasSum (b ω) 1 ∧
      (∀ i, 0 < a ω i) ∧ (∀ i, 0 < b ω i))
    (hfactor : ∀ᵐ ω ∂μ, ∀ i,
      simplexTerm (a ω) (b ω) i = (a ω i - b ω i) * (D ω + Δ ω i))
    (hD : Integrable D μ)
    (hchild : ∀ i, AEStronglyMeasurable (fun ω => (a ω i - b ω i) * Δ ω i) μ)
    (hroot : ∀ i, AEStronglyMeasurable (fun ω => (a ω i - b ω i) * D ω) μ)
    (hexchange : ∀ g : ℝ → ℝ≥0∞, Measurable g →
      (∫⁻ ω, ∑' i, g ((a ω i - b ω i) * Δ ω i) ∂μ) =
        ∫⁻ ω, ∑' i, g ((a ω i - b ω i) * D ω) ∂μ) :
    ∀ᵐ ω ∂μ, a ω = b ω := by
  have habs := hexchange enorm measurable_enorm
  have hprob₀ : ∀ᵐ ω ∂μ, HasSum (a ω) 1 ∧ HasSum (b ω) 1 ∧
      (∀ i, 0 ≤ a ω i) ∧ (∀ i, 0 ≤ b ω i) := by
    filter_upwards [hprob] with ω h
    exact ⟨h.1, h.2.1, fun i => (h.2.2.1 i).le, fun i => (h.2.2.2 i).le⟩
  have hR := root_absolute_integral_lt_top hprob₀ hD
  have hC : (∫⁻ ω, ∑' i, ‖(a ω i - b ω i) * Δ ω i‖ₑ ∂μ) < ∞ := habs.symm ▸ hR
  have hpos := hexchange ENNReal.ofReal measurable_id.ennreal_ofReal
  have hneg := hexchange (fun x => ENNReal.ofReal (-x)) measurable_id.neg.ennreal_ofReal
  apply ae_occupations_eq_of_abs_and_signed_exchange hprob hfactor hD hchild habs
  rw [integral_tsum_eq_parts hchild hC, hpos, hneg, ← integral_tsum_eq_parts hroot hR]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω => tsum_mul_right

end Certificate

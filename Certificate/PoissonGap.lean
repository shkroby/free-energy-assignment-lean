import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Splitting two exponential gaps

The pair consisting of the first gap and the sum of two independent unit
exponential gaps has density `exp(-s)` on the triangle `0 < a < s`. The
proof uses the Lebesgue measure preserving shear `(a,b) ↦ (a,a+b)`.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Certificate

private noncomputable def expOneWeight (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-x))

private theorem measurable_expOneWeight : Measurable expOneWeight := by
  unfold expOneWeight
  fun_prop

private noncomputable def expOneDensity : ℝ → ℝ≥0∞ :=
  (Ioi (0:ℝ)).indicator expOneWeight

private theorem measurable_expOneDensity : Measurable expOneDensity :=
  measurable_expOneWeight.indicator measurableSet_Ioi

private theorem expMeasure_one_density :
    expMeasure 1 = (volume : Measure ℝ).withDensity expOneDensity := by
  unfold expMeasure gammaMeasure
  apply withDensity_congr_ae
  filter_upwards [(volume : Measure ℝ).ae_ne (0:ℝ)] with x hx
  rcases lt_or_gt_of_ne hx with hn | hp
  · rw [gammaPDF_of_neg hn, expOneDensity,
      indicator_of_notMem (show x ∉ Ioi (0:ℝ) from notMem_Ioi.mpr hn.le)]
  · simp [gammaPDF_of_nonneg hp.le, expOneDensity, expOneWeight, hp, Real.Gamma_one]

private theorem expShear_measurePreserving :
    MeasurePreserving (fun p : ℝ × ℝ => (p.1,p.1+p.2))
      ((volume : Measure ℝ).prod volume) ((volume : Measure ℝ).prod volume) := by
  exact (MeasurePreserving.id (volume : Measure ℝ)).skew_product
    (g := fun a b : ℝ => a+b) (by unfold Function.uncurry; fun_prop)
    (Filter.Eventually.of_forall fun a =>
      (measurePreserving_add_left (volume : Measure ℝ) a).map_eq)

private def splitTriangle : Set (ℝ × ℝ) :=
  {p | 0 < p.1 ∧ p.1 < p.2}

private theorem measurableSet_splitTriangle : MeasurableSet splitTriangle :=
  (measurableSet_lt measurable_const measurable_fst).inter
    (measurableSet_lt measurable_fst measurable_snd)

private theorem expOneDensity_mul_shear (q : ℝ × ℝ) :
    expOneDensity q.1 * expOneDensity q.2 =
      splitTriangle.indicator (fun p => expOneWeight p.2) (q.1,q.1+q.2) := by
  have ht : (q.1, q.1+q.2) ∈ splitTriangle ↔ 0 < q.1 ∧ 0 < q.2 := by
    change (0 < q.1 ∧ q.1 < q.1 + q.2) ↔ 0 < q.1 ∧ 0 < q.2
    simp
  by_cases h₁ : 0 < q.1
  · by_cases h₂ : 0 < q.2
    · rw [expOneDensity, indicator_of_mem (mem_Ioi.mpr h₁), indicator_of_mem (mem_Ioi.mpr h₂),
        indicator_of_mem (ht.mpr ⟨h₁,h₂⟩)]
      simp only [expOneWeight]
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ← neg_add]
    · rw [expOneDensity, indicator_of_notMem (show q.2 ∉ Ioi (0:ℝ) from h₂), mul_zero,
        indicator_of_notMem (fun h => h₂ (ht.mp h).2)]
  · rw [expOneDensity, indicator_of_notMem (show q.1 ∉ Ioi (0:ℝ) from h₁), zero_mul,
      indicator_of_notMem (fun h => h₁ (ht.mp h).1)]

/-- Integration over two iid unit exponential gaps agrees with integration over
an exponential total gap and a Lebesgue split inside that gap. -/
theorem exp_gap_split_lintegral (f : ℝ × ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ p, f (p.1,p.1+p.2) ∂(expMeasure 1).prod (expMeasure 1)) =
      ∫⁻ s, (∫⁻ a in Ioo 0 s, f (a,s)) ∂expMeasure 1 := by
  let V : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod volume
  let D := fun p : ℝ × ℝ => expOneDensity p.1 * expOneDensity p.2
  let G := splitTriangle.indicator (fun p : ℝ × ℝ => expOneWeight p.2 * f p)
  let H := fun s : ℝ => ∫⁻ a in Ioo 0 s, f (a,s)
  have hD : Measurable D :=
    (measurable_expOneDensity.comp measurable_fst).mul
      (measurable_expOneDensity.comp measurable_snd)
  have hG : Measurable G :=
    ((measurable_expOneWeight.comp measurable_snd).mul hf).indicator measurableSet_splitTriangle
  have hH : Measurable H := by
    have hM : Measurable (fun p : ℝ × ℝ => splitTriangle.indicator f p.swap) :=
      (hf.indicator measurableSet_splitTriangle).comp measurable_swap
    have hA := hM.lintegral_prod_right' (ν := volume)
    have heq : H = (fun s => ∫⁻ a, splitTriangle.indicator f (a,s)) := by
      funext s
      change (∫⁻ a in Ioo 0 s, f (a,s)) = _
      rw [← lintegral_indicator measurableSet_Ioo]
      rfl
    rw [heq]
    exact hA
  have hshear : Measurable (fun p : ℝ × ℝ => f (p.1,p.1+p.2)) :=
    hf.comp expShear_measurePreserving.measurable
  have hV : (expMeasure 1).prod (expMeasure 1) = V.withDensity D :=
    by rw [expMeasure_one_density, prod_withDensity measurable_expOneDensity
      measurable_expOneDensity]
  calc
    (∫⁻ p, f (p.1,p.1+p.2) ∂(expMeasure 1).prod (expMeasure 1)) =
      ∫⁻ p, D p * f (p.1,p.1+p.2) ∂V := by
        rw [hV, lintegral_withDensity_eq_lintegral_mul _ hD hshear]
        rfl
    _ = ∫⁻ p, G (p.1,p.1+p.2) ∂V := by
      apply lintegral_congr
      intro p
      change expOneDensity p.1 * expOneDensity p.2 * f (p.1,p.1+p.2) =
        splitTriangle.indicator (fun q => expOneWeight q.2 * f q) (p.1,p.1+p.2)
      rw [expOneDensity_mul_shear, indicator_mul_left]
    _ = ∫⁻ p, G p ∂V := expShear_measurePreserving.lintegral_comp hG
    _ = ∫⁻ s, ∫⁻ a, G (a,s) := lintegral_prod_symm' _ hG
    _ = ∫⁻ s, expOneDensity s * H s := by
      apply lintegral_congr
      intro s
      have he : (fun a => G (a,s)) =
          (Ioo 0 s).indicator (fun a => expOneWeight s * f (a,s)) := rfl
      simp_rw [he]
      rw [lintegral_indicator measurableSet_Ioo, lintegral_const_mul' (expOneWeight s) _
        (by unfold expOneWeight; exact ENNReal.ofReal_ne_top)]
      by_cases hs : 0 < s
      · simp [expOneDensity, hs, H]
      · rw [show H s = 0 by dsimp [H]; rw [Ioo_eq_empty hs, Measure.restrict_empty,
            lintegral_zero_measure]]
        simp [expOneDensity, hs]
    _ = ∫⁻ s, H s ∂expMeasure 1 := by
      rw [expMeasure_one_density, lintegral_withDensity_eq_lintegral_mul _
        measurable_expOneDensity hH]
      rfl

/-- The tail of a unit exponential variable, shifted back by the elapsed
time, is its original law multiplied by the survival probability. -/
theorem exp_one_memoryless_lintegral {t : ℝ} (ht : 0 ≤ t)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x in Ioi t, f (x-t) ∂expMeasure 1) =
      ENNReal.ofReal (Real.exp (-t)) * ∫⁻ x, f x ∂expMeasure 1 := by
  let F := (Ioi t).indicator (fun x => f (x-t))
  have hF : Measurable F := (hf.comp (by fun_prop)).indicator measurableSet_Ioi
  let K := fun x => expOneDensity x * F x
  have hK : Measurable K := measurable_expOneDensity.mul hF
  calc
    (∫⁻ x in Ioi t, f (x-t) ∂expMeasure 1) = ∫⁻ x, K x := by
      rw [← lintegral_indicator measurableSet_Ioi, expMeasure_one_density,
        lintegral_withDensity_eq_lintegral_mul _ measurable_expOneDensity hF]
      rfl
    _ = ∫⁻ y, K (t+y) :=
      ((measurePreserving_add_left (volume : Measure ℝ) t).lintegral_comp hK).symm
    _ = ∫⁻ y, expOneWeight t * (expOneDensity y * f y) := by
      apply lintegral_congr
      intro y
      by_cases hy : 0 < y
      · have hp : 0 < t+y := add_pos_of_nonneg_of_pos ht hy
        have htp : t < t+y := lt_add_of_pos_right _ hy
        simp only [K, F, expOneDensity, indicator_of_mem (mem_Ioi.mpr hp),
          indicator_of_mem (mem_Ioi.mpr hy), indicator_of_mem (mem_Ioi.mpr htp),
          add_sub_cancel_left, expOneWeight, neg_add, Real.exp_add,
          ENNReal.ofReal_mul (Real.exp_pos _).le, mul_assoc]
      · simp [K, F, expOneDensity, hy]
    _ = expOneWeight t * ∫⁻ y, f y ∂expMeasure 1 := by
      rw [lintegral_const_mul' (expOneWeight t) _ (by unfold expOneWeight; exact ENNReal.ofReal_ne_top),
        expMeasure_one_density,
        lintegral_withDensity_eq_lintegral_mul _ measurable_expOneDensity hf]
      rfl

end Certificate

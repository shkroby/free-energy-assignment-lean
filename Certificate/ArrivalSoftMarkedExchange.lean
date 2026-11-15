import Certificate.ArrivalHardCoupling
import Certificate.ArrivalSoftExchange

/-! Mecke's formula with additional marks carried by occupied edges. -/

open MeasureTheory Set
open scoped ENNReal

namespace Certificate

/-- Occupation of a child edge at positive fugacity on the paired mark space.
Only the mark's first coordinate enters the recursion. -/
noncomputable def softMarkedOccupation (β d z : ℝ)
    (ω : PairedArrivalConfiguration) (i : ℕ) : ℝ :=
  Real.exp (-β * arrivalLength d ω.1 i) * (ω.2 i).1 *
    arrivalSoftOutput β d z (firstArrivalConfiguration ω)

private theorem softMarkedOccupation_reinsert {β d z : ℝ} (hz : 0 < z)
    (ω : PairedArrivalConfiguration) (i : ℕ)
    (hfin : arrivalWeightedSum β d (firstArrivalConfiguration ω) ≠ ∞)
    (hmark : 0 ≤ (ω.2 i).1) :
    softMarkedOccupation β d z ω i = edgeOccupation (Real.exp (-β * arrivalLength d ω.1 i))
      (ω.2 i).1 (arrivalSoftOutput β d z
        (firstArrivalConfiguration (eraseArrivalGap i ω.1, eraseSequence i ω.2))) := by
  let ω' := firstArrivalConfiguration (eraseArrivalGap i ω.1, eraseSequence i ω.2)
  have hω' : ω' = (eraseArrivalGap i ω.1, eraseSequence i (firstArrivalConfiguration ω).2) := rfl
  let w := Real.exp (-β * arrivalLength d ω.1 i)
  let m := (ω.2 i).1
  have hrestore : arrivalWeightedSum β d ω' + ENNReal.ofReal (w * m) =
      arrivalWeightedSum β d (firstArrivalConfiguration ω) := by
    rw [hω']
    exact arrivalWeightedSum_erase_add β d (firstArrivalConfiguration ω) i
  have hfin' : arrivalWeightedSum β d ω' ≠ ∞ :=
    ne_top_of_le_ne_top hfin (le_self_add.trans_eq hrestore)
  have hr := congrArg ENNReal.toReal hrestore
  rw [ENNReal.toReal_add hfin' ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (mul_nonneg (Real.exp_nonneg _) hmark)] at hr
  let S := (arrivalWeightedSum β d ω').toReal
  have hS : 0 ≤ S := ENNReal.toReal_nonneg
  have hW : 0 ≤ w * m := mul_nonneg (Real.exp_nonneg _) hmark
  unfold softMarkedOccupation arrivalSoftOutput edgeOccupation
  change w * m * (z + (arrivalWeightedSum β d (firstArrivalConfiguration ω)).toReal)⁻¹ =
    w * m * (z + S)⁻¹ / (1 + w * m * (z + S)⁻¹)
  rw [← hr]
  change w * m * (z + (S + w * m))⁻¹ =
    w * m * (z + S)⁻¹ / (1 + w * m * (z + S)⁻¹)
  have hzS : 0 < z + S := by positivity
  have hzSm : 0 < z + (S + w * m) := by positivity
  have hden : 0 < 1 + w * m * (z + S)⁻¹ := by positivity
  field_simp [hzS.ne', hzSm.ne', hden.ne']
  ring

/-- On the canonical marked process, a nonnegative test of an occupied
child mark integrates against the intensity, the child law, and an
independent cavity message at the other end. -/
theorem lintegral_soft_marked_occupation {β d z : ℝ} (hd : 0 < d) (hz : 0 < z)
    (ρ : Measure (ℝ × ℝ)) [IsProbabilityMeasure ρ] (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hproj : ρ.map Prod.fst = μ)
    (hLaw : (markedSpacings μ).map (arrivalSoftOutput β d z) = μ)
    (hfin : ∀ᵐ ω ∂markedSpacings μ, arrivalWeightedSum β d ω ≠ ∞)
    (hmark : ∀ᵐ ω ∂markedArrivalSequenceLaw ρ, ∀ i, 0 ≤ (ω.2 i).1)
    (f : ℝ × (ℝ × ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, ∑' i, ENNReal.ofReal (softMarkedOccupation β d z ω i) *
        f (arrivalLength d ω.1 i, ω.2 i) ∂markedArrivalSequenceLaw ρ) =
      ∫⁻ x, ∫⁻ B, ∫⁻ A, ENNReal.ofReal (edgeOccupation (Real.exp (-β * x)) B.1 A) *
        f (x, B) ∂μ ∂ρ ∂intensity d := by
  let P := markedArrivalSequenceLaw ρ
  let : IsProbabilityMeasure P := isProbabilityMeasure_markedArrivalSequenceLaw ρ
  let root := arrivalSoftOutput β d z ∘ firstArrivalConfiguration
  have hr : Measurable root := (measurable_arrivalSoftOutput ..).comp
    measurable_firstArrivalConfiguration
  have hp : MeasurePreserving firstArrivalConfiguration P (markedSpacings μ) := by
    rw [← hproj]
    exact markedArrival_projection ρ Prod.fst measurable_fst
  have hroot : P.map root = μ := by
    rw [← Measure.map_map (measurable_arrivalSoftOutput ..) measurable_firstArrivalConfiguration,
      hp.map_eq, hLaw]
  let G : (ℝ × (ℝ × ℝ)) × PairedArrivalConfiguration → ℝ≥0∞ :=
    fun p ↦ ENNReal.ofReal (edgeOccupation (Real.exp (-β * p.1.1)) p.1.2.1 (root p.2)) * f p.1
  have hG : Measurable G := by
    apply Measurable.mul _ (hf.comp measurable_fst)
    have hr' : Measurable (fun p : (ℝ × (ℝ × ℝ)) × PairedArrivalConfiguration ↦ root p.2) :=
      hr.comp measurable_snd
    unfold edgeOccupation
    fun_prop
  have hMecke := canonical_iid_marked_arrival_insertion hd ρ G hG
  calc
    _ = ∫⁻ ω, ∑' i, G ((arrivalLength d ω.1 i, ω.2 i),
        (eraseArrivalGap i ω.1, eraseSequence i ω.2)) ∂P := by
      apply lintegral_congr_ae
      filter_upwards [hp.quasiMeasurePreserving.tendsto_ae.eventually hfin, hmark] with ω hω hm
      apply tsum_congr
      intro i
      exact congrArg (fun x ↦ ENNReal.ofReal x * f (arrivalLength d ω.1 i, ω.2 i))
        (softMarkedOccupation_reinsert hz ω i hω (hm i))
    _ = ∫⁻ p, G p ∂((intensity d).prod ρ).prod P := hMecke
    _ = _ := by
      rw [lintegral_prod _ hG.aemeasurable, lintegral_prod _ hG.lintegral_prod_right'.aemeasurable]
      apply lintegral_congr
      intro x
      apply lintegral_congr
      intro B
      rw [← hroot, lintegral_map _ hr]
      unfold edgeOccupation
      fun_prop

end Certificate

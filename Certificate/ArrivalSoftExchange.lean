import Certificate.ArrivalDeletion
import Certificate.BatchSoftExchange
import Certificate.PoissonArrivalMecke

/-!
# Positive-fugacity exchange on the exponential arrivals

The canonical marked Mecke identity and the exact effect of deleting an
arrival yield the vacancy-deficit identity for the actual recursive model.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Certificate

private noncomputable def arrivalMarkWeight (β : ℝ) (p : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-β * p.1) * p.2)

/-- The crossed occupancy identity for the actual exponential arrival process. -/
theorem arrivalOccupationMass_eq_mean_vacancy_deficit {β d z : ℝ}
    (hd : 0 < d) (hz : 0 < z)
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x)
    (hfin : ∀ᵐ ω ∂markedSpacings μ, arrivalWeightedSum β d ω ≠ ∞)
    (hLaw : (markedSpacings μ).map (arrivalSoftOutput β d z) = ν) :
    occupationMassBetween β d μ ν = ∫⁻ x, ENNReal.ofReal (1 - z * x) ∂ν := by
  let P := markedSpacings μ
  let : IsProbabilityMeasure P := isProbabilityMeasure_markedArrivalSequenceLaw μ
  let Z := ENNReal.ofReal z
  let g : (ℝ × ℝ) × ArrivalConfiguration → ℝ≥0∞ := fun p ↦
    arrivalMarkWeight β p.1 / (Z + (arrivalWeightedSum β d p.2 + arrivalMarkWeight β p.1))
  have hg : Measurable g := by
    have hW : Measurable (arrivalMarkWeight β) := by unfold arrivalMarkWeight; fun_prop
    have hSW := (measurable_arrivalWeightedSum β d).comp
      (measurable_snd : Measurable (Prod.snd : (ℝ × ℝ) × ArrivalConfiguration → _))
    exact (hW.comp measurable_fst).div
      (measurable_const.add (hSW.add (hW.comp measurable_fst)))
  have hMecke := canonical_marked_arrival_insertion hd μ g hg
  have hrestore (ω : ArrivalConfiguration) :
      (∑' i, g ((arrivalLength d ω.1 i, ω.2 i),
        (eraseArrivalGap i ω.1, eraseSequence i ω.2))) =
      arrivalWeightedSum β d ω / (Z + arrivalWeightedSum β d ω) := by
    unfold arrivalWeightedSum
    rw [div_eq_mul_inv, ← ENNReal.tsum_mul_right]
    apply tsum_congr
    intro i
    change ENNReal.ofReal (cavityTerm β d ω i) /
      (Z + (arrivalWeightedSum β d (eraseArrivalGap i ω.1, eraseSequence i ω.2) +
        ENNReal.ofReal (cavityTerm β d ω i))) = _
    rw [arrivalWeightedSum_erase_add, div_eq_mul_inv]
    rfl
  simp_rw [hrestore] at hMecke
  have hLeft :
      (∫⁻ ω, arrivalWeightedSum β d ω / (Z + arrivalWeightedSum β d ω) ∂P) =
        ∫⁻ x, ENNReal.ofReal (1 - z * x) ∂ν := by
    rw [← hLaw, lintegral_map (by fun_prop) (measurable_arrivalSoftOutput _ _ _)]
    apply lintegral_congr_ae
    filter_upwards [hfin] with ω hf
    let S := (arrivalWeightedSum β d ω).toReal
    have hS : 0 ≤ S := ENNReal.toReal_nonneg
    have hsum : arrivalWeightedSum β d ω = ENNReal.ofReal S :=
      (ENNReal.ofReal_toReal hf).symm
    have hterm : (S / (z + S)) = 1 - z * (z + S)⁻¹ := by
      field_simp
      ring
    change arrivalWeightedSum β d ω / (ENNReal.ofReal z + arrivalWeightedSum β d ω) =
      ENNReal.ofReal (1 - z * (z + S)⁻¹)
    rw [hsum, ← ENNReal.ofReal_add hz.le hS, ← ENNReal.ofReal_div_of_pos (by positivity), hterm]
  have hRight : (∫⁻ p, g p ∂((intensity d).prod μ).prod P) =
      occupationMassBetween β d μ ν := by
    rw [lintegral_prod _ hg.aemeasurable]
    unfold occupationMassBetween
    have hmeas : Measurable (fun x : (ℝ × ℝ) ↦ ∫⁻ ω, g (x, ω) ∂P) :=
      hg.lintegral_prod_right'
    rw [lintegral_prod _ hmeas.aemeasurable]
    apply lintegral_congr
    intro x
    have hmeas_inner : Measurable (fun p : ℝ × ℝ ↦
        ENNReal.ofReal (edgeOccupation (Real.exp (-β * x)) p.1 p.2)) := by
      unfold edgeOccupation
      fun_prop
    rw [lintegral_prod _ hmeas_inner.aemeasurable]
    apply lintegral_congr_ae
    filter_upwards [hμ] with h hh
    rw [← hLaw, lintegral_map (by unfold edgeOccupation; fun_prop)
      (measurable_arrivalSoftOutput _ _ _)]
    apply lintegral_congr_ae
    filter_upwards [hfin] with ω hf
    let W := Real.exp (-β * x) * h
    let S := (arrivalWeightedSum β d ω).toReal
    have hW : 0 ≤ W := mul_nonneg (Real.exp_nonneg _) hh
    have hS : 0 ≤ S := ENNReal.toReal_nonneg
    have hsum : arrivalWeightedSum β d ω = ENNReal.ofReal S :=
      (ENNReal.ofReal_toReal hf).symm
    change ENNReal.ofReal W / (ENNReal.ofReal z + (arrivalWeightedSum β d ω + ENNReal.ofReal W)) =
      ENNReal.ofReal (edgeOccupation (Real.exp (-β * x)) h (z + S)⁻¹)
    rw [hsum, ← ENNReal.ofReal_add hS hW, ← ENNReal.ofReal_add hz.le (add_nonneg hS hW),
      ← ENNReal.ofReal_div_of_pos (by positivity)]
    congr 1
    change W / (z + (S + W)) = W * (z + S)⁻¹ / (1 + W * (z + S)⁻¹)
    have hden : 0 < z + S := by positivity
    have hden' : 0 < z + (S + W) := by positivity
    have hden'' : 0 < 1 + W * (z + S)⁻¹ := by positivity
    field_simp
    ring
  calc
    _ = ∫⁻ p, g p ∂((intensity d).prod μ).prod P := hRight.symm
    _ = ∫⁻ ω, arrivalWeightedSum β d ω / (Z + arrivalWeightedSum β d ω) ∂P := hMecke.symm
    _ = _ := hLeft

/-- The canonical crossed-recursion comparison, using the proved insertion
identity on exponential arrivals. -/
theorem ae_eq_of_ordered_crossed_arrival_recursions
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {d β z : ℝ} (hd : 0 < d) (hβ : 0 < β) (hz : 0 < z)
    {L U : A → ℝ} (hL : Measurable L) (hU : Measurable U)
    (hb : ∀ᵐ x ∂P, 0 ≤ L x ∧ L x ≤ U x ∧ U x ≤ z⁻¹)
    (hLower : (markedSpacings (P.map U)).map (arrivalSoftOutput β d z) = P.map L)
    (hUpper : (markedSpacings (P.map L)).map (arrivalSoftOutput β d z) = P.map U) :
    L =ᵐ[P] U := by
  let : IsProbabilityMeasure (P.map L) := Measure.isProbabilityMeasure_map hL.aemeasurable
  let : IsProbabilityMeasure (P.map U) := Measure.isProbabilityMeasure_map hU.aemeasurable
  have hL₀ : 0 ≤ᵐ[P.map L] (fun x : ℝ ↦ x) :=
    (ae_map_iff hL.aemeasurable measurableSet_Ici).mpr (hb.mono fun _ h ↦ h.1)
  have hU₀ : 0 ≤ᵐ[P.map U] (fun x : ℝ ↦ x) :=
    (ae_map_iff hU.aemeasurable measurableSet_Ici).mpr (hb.mono fun _ h ↦ h.1.trans h.2.1)
  have hLmax : ∀ᵐ x ∂P.map L, x ∈ Icc 0 z⁻¹ :=
    (ae_map_iff hL.aemeasurable measurableSet_Icc).mpr
      (hb.mono fun _ h ↦ ⟨h.1, h.2.1.trans h.2.2⟩)
  have hUmax : ∀ᵐ x ∂P.map U, x ∈ Icc 0 z⁻¹ :=
    (ae_map_iff hU.aemeasurable measurableSet_Icc).mpr
      (hb.mono fun _ h ↦ ⟨h.1.trans h.2.1, h.2.2⟩)
  have hfin (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : ∀ᵐ x ∂μ, x ∈ Icc 0 z⁻¹) :
      ∀ᵐ ω ∂markedSpacings μ, arrivalWeightedSum β d ω ≠ ∞ := by
    filter_upwards [ae_arrivalWeightedSum_eq_ofReal_tsum hd hβ μ hμ] with ω hω
    rw [hω]
    exact ENNReal.ofReal_ne_top
  have hLmass := arrivalOccupationMass_eq_mean_vacancy_deficit hd hz (P.map U) (P.map L)
    hU₀ (hfin _ hUmax) hLower
  have hUmass := arrivalOccupationMass_eq_mean_vacancy_deficit hd hz (P.map L) (P.map U)
    hL₀ (hfin _ hLmax) hUpper
  rw [occupationMassBetween_swap] at hLmass
  have heq := hLmass.symm.trans hUmass
  rw [lintegral_map (by fun_prop) hL, lintegral_map (by fun_prop) hU] at heq
  exact ae_eq_of_ordered_of_equal_vacancy_deficit P hz hL hU hb heq

end Certificate

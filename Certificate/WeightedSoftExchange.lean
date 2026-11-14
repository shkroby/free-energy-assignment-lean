import Certificate.ArrivalDeletion
import Certificate.BatchSoftExchange
import Certificate.PoissonArrivalMecke

/-! Marked endpoint exchange for a nonnegative edge-weight kernel. -/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Certificate

noncomputable def kernelMarkWeight (K : ℝ → ℝ) (p : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (K p.1 * p.2)

noncomputable def kernelWeightedSum (K : ℝ → ℝ) (d : ℝ) (ω : ArrivalConfiguration) : ℝ≥0∞ :=
  ∑' i, kernelMarkWeight K (arrivalLength d ω.1 i, ω.2 i)

theorem measurable_kernelWeightedSum (d : ℝ) {K : ℝ → ℝ} (hK : Measurable K) :
    Measurable (kernelWeightedSum K d) := by
  apply Measurable.tsum
  intro i
  have hx : Measurable (fun ω : ArrivalConfiguration => arrivalLength d ω.1 i) := by
    unfold arrivalLength
    fun_prop
  exact ((hK.comp hx).mul ((measurable_pi_apply i).comp measurable_snd)).ennreal_ofReal

noncomputable def kernelSoftOutput (K : ℝ → ℝ) (d z : ℝ) (ω : ArrivalConfiguration) : ℝ :=
  (z + (kernelWeightedSum K d ω).toReal)⁻¹

theorem measurable_kernelSoftOutput (d z : ℝ) {K : ℝ → ℝ} (hK : Measurable K) :
    Measurable (kernelSoftOutput K d z) :=
  (measurable_const.add (measurable_kernelWeightedSum d hK).ennreal_toReal).inv

private theorem kernelWeightedSum_erase_add (K : ℝ → ℝ) (d : ℝ)
    (ω : ArrivalConfiguration) (i : ℕ) :
    kernelWeightedSum K d (eraseArrivalGap i ω.1, eraseSequence i ω.2) +
      kernelMarkWeight K (arrivalLength d ω.1 i, ω.2 i) = kernelWeightedSum K d ω := by
  let f : ℕ → ℝ≥0∞ := fun j => kernelMarkWeight K (arrivalLength d ω.1 j, ω.2 j)
  let g : ℕ → ℝ≥0∞ := fun j =>
    kernelMarkWeight K (arrivalLength d (eraseArrivalGap i ω.1) j, eraseSequence i ω.2 j)
  have hg (j : ℕ) : g j = if j < i then f j else f (j + 1) := by
    dsimp only [g, f]
    rw [arrivalLength_eraseGap]
    by_cases hj : j < i
    · rw [if_pos hj, if_pos hj, eraseSequence_apply_of_lt ω.2 hj]
    · rw [if_neg hj, if_neg hj, eraseSequence_apply_of_ge ω.2 (le_of_not_gt hj)]
  change (∑' j, g j) + f i = ∑' j, f j
  exact tsum_nat_skip_add i hg

noncomputable def kernelOccupationMass (K : ℝ → ℝ) (d : ℝ) (μ ν : Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ∫⁻ p : ℝ × ℝ, ENNReal.ofReal
    (edgeOccupation (K x) p.1 p.2) ∂(μ.prod ν) ∂intensity d

theorem kernelOccupationMass_swap (K : ℝ → ℝ) (d : ℝ) (μ ν : Measure ℝ)
    [SFinite μ] [SFinite ν] :
    kernelOccupationMass K d μ ν = kernelOccupationMass K d ν μ := by
  unfold kernelOccupationMass
  apply lintegral_congr
  intro x
  rw [← Measure.prod_swap, lintegral_map (by unfold edgeOccupation; fun_prop) measurable_swap]
  apply lintegral_congr
  intro p
  exact congrArg ENNReal.ofReal (edgeOccupation_swap _ _ _)

/-- The crossed occupancy identity for the actual exponential arrival process. -/
theorem kernelOccupationMass_eq_mean_vacancy_deficit {K : ℝ → ℝ} {d z : ℝ}
    (hK : Measurable K) (hK₀ : ∀ x, 0 ≤ K x) (hd : 0 < d) (hz : 0 < z)
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x)
    (hfin : ∀ᵐ ω ∂markedSpacings μ, kernelWeightedSum K d ω ≠ ∞)
    (hLaw : (markedSpacings μ).map (kernelSoftOutput K d z) = ν) :
    kernelOccupationMass K d μ ν = ∫⁻ x, ENNReal.ofReal (1 - z * x) ∂ν := by
  let P := markedSpacings μ
  let : IsProbabilityMeasure P := isProbabilityMeasure_markedArrivalSequenceLaw μ
  let Z := ENNReal.ofReal z
  let g : (ℝ × ℝ) × ArrivalConfiguration → ℝ≥0∞ := fun p ↦
    kernelMarkWeight K p.1 / (Z + (kernelWeightedSum K d p.2 + kernelMarkWeight K p.1))
  have hg : Measurable g := by
    have hW : Measurable (kernelMarkWeight K) :=
      ((hK.comp measurable_fst).mul measurable_snd).ennreal_ofReal
    have hSW := (measurable_kernelWeightedSum d hK).comp
      (measurable_snd : Measurable (Prod.snd : (ℝ × ℝ) × ArrivalConfiguration → _))
    exact (hW.comp measurable_fst).div
      (measurable_const.add (hSW.add (hW.comp measurable_fst)))
  have hMecke := canonical_marked_arrival_insertion hd μ g hg
  have hrestore (ω : ArrivalConfiguration) :
      (∑' i, g ((arrivalLength d ω.1 i, ω.2 i),
        (eraseArrivalGap i ω.1, eraseSequence i ω.2))) =
      kernelWeightedSum K d ω / (Z + kernelWeightedSum K d ω) := by
    unfold kernelWeightedSum
    rw [div_eq_mul_inv, ← ENNReal.tsum_mul_right]
    apply tsum_congr
    intro i
    change kernelMarkWeight K (arrivalLength d ω.1 i, ω.2 i) /
      (Z + (kernelWeightedSum K d (eraseArrivalGap i ω.1, eraseSequence i ω.2) +
        kernelMarkWeight K (arrivalLength d ω.1 i, ω.2 i))) = _
    rw [kernelWeightedSum_erase_add, div_eq_mul_inv]
    rfl
  simp_rw [hrestore] at hMecke
  have hLeft :
      (∫⁻ ω, kernelWeightedSum K d ω / (Z + kernelWeightedSum K d ω) ∂P) =
        ∫⁻ x, ENNReal.ofReal (1 - z * x) ∂ν := by
    rw [← hLaw, lintegral_map (by fun_prop) (measurable_kernelSoftOutput d z hK)]
    apply lintegral_congr_ae
    filter_upwards [hfin] with ω hf
    let S := (kernelWeightedSum K d ω).toReal
    have hS : 0 ≤ S := ENNReal.toReal_nonneg
    have hsum : kernelWeightedSum K d ω = ENNReal.ofReal S :=
      (ENNReal.ofReal_toReal hf).symm
    have hterm : (S / (z + S)) = 1 - z * (z + S)⁻¹ := by
      field_simp
      ring
    change kernelWeightedSum K d ω / (ENNReal.ofReal z + kernelWeightedSum K d ω) =
      ENNReal.ofReal (1 - z * (z + S)⁻¹)
    rw [hsum, ← ENNReal.ofReal_add hz.le hS, ← ENNReal.ofReal_div_of_pos (by positivity), hterm]
  have hRight : (∫⁻ p, g p ∂((intensity d).prod μ).prod P) =
      kernelOccupationMass K d μ ν := by
    rw [lintegral_prod _ hg.aemeasurable]
    unfold kernelOccupationMass
    have hmeas : Measurable (fun x : (ℝ × ℝ) ↦ ∫⁻ ω, g (x, ω) ∂P) :=
      hg.lintegral_prod_right'
    rw [lintegral_prod _ hmeas.aemeasurable]
    apply lintegral_congr
    intro x
    have hmeas_inner : Measurable (fun p : ℝ × ℝ ↦
        ENNReal.ofReal (edgeOccupation (K x) p.1 p.2)) := by
      unfold edgeOccupation
      fun_prop
    rw [lintegral_prod _ hmeas_inner.aemeasurable]
    apply lintegral_congr_ae
    filter_upwards [hμ] with h hh
    rw [← hLaw, lintegral_map (by unfold edgeOccupation; fun_prop)
      (measurable_kernelSoftOutput d z hK)]
    apply lintegral_congr_ae
    filter_upwards [hfin] with ω hf
    let W := K x * h
    let S := (kernelWeightedSum K d ω).toReal
    have hW : 0 ≤ W := mul_nonneg (hK₀ x) hh
    have hS : 0 ≤ S := ENNReal.toReal_nonneg
    have hsum : kernelWeightedSum K d ω = ENNReal.ofReal S :=
      (ENNReal.ofReal_toReal hf).symm
    change ENNReal.ofReal W / (ENNReal.ofReal z + (kernelWeightedSum K d ω + ENNReal.ofReal W)) =
      ENNReal.ofReal (edgeOccupation (K x) h (z + S)⁻¹)
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
    _ = ∫⁻ ω, kernelWeightedSum K d ω / (Z + kernelWeightedSum K d ω) ∂P := hMecke.symm
    _ = _ := hLeft

theorem ae_kernelWeightedSum_ne_top {K : ℝ → ℝ} {d M : ℝ} (hK₀ : ∀ x, 0 ≤ K x)
    (hKS : ∀ᵐ E ∂exponentialSpacings, Summable (fun i => K (arrivalLength d E i)))
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hb : ∀ᵐ x ∂μ, x ∈ Icc 0 M) :
    ∀ᵐ ω ∂markedSpacings μ, kernelWeightedSum K d ω ≠ ∞ := by
  let : IsProbabilityMeasure exponentialSpacings := isProbabilityMeasure_exponentialSpacings
  let Q := Measure.infinitePi (fun _ : ℕ => μ)
  have hmarks : ∀ᵐ T ∂Q, ∀ i, T i ∈ Icc 0 M := by
    apply ae_all_iff.mpr
    intro i
    have H := measurePreserving_eval_infinitePi (fun _ : ℕ => μ) i
    exact H.quasiMeasurePreserving.tendsto_ae.eventually hb
  have he : ∀ᵐ ω ∂markedSpacings μ, Summable (fun i => K (arrivalLength d ω.1 i)) := by
    have HF := measurePreserving_fst (μ := exponentialSpacings) (ν := Q)
    exact HF.quasiMeasurePreserving.tendsto_ae.eventually hKS
  have hm : ∀ᵐ ω ∂markedSpacings μ, ∀ i, ω.2 i ∈ Icc 0 M := by
    have HS := measurePreserving_snd (μ := exponentialSpacings) (ν := Q)
    exact HS.quasiMeasurePreserving.tendsto_ae.eventually hmarks
  filter_upwards [he, hm] with ω hs hT
  let f (i : ℕ) := K (arrivalLength d ω.1 i) * ω.2 i
  have hf₀ (i : ℕ) : 0 ≤ f i := mul_nonneg (hK₀ _) (hT i).1
  have hf : Summable f := (hs.mul_right M).of_nonneg_of_le hf₀
    (fun i => mul_le_mul_of_nonneg_left (hT i).2 (hK₀ _))
  change (∑' i, ENNReal.ofReal (f i)) ≠ ∞
  rw [← ENNReal.ofReal_tsum_of_nonneg hf₀ hf]
  exact ENNReal.ofReal_ne_top

/-- Ordered solutions of the two crossed recursions agree for every
nonnegative measurable edge-weight kernel with almost surely summable weights. -/
theorem ae_eq_of_ordered_crossed_kernel_recursions
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {K : ℝ → ℝ} {d z : ℝ} (hK : Measurable K) (hK₀ : ∀ x, 0 ≤ K x)
    (hd : 0 < d) (hz : 0 < z)
    (hKS : ∀ᵐ E ∂exponentialSpacings, Summable (fun i => K (arrivalLength d E i)))
    {L U : A → ℝ} (hL : Measurable L) (hU : Measurable U)
    (hb : ∀ᵐ x ∂P, 0 ≤ L x ∧ L x ≤ U x ∧ U x ≤ z⁻¹)
    (hLower : (markedSpacings (P.map U)).map (kernelSoftOutput K d z) = P.map L)
    (hUpper : (markedSpacings (P.map L)).map (kernelSoftOutput K d z) = P.map U) :
    L =ᵐ[P] U := by
  let : IsProbabilityMeasure (P.map L) := Measure.isProbabilityMeasure_map hL.aemeasurable
  let : IsProbabilityMeasure (P.map U) := Measure.isProbabilityMeasure_map hU.aemeasurable
  have hzero : MeasurableSet {x : ℝ | 0 ≤ x} :=
    measurableSet_le measurable_const measurable_id
  have hL₀ : ∀ᵐ x ∂P.map L, 0 ≤ x :=
    (ae_map_iff hL.aemeasurable hzero).mpr (hb.mono fun _ h => h.1)
  have hU₀ : ∀ᵐ x ∂P.map U, 0 ≤ x :=
    (ae_map_iff hU.aemeasurable hzero).mpr (hb.mono fun _ h => h.1.trans h.2.1)
  have hLmax : ∀ᵐ x ∂P.map L, x ∈ Icc 0 z⁻¹ :=
    (ae_map_iff hL.aemeasurable measurableSet_Icc).mpr
      (hb.mono fun _ h => ⟨h.1, h.2.1.trans h.2.2⟩)
  have hUmax : ∀ᵐ x ∂P.map U, x ∈ Icc 0 z⁻¹ :=
    (ae_map_iff hU.aemeasurable measurableSet_Icc).mpr
      (hb.mono fun _ h => ⟨h.1.trans h.2.1, h.2.2⟩)
  have hLmass := kernelOccupationMass_eq_mean_vacancy_deficit hK hK₀ hd hz (P.map U) (P.map L)
    hU₀ (ae_kernelWeightedSum_ne_top hK₀ hKS _ hUmax) hLower
  have hUmass := kernelOccupationMass_eq_mean_vacancy_deficit hK hK₀ hd hz (P.map L) (P.map U)
    hL₀ (ae_kernelWeightedSum_ne_top hK₀ hKS _ hLmax) hUpper
  rw [kernelOccupationMass_swap] at hLmass
  have heq := hLmass.symm.trans hUmass
  rw [lintegral_map (by fun_prop) hL, lintegral_map (by fun_prop) hU] at heq
  exact ae_eq_of_ordered_of_equal_vacancy_deficit P hz hL hU hb heq

end Certificate

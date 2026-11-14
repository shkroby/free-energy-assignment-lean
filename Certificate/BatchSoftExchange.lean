import Certificate.CavityMedianTail
import Certificate.Endpoints

/-!
# Positive-fugacity endpoint exchange on the marked Poisson batches

The deletion identity removes one actual point and then restores that point
in the normalization denominator. Applying marked insertion yields the expected
occupation of an edge between independent endpoint messages.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Certificate

private noncomputable def markWeight (β : ℝ) (p : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-β * p.1) * p.2)

private theorem partition_remove_add (β : ℝ) (ω : PWITConfiguration)
    (j : ℕ) (i : Fin (ω j).1) :
    pwitWeightedSum β (Function.update ω j (erasePoissonMark i.val (ω j))) +
      markWeight β ((ω j).2 i) = pwitWeightedSum β ω := by
  classical
  have hbatch (b : PoissonBatch (ℝ × ℝ)) (i : Fin b.1) :
      poissonBatchSum (0, 0) (markWeight β) (erasePoissonMark i.val b) +
        markWeight β (b.2 i) = poissonBatchSum (0, 0) (markWeight β) b := by
    obtain ⟨n, a⟩ := b
    cases n with
    | zero => exact Fin.elim0 i
    | succ n =>
      rw [show erasePoissonMark i.val (⟨n + 1, a⟩ : PoissonBatch (ℝ × ℝ)) =
          ⟨n, fun k ↦ a (i.succAbove k)⟩ by
        simp only [erasePoissonMark, dif_pos i.isLt]]
      rw [poissonBatchSum_eq_sum, poissonBatchSum_eq_sum, add_comm]
      exact (Fin.sum_univ_succAbove (fun k ↦ markWeight β (a k)) i).symm
  let T : ℕ → ℝ≥0∞ := fun k ↦ poissonBatchSum (0, 0) (markWeight β) (ω k)
  let S : ℕ → ℝ≥0∞ := fun k ↦ poissonBatchSum (0, 0) (markWeight β)
    (Function.update ω j (erasePoissonMark i.val (ω j)) k)
  change (∑' k, S k) + markWeight β ((ω j).2 i) = ∑' k, T k
  have hsingle : ∑' k : ℕ, (if k = j then markWeight β ((ω j).2 i) else 0) =
      markWeight β ((ω j).2 i) := tsum_ite_eq _ _
  rw [← hsingle, ← ENNReal.tsum_add]
  apply tsum_congr
  intro k
  by_cases hk : k = j
  · subst k
    simpa [S, T] using hbatch (ω j) i
  · simp [S, T, hk]

/-- The integrated occupation of two independent endpoint laws. -/
noncomputable def occupationMassBetween (β d : ℝ) (μ ν : Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ∫⁻ p : ℝ × ℝ, ENNReal.ofReal
    (edgeOccupation (Real.exp (-β * x)) p.1 p.2) ∂(μ.prod ν) ∂intensity d

theorem occupationMassBetween_swap (β d : ℝ) (μ ν : Measure ℝ)
    [SFinite μ] [SFinite ν] :
    occupationMassBetween β d μ ν = occupationMassBetween β d ν μ := by
  unfold occupationMassBetween
  apply lintegral_congr
  intro x
  rw [← Measure.prod_swap, lintegral_map (by unfold edgeOccupation; fun_prop) measurable_swap]
  apply lintegral_congr
  intro p
  exact congrArg ENNReal.ofReal (edgeOccupation_swap _ _ _)

/-- Endpoint exchange applied to the concrete marked batches. This is the
positive-fugacity mass identity for a pair of crossed scalar message laws. -/
theorem occupationMassBetween_eq_mean_vacancy_deficit {β d z : ℝ}
    (hd : 0 < d) (hz : 0 < z)
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x)
    (hfin : ∀ᵐ ω ∂pwitBatchLaw d μ, pwitWeightedSum β ω ≠ ∞)
    (hLaw : (pwitBatchLaw d μ).map (pwitCavityOutput β z) = ν) :
    occupationMassBetween β d μ ν = ∫⁻ x, ENNReal.ofReal (1 - z * x) ∂ν := by
  let P := pwitBatchLaw d μ
  let : IsProbabilityMeasure P := pwitBatchLaw_isProbabilityMeasure hd μ
  let Z := ENNReal.ofReal z
  let g : (ℝ × ℝ) × PWITConfiguration → ℝ≥0∞ := fun p ↦
    markWeight β p.1 / (Z + (pwitWeightedSum β p.2 + markWeight β p.1))
  have hg : Measurable g := by
    have hW : Measurable (markWeight β) := by unfold markWeight; fun_prop
    have hSW := (measurable_pwitWeightedSum β).comp
      (measurable_snd : Measurable (Prod.snd : (ℝ × ℝ) × PWITConfiguration → _))
    exact (hW.comp measurable_fst).div
      (measurable_const.add (hSW.add (hW.comp measurable_fst)))
  have hMecke := pwit_insertion hd μ g hg
  have hrestore (ω : PWITConfiguration) :
      (∑' j, poissonBatchDeletionSum (0, 0)
        (fun p ↦ g (p.1, Function.update ω j p.2)) (ω j)) =
      pwitWeightedSum β ω / (Z + pwitWeightedSum β ω) := by
    unfold pwitWeightedSum
    rw [div_eq_mul_inv, ← ENNReal.tsum_mul_right]
    apply tsum_congr
    intro j
    rw [poissonBatchDeletionSum_eq_sum, poissonBatchSum_eq_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    change markWeight β ((ω j).2 i) /
      (Z + (pwitWeightedSum β (Function.update ω j (erasePoissonMark i.val (ω j))) +
        markWeight β ((ω j).2 i))) = _
    rw [partition_remove_add, div_eq_mul_inv]
    rfl
  simp_rw [hrestore] at hMecke
  have hLeft :
      (∫⁻ ω, pwitWeightedSum β ω / (Z + pwitWeightedSum β ω) ∂P) =
        ∫⁻ x, ENNReal.ofReal (1 - z * x) ∂ν := by
    rw [← hLaw, lintegral_map (by fun_prop) (measurable_pwitCavityOutput _ _)]
    apply lintegral_congr_ae
    filter_upwards [hfin] with ω hf
    let S := (pwitWeightedSum β ω).toReal
    have hS : 0 ≤ S := ENNReal.toReal_nonneg
    have hsum : pwitWeightedSum β ω = ENNReal.ofReal S :=
      (ENNReal.ofReal_toReal hf).symm
    have hterm : (S / (z + S)) = 1 - z * (z + S)⁻¹ := by
      field_simp
      ring
    change pwitWeightedSum β ω / (ENNReal.ofReal z + pwitWeightedSum β ω) =
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
    have hP_meas : Measurable (pwitCavityOutput β z) := measurable_pwitCavityOutput _ _
    rw [← hLaw, lintegral_map (by unfold edgeOccupation; fun_prop) hP_meas]
    apply lintegral_congr_ae
    filter_upwards [hfin] with ω hf
    let W := Real.exp (-β * x) * h
    let S := (pwitWeightedSum β ω).toReal
    have hW : 0 ≤ W := mul_nonneg (Real.exp_nonneg _) hh
    have hS : 0 ≤ S := ENNReal.toReal_nonneg
    have hsum : pwitWeightedSum β ω = ENNReal.ofReal S :=
      (ENNReal.ofReal_toReal hf).symm
    change ENNReal.ofReal W / (ENNReal.ofReal z + (pwitWeightedSum β ω + ENNReal.ofReal W)) =
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
    _ = ∫⁻ ω, pwitWeightedSum β ω / (Z + pwitWeightedSum β ω) ∂P := hMecke.symm
    _ = _ := hLeft


/-- Bounded marks give the finite series required by endpoint exchange. -/
theorem pwit_weightedSum_ae_ne_top_of_bounded_marks {d β : ℝ}
    (hd : 0 < d) (hβ : 0 < β) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {M : ℝ} (hM : ∀ᵐ x ∂μ, x ≤ M) :
    ∀ᵐ ω ∂pwitBatchLaw d μ, pwitWeightedSum β ω ≠ ∞ := by
  have hI : (∫⁻ y, ENNReal.ofReal y ∂μ) < ∞ := by
    apply lt_of_le_of_lt (lintegral_mono_ae (hM.mono fun _ h ↦ ENNReal.ofReal_le_ofReal h))
    simp
  simpa only [pwitWeightedSum, ENNReal.ofReal_mul (Real.exp_nonneg _), lt_top_iff_ne_top, neg_mul]
    using pwit_exp_weighted_marks_ae_finite hd hβ μ hI

/-- Equal expected vacancy deficits identify two pointwise ordered bounded messages. -/
theorem ae_eq_of_ordered_of_equal_vacancy_deficit
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {z : ℝ} (hz : 0 < z) {L U : A → ℝ} (hL : Measurable L) (hU : Measurable U)
    (hb : ∀ᵐ x ∂P, 0 ≤ L x ∧ L x ≤ U x ∧ U x ≤ z⁻¹)
    (heq : (∫⁻ x, ENNReal.ofReal (1 - z * L x) ∂P) =
      ∫⁻ x, ENNReal.ofReal (1 - z * U x) ∂P) : L =ᵐ[P] U := by
  have heq := heq
  have hLI : Integrable L P := Integrable.of_mem_Icc 0 z⁻¹ hL.aemeasurable
    (hb.mono fun _ h ↦ ⟨h.1, h.2.1.trans h.2.2⟩)
  have hUI : Integrable U P := Integrable.of_mem_Icc 0 z⁻¹ hU.aemeasurable
    (hb.mono fun _ h ↦ ⟨h.1.trans h.2.1, h.2.2⟩)
  have hLG : Integrable (fun x ↦ 1 - z * L x) P :=
    (integrable_const 1).sub (hLI.const_mul z)
  have hUG : Integrable (fun x ↦ 1 - z * U x) P :=
    (integrable_const 1).sub (hUI.const_mul z)
  have hLG₀ : 0 ≤ᵐ[P] (fun x ↦ 1 - z * L x) := by
    filter_upwards [hb] with x h
    have hp := mul_le_mul_of_nonneg_left (h.2.1.trans h.2.2) hz.le
    rw [mul_inv_cancel₀ hz.ne'] at hp
    exact sub_nonneg.mpr hp
  have hUG₀ : 0 ≤ᵐ[P] (fun x ↦ 1 - z * U x) := by
    filter_upwards [hb] with x h
    have hp := mul_le_mul_of_nonneg_left h.2.2 hz.le
    rw [mul_inv_cancel₀ hz.ne'] at hp
    exact sub_nonneg.mpr hp
  rw [← ofReal_integral_eq_lintegral_ofReal hLG hLG₀,
    ← ofReal_integral_eq_lintegral_ofReal hUG hUG₀] at heq
  have hi := ENNReal.ofReal_eq_ofReal_iff
    (integral_nonneg_of_ae hLG₀) (integral_nonneg_of_ae hUG₀) |>.mp heq
  simp only [integral_sub (integrable_const 1) (hLI.const_mul z),
    integral_sub (integrable_const 1) (hUI.const_mul z), integral_const_mul] at hi
  apply (integral_eq_iff_of_ae_le hLI hUI (hb.mono fun _ h ↦ h.2.1)).mp
  apply mul_left_cancel₀ hz.ne'
  linarith

/-- Ordered crossed messages on the marked batch model agree almost surely.
The crossed recursions are hypotheses; the two expected occupation identities
are derived from the proved Poisson insertion formula. -/
theorem ae_eq_of_ordered_crossed_batch_recursions
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {d β z : ℝ} (hd : 0 < d) (hβ : 0 < β) (hz : 0 < z)
    {L U : A → ℝ} (hL : Measurable L) (hU : Measurable U)
    (hb : ∀ᵐ x ∂P, 0 ≤ L x ∧ L x ≤ U x ∧ U x ≤ z⁻¹)
    (hLower : (pwitBatchLaw d (P.map U)).map (pwitCavityOutput β z) = P.map L)
    (hUpper : (pwitBatchLaw d (P.map L)).map (pwitCavityOutput β z) = P.map U) :
    L =ᵐ[P] U := by
  let : IsProbabilityMeasure (P.map L) := Measure.isProbabilityMeasure_map hL.aemeasurable
  let : IsProbabilityMeasure (P.map U) := Measure.isProbabilityMeasure_map hU.aemeasurable
  have hL₀ : 0 ≤ᵐ[P.map L] (fun x : ℝ ↦ x) :=
    (ae_map_iff hL.aemeasurable measurableSet_Ici).mpr (hb.mono fun _ h ↦ h.1)
  have hU₀ : 0 ≤ᵐ[P.map U] (fun x : ℝ ↦ x) :=
    (ae_map_iff hU.aemeasurable measurableSet_Ici).mpr (hb.mono fun _ h ↦ h.1.trans h.2.1)
  have hLmax : ∀ᵐ x ∂P.map L, x ≤ z⁻¹ :=
    (ae_map_iff hL.aemeasurable measurableSet_Iic).mpr (hb.mono fun _ h ↦ h.2.1.trans h.2.2)
  have hUmax : ∀ᵐ x ∂P.map U, x ≤ z⁻¹ :=
    (ae_map_iff hU.aemeasurable measurableSet_Iic).mpr (hb.mono fun _ h ↦ h.2.2)
  have hLowerMass := occupationMassBetween_eq_mean_vacancy_deficit hd hz (P.map U) (P.map L) hU₀
    (pwit_weightedSum_ae_ne_top_of_bounded_marks hd hβ _ hUmax) hLower
  have hUpperMass := occupationMassBetween_eq_mean_vacancy_deficit hd hz (P.map L) (P.map U) hL₀
    (pwit_weightedSum_ae_ne_top_of_bounded_marks hd hβ _ hLmax) hUpper
  rw [occupationMassBetween_swap] at hLowerMass
  have heq := hLowerMass.symm.trans hUpperMass
  rw [lintegral_map (by fun_prop) hL, lintegral_map (by fun_prop) hU] at heq
  exact ae_eq_of_ordered_of_equal_vacancy_deficit P hz hL hU hb heq

end Certificate

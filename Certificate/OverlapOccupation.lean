import Certificate.ArrivalHardCoupling
import Certificate.HardLogUpperTail

/-! The insertion formula and strict bounds for the predicted overlap. -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

namespace Certificate

/-- Occupation of an outgoing edge in the marked cavity configuration. -/
noncomputable def rootOccupation (β d z : ℝ) (ω : ArrivalConfiguration) (i : ℕ) : ℝ :=
  cavityTerm β d ω i * arrivalSoftOutput β d z ω

/-- Squared probability that an edge inserted between two independent cavity
messages is occupied in both replicas. -/
noncomputable def overlapEdgeSquare (β x : ℝ) (p : ℝ × ℝ) : ℝ :=
  (edgeOccupation (Real.exp (-β * x)) p.1 p.2)^2

/-- The overlap predicted by the manuscript, for a given cavity message law. -/
noncomputable def cavityOverlap (β d : ℝ) (H : Measure ℝ) : ℝ :=
  ∫ x, (∫ p, overlapEdgeSquare β x p ∂H.prod H) ∂intensity d

theorem measurable_rootOccupation (β d z : ℝ) (i : ℕ) :
    Measurable (fun ω => rootOccupation β d z ω i) := by
  have hm : Measurable (fun ω => cavityTerm β d ω i) := by
    unfold cavityTerm arrivalLength
    fun_prop
  exact hm.mul (measurable_arrivalSoftOutput β d z)

theorem measurable_overlapEdgeSquare (β : ℝ) :
    Measurable (fun p : ℝ × (ℝ × ℝ) => overlapEdgeSquare β p.1 p.2) := by
  unfold overlapEdgeSquare edgeOccupation
  fun_prop

private theorem rootOccupation_eq_inserted {β d z : ℝ} (hz : 0 ≤ z)
    (ω : ArrivalConfiguration) (i : ℕ) (hfin : arrivalWeightedSum β d ω ≠ ∞)
    (hmarks : ∀ j, 0 < ω.2 j) :
    rootOccupation β d z ω i =
      edgeOccupation (Real.exp (-β * arrivalLength d ω.1 i)) (ω.2 i)
        (arrivalSoftOutput β d z (eraseArrivalGap i ω.1, eraseSequence i ω.2)) := by
  let erased : ArrivalConfiguration := (eraseArrivalGap i ω.1, eraseSequence i ω.2)
  let W := cavityTerm β d ω i
  have hW : 0 < W := mul_pos (Real.exp_pos _) (hmarks i)
  have hsum : arrivalWeightedSum β d erased + ENNReal.ofReal W = arrivalWeightedSum β d ω :=
    arrivalWeightedSum_erase_add β d ω i
  have hE : arrivalWeightedSum β d erased ≠ ∞ := ne_top_of_le_ne_top hfin
    ((le_self_add (b := ENNReal.ofReal W)).trans_eq hsum)
  have hmark0 : 0 < erased.2 0 := by
    change 0 < eraseSequence i ω.2 0
    by_cases hi : 0 < i
    · rw [eraseSequence_apply_of_lt ω.2 hi]
      exact hmarks 0
    · rw [eraseSequence_apply_of_ge ω.2 (le_of_not_gt hi)]
      exact hmarks 1
  have hpos : 0 < arrivalWeightedSum β d erased :=
    (ENNReal.ofReal_pos.mpr (mul_pos (Real.exp_pos _) hmark0)).trans_le
      (ENNReal.le_tsum (f := fun j => ENNReal.ofReal (cavityTerm β d erased j)) 0)
  have hS : 0 < z + (arrivalWeightedSum β d erased).toReal :=
    add_pos_of_nonneg_of_pos hz (ENNReal.toReal_pos hpos.ne' hE)
  have hfull := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_add hE ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hW.le] at hfull
  change W * (z + (arrivalWeightedSum β d ω).toReal)⁻¹ =
    W * (z + (arrivalWeightedSum β d erased).toReal)⁻¹ /
      (1 + W * (z + (arrivalWeightedSum β d erased).toReal)⁻¹)
  rw [← hfull, ← add_assoc]
  let S := z + (arrivalWeightedSum β d erased).toReal
  change W * (S + W)⁻¹ = W * S⁻¹ / (1 + W * S⁻¹)
  have hS' : 0 < S := hS
  have hB : 0 < S + W := add_pos hS' hW
  have hC : 0 < 1 + W * S⁻¹ := by positivity
  field_simp

set_option maxHeartbeats 1000000 in
/-- Mecke identifies the expected sum of squared root occupations with the
inserted-edge integral. The identity holds also at zero fugacity. -/
theorem lintegral_rootOccupation_sq {β d z : ℝ} (hd : 0 < d) (hz : 0 ≤ z)
    (H : Measure ℝ) [IsProbabilityMeasure H]
    (hH : ∀ᵐ x ∂H, 0 < x)
    (hfin : ∀ᵐ ω ∂markedSpacings H, arrivalWeightedSum β d ω ≠ ∞)
    (hLaw : (markedSpacings H).map (arrivalSoftOutput β d z) = H) :
    (∫⁻ ω, ∑' i, ENNReal.ofReal ((rootOccupation β d z ω i)^2) ∂markedSpacings H) =
      ∫⁻ x, ∫⁻ p, ENNReal.ofReal (overlapEdgeSquare β x p) ∂H.prod H ∂intensity d := by
  let P := markedSpacings H
  let : IsProbabilityMeasure P := isProbabilityMeasure_markedArrivalSequenceLaw H
  let g (p : (ℝ × ℝ) × ArrivalConfiguration) : ℝ≥0∞ :=
    ENNReal.ofReal (overlapEdgeSquare β p.1.1 (p.1.2, arrivalSoftOutput β d z p.2))
  have hg : Measurable g := by
    apply ENNReal.measurable_ofReal.comp
    exact (measurable_overlapEdgeSquare β).comp
      (measurable_fst.fst.prodMk
        (measurable_fst.snd.prodMk ((measurable_arrivalSoftOutput β d z).comp measurable_snd)))
  have hp : ∀ᵐ ω ∂P, ∀ i, 0 < ω.2 i :=
    ae_all_iff.mpr fun i =>
      (markedArrival_eval_preserving H i).quasiMeasurePreserving.tendsto_ae.eventually hH
  have hLeft : (∫⁻ ω, ∑' i, ENNReal.ofReal ((rootOccupation β d z ω i)^2) ∂P) =
      ∫⁻ ω, ∑' i, g ((arrivalLength d ω.1 i, ω.2 i),
        (eraseArrivalGap i ω.1, eraseSequence i ω.2)) ∂P := by
    apply lintegral_congr_ae
    filter_upwards [hp, hfin] with ω hω hωfin
    apply tsum_congr
    intro i
    rw [rootOccupation_eq_inserted hz ω i hωfin hω]
    rfl
  rw [hLeft, canonical_marked_arrival_insertion hd H g hg,
    lintegral_prod _ hg.aemeasurable, lintegral_prod _ hg.lintegral_prod_right'.aemeasurable]
  apply lintegral_congr
  intro x
  have hx : Measurable (fun p => ENNReal.ofReal (overlapEdgeSquare β x p)) :=
    ENNReal.measurable_ofReal.comp ((measurable_overlapEdgeSquare β).comp
      (measurable_const.prodMk measurable_id))
  rw [lintegral_prod _ hx.aemeasurable]
  apply lintegral_congr
  intro y
  have hxy : Measurable (fun s => ENNReal.ofReal (overlapEdgeSquare β x (y,s))) :=
    hx.comp (measurable_const.prodMk measurable_id)
  calc
    _ = ∫⁻ s, ENNReal.ofReal (overlapEdgeSquare β x (y,s))
        ∂P.map (arrivalSoftOutput β d z) :=
      (lintegral_map hxy (measurable_arrivalSoftOutput β d z)).symm
    _ = _ := by rw [hLaw]

private theorem ae_positive_cavity_marks {β d : ℝ} {H : Measure ℝ} (hH : IsCavityLaw β d H) :
    ∀ᵐ x ∂H, 0 < x := by
  let : IsProbabilityMeasure H := hH.1
  exact (mem_ae_iff_prob_eq_one (measurableSet_Ioi (a := (0:ℝ)))).mpr hH.2.1

/-- At zero fugacity the root occupations form a strictly positive
probability vector. -/
theorem ae_hard_rootOccupation_probability {β d : ℝ} {H : Measure ℝ} (hH : IsCavityLaw β d H) :
    ∀ᵐ ω ∂markedSpacings H,
      (∀ i, 0 < rootOccupation β d 0 ω i) ∧
      Summable (rootOccupation β d 0 ω) ∧ ∑' i, rootOccupation β d 0 ω i = 1 := by
  let : IsProbabilityMeasure H := hH.1
  have hp : ∀ᵐ ω ∂markedSpacings H, ∀ i, 0 < ω.2 i :=
    ae_all_iff.mpr fun i =>
      (markedArrival_eval_preserving H i).quasiMeasurePreserving.tendsto_ae.eventually
        (ae_positive_cavity_marks hH)
  filter_upwards [hp, hH.2.2.1, ae_cavityMap_eq_arrivalSoftOutput_zero hH] with ω hω hs heq
  have h : arrivalSoftOutput β d 0 ω = (∑' i, cavityTerm β d ω i)⁻¹ := heq.symm
  simp only [rootOccupation, h]
  refine ⟨fun i => mul_pos (mul_pos (Real.exp_pos _) (hω i)) (inv_pos.mpr hs.2),
    hs.1.mul_right _, ?_⟩
  rw [tsum_mul_right, mul_inv_cancel₀ hs.2.ne']

private theorem strict_square_sum {a : ℕ → ℝ} (ha : ∀ i, 0 < a i) (hs : Summable a)
    (ht : ∑' i, a i = 1) :
    Summable (fun i => (a i)^2) ∧ 0 < ∑' i, (a i)^2 ∧ ∑' i, (a i)^2 < 1 := by
  have hb (i : ℕ) : a i < 1 := by
    let j := i+1
    have hsum := hs.sum_le_tsum (s := {i,j}) (fun k _ => (ha k).le)
    rw [Finset.sum_pair (show i ≠ j by simp [j]), ht] at hsum
    linarith [ha j]
  have hsq (i : ℕ) : (a i)^2 < a i := by nlinarith [mul_pos (ha i) (sub_pos.mpr (hb i))]
  have hsub := hs.of_nonneg_of_le (fun i => sq_nonneg (a i)) (fun i => (hsq i).le)
  refine ⟨hsub, ?_, ?_⟩
  · exact (sq_pos_of_pos (ha 0)).trans_le (hsub.le_tsum 0 (fun i _ => sq_nonneg (a i)))
  · rw [← ht]
    exact hs.tsum_lt_tsum_of_nonneg (fun i => sq_nonneg (a i))
      (fun i => (hsq i).le) (hsq 0)

/-- The squared occupation sum has a strictly positive expectation below one. -/
theorem integral_rootOccupation_sq_mem_Ioo {β d : ℝ} {H : Measure ℝ}
    (hH : IsCavityLaw β d H) :
    (∫ ω, ∑' i, (rootOccupation β d 0 ω i)^2 ∂markedSpacings H) ∈ Ioo (0:ℝ) 1 := by
  let : IsProbabilityMeasure H := hH.1
  let : IsProbabilityMeasure (markedSpacings H) := isProbabilityMeasure_markedArrivalSequenceLaw H
  let f (ω : ArrivalConfiguration) := ∑' i, (rootOccupation β d 0 ω i)^2
  have hM : Measurable f := Measurable.tsum fun i => (measurable_rootOccupation β d 0 i).pow_const 2
  have hb : ∀ᵐ ω ∂markedSpacings H, 0 < f ω ∧ f ω < 1 :=
    (ae_hard_rootOccupation_probability hH).mono fun _ h =>
      (strict_square_sum h.1 h.2.1 h.2.2).2
  have hfi : Integrable f (markedSpacings H) :=
    Integrable.of_bound hM.aestronglyMeasurable 1
      (hb.mono fun x h => by simpa only [Real.norm_eq_abs, abs_of_pos h.1] using h.2.le)
  have hpos {g : ArrivalConfiguration → ℝ} (hg : Integrable g (markedSpacings H))
      (hgp : ∀ᵐ ω ∂markedSpacings H, 0 < g ω) : 0 < ∫ ω, g ω ∂markedSpacings H := by
    refine lt_of_le_of_ne' (integral_nonneg_of_ae (hgp.mono fun _ h => h.le)) ?_
    intro hzero
    have he := (integral_eq_zero_iff_of_nonneg_ae (hgp.mono fun _ h => h.le) hg).mp hzero
    have hc : ∀ᵐ _ ∂markedSpacings H, False :=
      (hgp.and he).mono fun ω ⟨hp, he⟩ => (ne_of_gt hp) (show g ω = 0 from he)
    obtain ⟨_, hfalse⟩ := hc.exists
    exact hfalse
  have ha := hpos hfi (hb.mono fun _ h => h.1)
  have hc := hpos ((integrable_const (1:ℝ)).sub hfi) (hb.mono fun _ h => sub_pos.mpr h.2)
  change 0 < ∫ ω, (1 : ℝ) - f ω ∂markedSpacings H at hc
  rw [integral_sub (integrable_const _) hfi, integral_const, probReal_univ, one_smul] at hc
  exact ⟨ha, sub_pos.mp hc⟩

/-- The inserted-edge integral is the mean squared occupation sum for a fixed-point law. -/
theorem cavityOverlap_eq_integral_rootOccupation_sq_of_fixedPoint {β d z : ℝ}
    (hd : 0 < d) (hz : 0 ≤ z) {H : Measure ℝ} [IsProbabilityMeasure H]
    (hp : ∀ᵐ x ∂H, 0 < x)
    (hfin : ∀ᵐ ω ∂markedSpacings H, arrivalWeightedSum β d ω ≠ ∞)
    (hLaw : (markedSpacings H).map (arrivalSoftOutput β d z) = H)
    (hsq : ∀ᵐ ω ∂markedSpacings H, Summable (fun i => (rootOccupation β d z ω i)^2)) :
    cavityOverlap β d H = ∫ ω, ∑' i, (rootOccupation β d z ω i)^2 ∂markedSpacings H := by
  have hp' : ∀ᵐ p ∂H.prod H, 0 < p.1 ∧ 0 < p.2 :=
    ((measurePreserving_fst (μ := H) (ν := H)).quasiMeasurePreserving.tendsto_ae.eventually hp).and
      ((measurePreserving_snd (μ := H) (ν := H)).quasiMeasurePreserving.tendsto_ae.eventually hp)
  have hm (x : ℝ) : Measurable (overlapEdgeSquare β x) :=
    (measurable_overlapEdgeSquare β).comp (measurable_const.prodMk measurable_id)
  have hi (x : ℝ) : Integrable (overlapEdgeSquare β x) (H.prod H) :=
    Integrable.of_bound (hm x).aestronglyMeasurable 1 (hp'.mono fun p h => by
      have h₀ := edgeOccupation_pos (Real.exp_pos (-β * x)) h.1 h.2
      have h₁ := edgeOccupation_lt_one (Real.exp_pos (-β * x)) h.1 h.2
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_one₀ h₀.le h₁.le)
  have hinner (x : ℝ) :
      ENNReal.ofReal (∫ p, overlapEdgeSquare β x p ∂H.prod H) =
        ∫⁻ p, ENNReal.ofReal (overlapEdgeSquare β x p) ∂H.prod H :=
    ofReal_integral_eq_lintegral_ofReal (hi x) (Eventually.of_forall fun _ => sq_nonneg _)
  have hM : Measurable (fun x => ∫ p, overlapEdgeSquare β x p ∂H.prod H) :=
    (measurable_overlapEdgeSquare β).stronglyMeasurable.integral_prod_right'.measurable
  have hsM : Measurable (fun ω : ArrivalConfiguration => ∑' i, (rootOccupation β d z ω i)^2) :=
    Measurable.tsum fun i => (measurable_rootOccupation β d z i).pow_const 2
  have hMecke := lintegral_rootOccupation_sq hd hz H hp hfin hLaw
  have hn : 0 ≤ᵐ[intensity d] (fun x => ∫ p, overlapEdgeSquare β x p ∂H.prod H) :=
    Eventually.of_forall fun _ => integral_nonneg fun _ => sq_nonneg _
  unfold cavityOverlap
  rw [integral_eq_lintegral_of_nonneg_ae hn hM.aestronglyMeasurable]
  simp_rw [hinner]
  rw [← hMecke, integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun _ => tsum_nonneg fun _ => sq_nonneg _) hsM.aestronglyMeasurable]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [hsq] with ω ho
  exact (ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) ho).symm

/-- At zero fugacity, the overlap is the mean of the hard root
occupation square sum. -/
theorem cavityOverlap_eq_integral_rootOccupation_sq {β d : ℝ} (hd : 0 < d) {H : Measure ℝ}
    (hH : IsCavityLaw β d H) :
    cavityOverlap β d H = ∫ ω, ∑' i, (rootOccupation β d 0 ω i)^2 ∂markedSpacings H := by
  let : IsProbabilityMeasure H := hH.1
  exact cavityOverlap_eq_integral_rootOccupation_sq_of_fixedPoint hd le_rfl
    (ae_positive_cavity_marks hH) ((ae_hard_arrivalWeightedSum_spec hH).mono fun _ h => h.1)
    (map_arrivalSoftOutput_zero_of_IsCavityLaw hH)
    ((ae_hard_rootOccupation_probability hH).mono fun _ h => (strict_square_sum h.1 h.2.1 h.2.2).1)

/-- The predicted overlap is strictly between zero and one. -/
theorem cavityOverlap_mem_Ioo {β d : ℝ} (hd : 0 < d) {H : Measure ℝ}
    (hH : IsCavityLaw β d H) : cavityOverlap β d H ∈ Ioo (0 : ℝ) 1 := by
  rw [cavityOverlap_eq_integral_rootOccupation_sq hd hH]
  exact integral_rootOccupation_sq_mem_Ioo hH

end Certificate

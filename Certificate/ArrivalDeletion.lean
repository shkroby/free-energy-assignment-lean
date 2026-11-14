import Certificate.Arrivals
import Certificate.PoissonIndexedGap

/-! Removing one marked arrival subtracts exactly its term from the weighted sum. -/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Certificate

abbrev ArrivalConfiguration := (ℕ → ℝ) × (ℕ → ℝ)

private theorem eraseArrivalGap_apply_before (E : ℕ → ℝ) {i j : ℕ} (h : j < i) :
    eraseArrivalGap i E j = E j := by
  rw [eraseArrivalGap, Function.update_of_ne h.ne, eraseSequence_apply_of_lt E (by omega)]

private theorem eraseArrivalGap_apply_after (E : ℕ → ℝ) {i j : ℕ} (h : i < j) :
    eraseArrivalGap i E j = E (j + 1) := by
  rw [eraseArrivalGap, Function.update_of_ne h.ne', eraseSequence_apply_of_ge E (by omega)]

/-- Before the deleted point the lengths are unchanged; from its index on,
the new length is the old length at the next index. -/
theorem arrivalLength_eraseGap (d : ℝ) (E : ℕ → ℝ) (i j : ℕ) :
    arrivalLength d (eraseArrivalGap i E) j =
      if j < i then arrivalLength d E j else arrivalLength d E (j + 1) := by
  by_cases h : j < i
  · simp only [if_pos h, arrivalLength]
    congr 1
    exact Finset.sum_congr rfl fun k hk ↦
      eraseArrivalGap_apply_before E (by have := Finset.mem_range.mp hk; omega)
  · simp only [if_neg h, arrivalLength]
    congr 1
    obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le (le_of_not_gt h)
    induction l with
    | zero =>
      simp only [Nat.add_zero]
      rw [Finset.sum_range_succ, Finset.sum_range_succ (f := E) (n := i+1),
        Finset.sum_range_succ (f := E) (n := i)]
      have hb : (∑ k ∈ Finset.range i, eraseArrivalGap i E k) =
          ∑ k ∈ Finset.range i, E k :=
        Finset.sum_congr rfl (fun k hk ↦ eraseArrivalGap_apply_before E (Finset.mem_range.mp hk))
      rw [hb, eraseArrivalGap, Function.update_self]
      ring
    | succ l ih =>
      change (∑ k ∈ Finset.range ((i + l + 1) + 1), eraseArrivalGap i E k) =
        ∑ k ∈ Finset.range (((i + l + 1) + 1) + 1), E k
      have hi : i < i + l + 1 := by omega
      rw [Finset.sum_range_succ, Finset.sum_range_succ (f := E), eraseArrivalGap_apply_after E hi]
      rw [ih (by omega)]

/-- The weighted arrival sum, with nonnegative terms in extended reals. -/
noncomputable def arrivalWeightedSum (β d : ℝ) (ω : ArrivalConfiguration) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (cavityTerm β d ω i)

theorem measurable_arrivalWeightedSum (β d : ℝ) : Measurable (arrivalWeightedSum β d) := by
  unfold arrivalWeightedSum
  apply Measurable.tsum
  intro i
  unfold cavityTerm arrivalLength
  fun_prop

/-- The retained configuration's total plus the selected term is precisely the
original total, including at infinite total mass. -/
theorem arrivalWeightedSum_erase_add (β d : ℝ) (ω : ArrivalConfiguration) (i : ℕ) :
    arrivalWeightedSum β d (eraseArrivalGap i ω.1, eraseSequence i ω.2) +
      ENNReal.ofReal (cavityTerm β d ω i) = arrivalWeightedSum β d ω := by
  let f : ℕ → ℝ≥0∞ := fun j ↦ ENNReal.ofReal (cavityTerm β d ω j)
  let g : ℕ → ℝ≥0∞ := fun j ↦
    ENNReal.ofReal (cavityTerm β d (eraseArrivalGap i ω.1, eraseSequence i ω.2) j)
  have hg (j : ℕ) : g j = if j < i then f j else f (j + 1) := by
    unfold g f cavityTerm
    dsimp
    rw [arrivalLength_eraseGap]
    by_cases hj : j < i
    · rw [if_pos hj, if_pos hj, eraseSequence_apply_of_lt ω.2 hj]
    · rw [if_neg hj, if_neg hj, eraseSequence_apply_of_ge ω.2 (le_of_not_gt hj)]
  change (∑' j, g j) + f i = ∑' j, f j
  exact tsum_nat_skip_add i hg

/-- Real reciprocal with positive fugacity on the canonical arrival model. -/
noncomputable def arrivalSoftOutput (β d z : ℝ) (ω : ArrivalConfiguration) : ℝ :=
  (z + (arrivalWeightedSum β d ω).toReal)⁻¹

theorem measurable_arrivalSoftOutput (β d z : ℝ) :
    Measurable (arrivalSoftOutput β d z) :=
  (measurable_const.add (measurable_arrivalWeightedSum β d).ennreal_toReal).inv

/-- For bounded nonnegative marks the embedded real series and the extended
arrival sum agree almost surely. -/
theorem ae_arrivalWeightedSum_eq_ofReal_tsum {d β M : ℝ}
    (hd : 0 < d) (hβ : 0 < β) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hM : ∀ᵐ x ∂μ, x ∈ Icc 0 M) :
    ∀ᵐ ω ∂markedSpacings μ, arrivalWeightedSum β d ω =
      ENNReal.ofReal (∑' i, cavityTerm β d ω i) := by
  let : IsProbabilityMeasure exponentialSpacings := isProbabilityMeasure_exponentialSpacings
  let P := Measure.infinitePi (fun _ : ℕ ↦ μ)
  have hmarks : ∀ᵐ Y ∂P, ∀ i, 0 ≤ Y i := by
    refine ae_all_iff.2 fun i ↦ ?_
    have hm : P.map (fun Y : ℕ → ℝ ↦ Y i) = μ :=
      Measure.infinitePi_map_eval (fun _ : ℕ ↦ μ) i
    have hv : AEMeasurable (fun Y : ℕ → ℝ ↦ Y i) P := (measurable_pi_apply i).aemeasurable
    have hp : ∀ᵐ x ∂P.map (fun Y : ℕ → ℝ ↦ Y i), 0 ≤ x := by
      rw [hm]
      exact hM.mono fun _ h ↦ h.1
    exact (ae_map_iff hv (measurableSet_le (f := fun _ : ℝ ↦ (0 : ℝ)) (g := id)
      measurable_const measurable_id)).mp hp
  have hmarks' : ∀ᵐ ω ∂markedSpacings μ, ∀ i, 0 ≤ ω.2 i :=
    (Measure.quasiMeasurePreserving_snd (μ := exponentialSpacings) (ν := P)).tendsto_ae.eventually hmarks
  filter_upwards [hmarks', ae_summable_cavityTerm_of_bounded_marks hd hβ μ hM] with ω hw hs
  exact (ENNReal.ofReal_tsum_of_nonneg (fun i ↦ mul_nonneg (Real.exp_nonneg _) (hw i)) hs).symm

end Certificate

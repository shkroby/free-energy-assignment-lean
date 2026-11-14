import Certificate.ArrivalDeletion
import Certificate.PoissonArrivalMecke
import Certificate.PoissonLaw
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Poisson counts on the canonical exponential arrival law

The marked insertion formula yields the size-bias recurrence for the number
of points in any measurable set of finite intensity. Its normalized solution
is the Poisson law.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace Certificate

variable {Y : Type*} [MeasurableSpace Y]

/-- The length and mark of arrival `i`. -/
noncomputable def markedArrivalPoint (d : ℝ) (i : ℕ)
    (ω : (ℕ → ℝ) × (ℕ → Y)) : ℝ × Y :=
  (arrivalLength d ω.1 i, ω.2 i)

private theorem measurable_markedArrivalPoint (d : ℝ) (i : ℕ) :
    Measurable (markedArrivalPoint (Y := Y) d i) := by
  unfold markedArrivalPoint arrivalLength
  fun_prop

private noncomputable def pointHit (A : Set (ℝ × Y)) : ℝ × Y → ℝ≥0∞ :=
  A.indicator (fun _ => 1)

private theorem measurable_pointHit {A : Set (ℝ × Y)} (hA : MeasurableSet A) :
    Measurable (pointHit A) := measurable_const.indicator hA

/-- The count of points in the specified set, including infinite counts. -/
noncomputable def markedArrivalCount (d : ℝ) (A : Set (ℝ × Y))
    (ω : (ℕ → ℝ) × (ℕ → Y)) : ℝ≥0∞ :=
  ∑' i, pointHit A (markedArrivalPoint d i ω)

theorem measurable_markedArrivalCount (d : ℝ) {A : Set (ℝ × Y)} (hA : MeasurableSet A) :
    Measurable (markedArrivalCount d A) :=
  Measurable.tsum fun i => (measurable_pointHit hA).comp (measurable_markedArrivalPoint d i)

omit [MeasurableSpace Y] in
private theorem markedArrivalPoint_erase (d : ℝ) (ω : (ℕ → ℝ) × (ℕ → Y)) (i j : ℕ) :
    markedArrivalPoint d j (eraseArrivalGap i ω.1, eraseSequence i ω.2) =
      if j < i then markedArrivalPoint d j ω else markedArrivalPoint d (j+1) ω := by
  unfold markedArrivalPoint
  dsimp
  rw [arrivalLength_eraseGap]
  by_cases h : j < i
  · rw [if_pos h, if_pos h, eraseSequence_apply_of_lt ω.2 h]
  · rw [if_neg h, if_neg h, eraseSequence_apply_of_ge ω.2 (le_of_not_gt h)]

omit [MeasurableSpace Y] in
private theorem markedArrivalCount_erase_add (d : ℝ) (A : Set (ℝ × Y))
    (ω : (ℕ → ℝ) × (ℕ → Y)) (i : ℕ) :
    markedArrivalCount d A (eraseArrivalGap i ω.1, eraseSequence i ω.2) +
      pointHit A (markedArrivalPoint d i ω) = markedArrivalCount d A ω := by
  let f : ℕ → ℝ≥0∞ := fun j => pointHit A (markedArrivalPoint d j ω)
  let g : ℕ → ℝ≥0∞ := fun j => pointHit A
    (markedArrivalPoint d j (eraseArrivalGap i ω.1, eraseSequence i ω.2))
  have h (j : ℕ) : g j = if j < i then f j else f (j + 1) := by
    unfold g f
    rw [markedArrivalPoint_erase]
    split_ifs <;> rfl
  exact tsum_nat_skip_add i h

omit [MeasurableSpace Y] in
private theorem markedArrivalCount_nat {d : ℝ} {A : Set (ℝ × Y)}
    {ω : (ℕ → ℝ) × (ℕ → Y)} (h : markedArrivalCount d A ω ≠ ∞) :
    ∃ n : ℕ, markedArrivalCount d A ω = n := by
  let s : Set ℕ := {i | markedArrivalPoint d i ω ∈ A}
  have heq : markedArrivalCount d A ω = s.encard := by
    rw [← ENNReal.tsum_set_one, tsum_subtype s (fun _ : ℕ => (1 : ℝ≥0∞))]
    unfold markedArrivalCount pointHit
    apply tsum_congr
    intro i
    by_cases hi : markedArrivalPoint d i ω ∈ A
    · simp [s, hi]
    · simp [s, hi]
  have hfin : s.Finite := by
    by_contra hin
    apply h
    rw [heq, encard_eq_top hin, ENat.toENNReal_top]
  obtain ⟨n, hn⟩ := hfin.exists_encard_eq_coe
  exact ⟨n, by rw [heq, hn, ENat.toENNReal_coe]⟩

/-- Campbell's formula on the canonical arrival law. -/
theorem canonical_iid_marked_campbell {d : ℝ} (hd : 0 < d)
    (μ : Measure Y) [IsProbabilityMeasure μ] (f : ℝ × Y → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, ∑' i, f (markedArrivalPoint d i ω) ∂markedArrivalSequenceLaw μ) =
      ∫⁻ z, f z ∂(intensity d).prod μ := by
  let P := markedArrivalSequenceLaw μ
  let : IsProbabilityMeasure P := isProbabilityMeasure_markedArrivalSequenceLaw μ
  have h := canonical_iid_marked_arrival_insertion hd μ (fun z => f z.1) (hf.comp measurable_fst)
  change (∫⁻ ω, ∑' i, f (markedArrivalPoint d i ω) ∂P) =
    ∫⁻ z, f z ∂(intensity d).prod μ
  refine h.trans ?_
  rw [lintegral_prod (fun z : (ℝ × Y) × ((ℕ → ℝ) × (ℕ → Y)) => f z.1)
    (hf.comp measurable_fst).aemeasurable]
  simp [lintegral_const, show markedArrivalSequenceLaw μ univ = 1 from measure_univ]

/-- Counts of measurable finite-intensity sets have the stated Poisson law. -/
theorem canonical_iid_marked_count_probability {d : ℝ} (hd : 0 < d)
    (μ : Measure Y) [IsProbabilityMeasure μ] {A : Set (ℝ × Y)}
    (hA : MeasurableSet A) (hfin : ((intensity d).prod μ) A ≠ ∞) (n : ℕ) :
    markedArrivalSequenceLaw μ {ω | markedArrivalCount d A ω = (n : ℝ≥0∞)} =
      poissonMeasure (((intensity d).prod μ) A).toNNReal {n} := by
  let N := markedArrivalCount d A
  let P := markedArrivalSequenceLaw μ
  let T := (intensity d).prod μ
  let r := (T A).toNNReal
  let e (k : ℕ) : Set ((ℕ → ℝ) × (ℕ → Y)) := {ω | N ω = (k : ℝ≥0∞)}
  let p (k : ℕ) : ℝ≥0∞ := P (e k)
  let : IsProbabilityMeasure P := isProbabilityMeasure_markedArrivalSequenceLaw μ
  have hr : (r : ℝ≥0∞) = T A := ENNReal.coe_toNNReal hfin
  have hN : Measurable N := measurable_markedArrivalCount d hA
  have he (k : ℕ) : MeasurableSet (e k) := hN (measurableSet_singleton _)
  have hC : (∫⁻ ω, N ω ∂P) = T A :=
    (canonical_iid_marked_campbell hd μ _ (measurable_pointHit hA)).trans
      (lintegral_indicator_one hA)
  have hfinite : ∀ᵐ ω ∂P, N ω ≠ ∞ :=
    (ae_lt_top' hN.aemeasurable (hC.trans_ne hfin)).mono (fun _ h => h.ne)
  have hp : (∑' k, p k) = 1 := by
    have hdisj : Pairwise (fun i j : ℕ => Disjoint (e i) (e j)) := by
      intro i j hij
      apply Set.disjoint_left.mpr
      intro ω hi hj
      have h := congrArg ENNReal.toReal (hi.symm.trans hj)
      simp only [ENNReal.toReal_natCast] at h
      exact hij (by exact_mod_cast h)
    have hu : (⋃ k, e k) =ᵐ[P] univ := by
      filter_upwards [hfinite] with ω hω
      change (ω ∈ ⋃ k, e k) = (ω ∈ univ)
      simp only [mem_univ, eq_true, mem_iUnion]
      exact eq_true_intro (markedArrivalCount_nat hω)
    rw [← measure_iUnion hdisj he, measure_congr hu, measure_univ]
  have hrec (k : ℕ) :
      (↑(k+1 : ℕ) : ℝ≥0∞) * p (k+1) = (r : ℝ≥0∞) * p k := by
    let f (z : (ℝ × Y) × ((ℕ → ℝ) × (ℕ → Y))) :=
      pointHit A z.1 * (e k).indicator (fun _ => 1) z.2
    have hf : Measurable f :=
      ((measurable_pointHit hA).comp measurable_fst).mul
        ((measurable_const.indicator (he k)).comp measurable_snd)
    have H := canonical_iid_marked_arrival_insertion hd μ f hf
    have hpoint (ω : (ℕ → ℝ) × (ℕ → Y)) (i : ℕ) :
        f (markedArrivalPoint d i ω, (eraseArrivalGap i ω.1, eraseSequence i ω.2)) =
          pointHit A (markedArrivalPoint d i ω) *
            (e (k+1)).indicator (fun _ => 1) ω := by
      by_cases hAω : markedArrivalPoint d i ω ∈ A
      · have ha : pointHit A (markedArrivalPoint d i ω) = 1 := indicator_of_mem hAω _
        have H := markedArrivalCount_erase_add d A ω i
        rw [ha] at H
        have hm : (eraseArrivalGap i ω.1, eraseSequence i ω.2) ∈ e k ↔ ω ∈ e (k+1) := by
          change markedArrivalCount d A (eraseArrivalGap i ω.1, eraseSequence i ω.2) =
            (k : ℝ≥0∞) ↔ markedArrivalCount d A ω = ↑(k+1 : ℕ)
          rw [← H, Nat.cast_add, Nat.cast_one, ENNReal.add_left_inj ENNReal.one_ne_top]
        by_cases heω : ω ∈ e (k+1)
        · simp only [f, ha, one_mul, indicator_of_mem heω, indicator_of_mem (hm.mpr heω)]
        · simp only [f, ha, one_mul, indicator_of_notMem heω, indicator_of_notMem (mt hm.mp heω)]
      · simp only [f, pointHit, indicator_of_notMem hAω, zero_mul]
    have hL : (∫⁻ ω, ∑' i, f (markedArrivalPoint d i ω,
        (eraseArrivalGap i ω.1, eraseSequence i ω.2)) ∂P) =
          (↑(k+1 : ℕ) : ℝ≥0∞) * p (k+1) := by
      calc
        _ = ∫⁻ ω, (e (k+1)).indicator (fun _ => (↑(k+1 : ℕ) : ℝ≥0∞)) ω ∂P := by
          apply lintegral_congr
          intro ω
          simp_rw [hpoint, ENNReal.tsum_mul_right]
          by_cases hi : ω ∈ e (k+1)
          · have hc : markedArrivalCount d A ω = (↑(k+1 : ℕ) : ℝ≥0∞) := hi
            simp only [indicator_of_mem hi, mul_one]
            exact hc
          · simp only [indicator_of_notMem hi, mul_zero]
        _ = _ := lintegral_indicator_const (he (k+1)) _
    have hR : (∫⁻ z, f z ∂T.prod P) = (r : ℝ≥0∞) * p k := by
      change (∫⁻ z, pointHit A z.1 * (e k).indicator (fun _ => 1) z.2 ∂T.prod P) = _
      have hA' : (∫⁻ z, pointHit A z ∂T) = T A := lintegral_indicator_one hA
      have he' : (∫⁻ ω, (e k).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂P) = p k :=
        lintegral_indicator_one (he k)
      rw [lintegral_prod_mul (measurable_pointHit hA).aemeasurable
        (measurable_const.indicator (he k)).aemeasurable, hA', he', hr]
    exact hL.symm.trans (H.trans hR)
  exact poisson_eq_of_count_recurrence r p hp hrec n

/-- The void event on the canonical arrival space has the Poisson probability. -/
theorem canonical_iid_marked_void {d : ℝ} (hd : 0 < d)
    (μ : Measure Y) [IsProbabilityMeasure μ] {A : Set (ℝ × Y)}
    (hA : MeasurableSet A) (hfin : ((intensity d).prod μ) A ≠ ∞) :
    markedArrivalSequenceLaw μ {ω | ∀ i, markedArrivalPoint d i ω ∉ A} =
      ENNReal.ofReal (Real.exp (-(((intensity d).prod μ) A).toReal)) := by
  have h := canonical_iid_marked_count_probability hd μ hA hfin 0
  rw [poissonMeasure_singleton] at h
  have heq : {ω | ∀ i, markedArrivalPoint d i ω ∉ A} =
      {ω | markedArrivalCount d A ω = (↑(0 : ℕ) : ℝ≥0∞)} := by
    ext ω
    simp [markedArrivalCount, ENNReal.tsum_eq_zero, pointHit, indicator_apply_eq_zero]
  rw [heq]
  simpa only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, div_one,
    ENNReal.coe_toNNReal_eq_toReal] using h

/-- Exact waiting probability for a qualifying mark before length `R` on the
manuscript's canonical exponential arrival law. -/
theorem canonical_marked_window_void {d R : ℝ} (hd : 0 < d) (hR : 0 ≤ R)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {A : Set ℝ} (hA : MeasurableSet A) :
    markedSpacings μ {ω | ∀ i, (arrivalLength d ω.1 i, ω.2 i) ∉ Ioc 0 R ×ˢ A} =
      ENNReal.ofReal (Real.exp (-(R ^ d * (μ A).toReal))) := by
  have hmass : ((intensity d).prod μ) (Ioc 0 R ×ˢ A) =
      ENNReal.ofReal (R ^ d) * μ A := by
    rw [Measure.prod_prod, intensity_Ioc_zero hd hR]
  have hf : ((intensity d).prod μ) (Ioc 0 R ×ˢ A) ≠ ∞ := by
    rw [hmass]
    exact (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ A)).ne
  have H := canonical_iid_marked_void hd μ (measurableSet_Ioc.prod hA) hf
  rw [hmass, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg hR d)] at H
  exact H

end Certificate

import Certificate.ArrivalDeletion
import Certificate.PoissonArrivalCount
import Certificate.PressureFormula

/-!
# Controlling unbounded marks on the canonical arrivals

The marked series can converge even when the positive marks have no finite
first moment. Campbell's identity bounds the number of exceptions, and the
remaining summands are dominated by the summable exponential edge weights.
-/

open MeasureTheory Filter Set
open scoped ENNReal

namespace Certificate

/-- Campbell's first-moment formula for the spacings and marks in `Model`. -/
theorem canonical_marked_campbell {d : ℝ} (hd : 0 < d)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f : ℝ × ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, ∑' i, f (arrivalLength d ω.1 i, ω.2 i) ∂markedSpacings μ) =
      ∫⁻ x, f x ∂(intensity d).prod μ := by
  exact canonical_iid_marked_campbell hd μ f hf

/-- A set of finite marked intensity contains only finitely many of the
canonical arrival indices almost surely. -/
theorem ae_finite_marked_indices {d : ℝ} (hd : 0 < d) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {s : Set (ℝ × ℝ)} (hs : MeasurableSet s)
    (hfinite : ((intensity d).prod μ) s ≠ ∞) :
    ∀ᵐ ω ∂markedSpacings μ, {i | (arrivalLength d ω.1 i, ω.2 i) ∈ s}.Finite := by
  let f : ℝ × ℝ → ℝ≥0∞ := s.indicator 1
  have hf : Measurable f := measurable_const.indicator hs
  have hI := canonical_marked_campbell hd μ f hf
  rw [show (∫⁻ x, f x ∂(intensity d).prod μ) =
    ((intensity d).prod μ) s from lintegral_indicator_one hs] at hI
  have hm_i (i : ℕ) : Measurable (fun ω : ArrivalConfiguration ↦
      f (arrivalLength d ω.1 i, ω.2 i)) := by
    apply hf.comp
    unfold arrivalLength
    fun_prop
  have hm : Measurable (fun ω : ArrivalConfiguration ↦ ∑' i, f (arrivalLength d ω.1 i, ω.2 i)) :=
    Measurable.tsum hm_i
  have hAlmost := ae_lt_top' hm.aemeasurable (hI ▸ hfinite)
  filter_upwards [hAlmost] with ω hω
  have hset : {i | (arrivalLength d ω.1 i, ω.2 i) ∈ s} =
      {i | 1 ≤ f (arrivalLength d ω.1 i, ω.2 i)} := by
    ext i
    by_cases h : (arrivalLength d ω.1 i, ω.2 i) ∈ s <;> simp [f, h]
  rw [hset]
  exact ENNReal.finite_const_le_of_tsum_ne_top hω.ne one_ne_zero

/-- The canonical marked series is summable under an upper bound on the
logarithmic tail, without a positive moment of the marks themselves. -/
theorem ae_summable_cavityTerm_of_stretched_log_tail {d β c K : ℝ}
    (hd : 0 < d) (hβ : 0 < β) (hc : 0 < c) (hK : 0 ≤ K)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : ∀ᵐ h ∂μ, 0 ≤ h)
    (ht : ∀ x > 0, μ (Ioi (Real.exp (β * x / 2))) ≤
      ENNReal.ofReal (K * Real.exp (-(c * x ^ d)))) :
    ∀ᵐ ω ∂markedSpacings μ, Summable (cavityTerm β d ω) := by
  let : IsProbabilityMeasure exponentialSpacings := isProbabilityMeasure_exponentialSpacings
  let P := Measure.infinitePi (fun _ : ℕ ↦ μ)
  let s : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ Real.exp (β * p.1 / 2) < p.2}
  have hs : MeasurableSet s :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt (by fun_prop) measurable_snd)
  have hsfin : ((intensity d).prod μ) s ≠ ∞ := by
    rw [Measure.prod_apply hs]
    have hI : Integrable (fun x : ℝ ↦ K * Real.exp (-(c * x ^ d))) (intensity d) :=
      by simpa only [neg_mul] using (integrable_intensity_exp_rpow hd hd hc).const_mul K
    have hlt : (∫⁻ x, ENNReal.ofReal (K * Real.exp (-(c * x ^ d))) ∂intensity d) < ∞ :=
      (hasFiniteIntegral_iff_ofReal
        (.of_forall fun _ ↦ mul_nonneg hK (Real.exp_nonneg _))).mp hI.2
    refine (lt_of_le_of_lt (lintegral_mono fun x ↦ ?_) hlt).ne
    by_cases hx : 0 < x
    · have H : Prod.mk x ⁻¹' s = Ioi (Real.exp (β * x / 2)) := by ext y; simp [s, hx]
      rw [H]
      exact ht x hx
    · have H : Prod.mk x ⁻¹' s = ∅ := by ext y; simp [s, hx]
      rw [H, measure_empty]
      exact zero_le
  have hfinite := ae_finite_marked_indices hd μ hs hsfin
  have hmark : ∀ᵐ Y ∂P, ∀ i, 0 ≤ Y i := by
    apply ae_all_iff.mpr
    intro i
    have hi : P.map (fun Y : ℕ → ℝ ↦ Y i) = μ :=
      Measure.infinitePi_map_eval (fun _ : ℕ ↦ μ) i
    have hA : MeasurableSet {y : ℝ | 0 ≤ y} :=
      measurableSet_le measurable_const measurable_id
    exact (ae_map_iff (measurable_pi_apply i).aemeasurable hA).mp (by rwa [hi])
  have hmark' : ∀ᵐ ω ∂markedSpacings μ, ∀ i, 0 ≤ ω.2 i :=
    (Measure.quasiMeasurePreserving_snd (μ := exponentialSpacings) (ν := P)).tendsto_ae.eventually hmark
  have hweights : ∀ᵐ ω ∂markedSpacings μ,
      Summable (fun i ↦ Real.exp (-(β / 2) * arrivalLength d ω.1 i)) :=
    (Measure.quasiMeasurePreserving_fst (μ := exponentialSpacings) (ν := P)).tendsto_ae.eventually
      (ae_summable_arrival_weights hd (by positivity : 0 < β / 2))
  have hlen' : ∀ᵐ E ∂exponentialSpacings, ∀ i : ℕ, 0 < arrivalLength d E i := by
    filter_upwards [ae_expSpacing_pos] with E hE
    intro i
    unfold arrivalLength
    exact Real.rpow_pos_of_pos (Finset.sum_pos (fun j _ ↦ hE j)
      ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ _)⟩) _
  have hlen : ∀ᵐ ω ∂markedSpacings μ, ∀ i, 0 < arrivalLength d ω.1 i :=
    (Measure.quasiMeasurePreserving_fst (μ := exponentialSpacings) (ν := P)).tendsto_ae.eventually hlen'
  filter_upwards [hfinite, hmark', hweights, hlen] with ω hf hm hw hξ
  apply hw.of_norm_bounded_eventually_nat
  have hevent : ∀ᶠ i : ℕ in atTop, i ∉ {i | (arrivalLength d ω.1 i, ω.2 i) ∈ s} :=
    by simpa only [← Nat.cofinite_eq_atTop, eventually_cofinite, mem_ofPred_eq, not_not] using hf
  filter_upwards [hevent] with i hi
  have hle : ω.2 i ≤ Real.exp (β * arrivalLength d ω.1 i / 2) := by
    by_contra h
    exact hi ⟨hξ i, lt_of_not_ge h⟩
  unfold cavityTerm
  rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_nonneg _) (hm i))]
  calc
    _ ≤ Real.exp (-β * arrivalLength d ω.1 i) * Real.exp (β * arrivalLength d ω.1 i / 2) :=
      mul_le_mul_of_nonneg_left hle (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Certificate

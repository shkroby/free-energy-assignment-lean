import Certificate.ArrivalTruncation
import Certificate.ArrivalHardCoupling
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Uniform truncation at a deterministic index

The length-cutoff estimate becomes a prefix estimate by paying for the
chance that the next arrival still lies inside the length cutoff.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology BigOperators

namespace Certificate

theorem arrivalLength_pos_of_positive_spacings {d : ℝ} {E : ℕ → ℝ}
    (hE : ∀ i, 0 < E i) (i : ℕ) : 0 < arrivalLength d E i := by
  unfold arrivalLength
  exact Real.rpow_pos_of_pos (Finset.sum_pos (fun j _ ↦ hE j)
    ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ _)⟩) _

theorem strictMono_arrivalLength {d : ℝ} (hd : 0 < d) {E : ℕ → ℝ}
    (hE : ∀ i, 0 < E i) : StrictMono (arrivalLength d E) := by
  apply strictMono_nat_of_lt_succ
  intro i
  unfold arrivalLength
  rw [Finset.sum_range_succ (n := i + 1)]
  exact Real.rpow_lt_rpow (Finset.sum_nonneg fun j _ ↦ (hE j).le)
    (lt_add_of_pos_right _ (hE (i + 1))) (one_div_pos.mpr hd)

/-- On any canonical marked law all spacings are positive almost surely. -/
theorem ae_marked_positive_spacings (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ∀ᵐ ω ∂markedSpacings μ, ∀ i, 0 < ω.1 i := by
  let : IsProbabilityMeasure exponentialSpacings := isProbabilityMeasure_exponentialSpacings
  exact (measurePreserving_fst (μ := exponentialSpacings)
    (ν := Measure.infinitePi (fun _ : ℕ ↦ μ))).quasiMeasurePreserving.tendsto_ae.eventually
      ae_expSpacing_pos

/-- The chance that a given arrival still lies within a fixed length is
bounded uniformly over all mark laws by the mean count divided by its index. -/
theorem measure_arrivalLength_le {d R : ℝ} (hd : 0 < d) (hR : 0 ≤ R)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (k : ℕ) :
    markedSpacings μ {ω | arrivalLength d ω.1 k ≤ R} ≤
      ENNReal.ofReal (R ^ d) / ((k + 1 : ℕ) : ℝ≥0∞) := by
  let A : Set (ℝ × ℝ) := Ioc 0 R ×ˢ univ
  let f : ℝ × ℝ → ℝ≥0∞ := A.indicator 1
  have hA : MeasurableSet A := measurableSet_Ioc.prod MeasurableSet.univ
  have hf : Measurable f := measurable_const.indicator hA
  have hM := meas_ge_le_lintegral_div (μ := markedSpacings μ)
    (measurable_arrivalSum d hf).aemeasurable (by positivity : ((k + 1 : ℕ) : ℝ≥0∞) ≠ 0)
    (ENNReal.natCast_ne_top (k + 1))
  have hi : (∫⁻ ω, arrivalSum d f ω ∂markedSpacings μ) = ENNReal.ofReal (R ^ d) := by
    change (∫⁻ ω, ∑' i, f (arrivalLength d ω.1 i, ω.2 i) ∂markedSpacings μ) = _
    rw [canonical_marked_campbell hd μ f hf,
      show (∫⁻ p, f p ∂(intensity d).prod μ) = ((intensity d).prod μ) A from
        lintegral_indicator_one hA,
      show ((intensity d).prod μ) A = ENNReal.ofReal (R ^ d) by
        rw [Measure.prod_prod, intensity_Ioc_zero hd hR, measure_univ, mul_one]]
  rw [hi] at hM
  refine (measure_mono_ae ?_).trans hM
  filter_upwards [ae_marked_positive_spacings μ] with ω hω hlen
  have hsum :
      (∑ i ∈ Finset.range (k + 1), f (arrivalLength d ω.1 i, ω.2 i)) =
        ((k + 1 : ℕ) : ℝ≥0∞) := by
    calc
      _ = ∑ _i ∈ Finset.range (k + 1), (1 : ℝ≥0∞) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hil : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have hmem : (arrivalLength d ω.1 i, ω.2 i) ∈ A :=
          ⟨⟨arrivalLength_pos_of_positive_spacings hω i,
            ((strictMono_arrivalLength hd hω).monotone hil).trans hlen⟩, mem_univ _⟩
        exact indicator_of_mem hmem _
      _ = _ := by simp
  rw [← hsum]
  exact ENNReal.sum_le_tsum _

/-- The right length tail of a finite nonnegative integral tends to zero. -/
theorem lintegral_Ioi_nat_tendsto_zero {μ : Measure ℝ} (g : ℝ → ℝ≥0∞)
    (hg : Measurable g) (hfin : (∫⁻ x, g x ∂μ) ≠ ∞) :
    Tendsto (fun R : ℕ ↦ ∫⁻ x in Ioi (R : ℝ), g x ∂μ) atTop (𝓝 0) := by
  simp_rw [← lintegral_indicator measurableSet_Ioi]
  simpa only [lintegral_zero] using tendsto_lintegral_of_dominated_convergence
    (μ := μ) (F := fun R : ℕ ↦ (Ioi (R : ℝ)).indicator g) (f := fun _ ↦ 0) g
    (fun _ ↦ hg.indicator measurableSet_Ioi)
    (fun _ ↦ .of_forall fun x ↦ indicator_le_self' (fun _ _ ↦ zero_le) x) hfin
    (.of_forall fun x ↦ by
      refine tendsto_const_nhds.congr' ?_
      obtain ⟨N, hN⟩ := exists_nat_ge x
      filter_upwards [eventually_ge_atTop N] with R hR
      exact (indicator_of_notMem (not_lt_of_ge (hN.trans (Nat.cast_le.mpr hR))) _).symm)

/-- Once the first omitted arrival exceeds a length cutoff, the omitted
prefix mass is bounded by the full tail beyond that length. -/
theorem measure_weightedSum_sub_prefix_ge_le {β d R δ : ℝ} (hd : 0 < d) (hβ : 0 < β)
    (hR : 0 ≤ R) (hδ : 0 < δ) (μ : Measure ℝ) [IsProbabilityMeasure μ] (k : ℕ)
    (hmarks : ∀ᵐ x ∂μ, 0 ≤ x)
    (hfin : ∀ᵐ ω ∂markedSpacings μ, arrivalWeightedSum β d ω ≠ ∞) :
    markedSpacings μ {ω | δ ≤ |(arrivalWeightedSum β d ω).toReal -
      ∑ i ∈ Finset.range k, cavityTerm β d ω i|} ≤
      ENNReal.ofReal (R ^ d) / ((k + 1 : ℕ) : ℝ≥0∞) +
      (∫⁻ x in Ioi R, μ (Ioi (Real.exp (β * x / 2))) ∂intensity d) +
      (∫⁻ x in Ioi R, ENNReal.ofReal (Real.exp (-β * x / 2)) ∂intensity d) /
        ENNReal.ofReal (δ / 2) := by
  let P := markedSpacings μ
  let F := fun p : ℝ × ℝ ↦ if R < p.1 then ENNReal.ofReal (Real.exp (-β * p.1) * p.2) else 0
  let Bad : Set ArrivalConfiguration := {ω | arrivalLength d ω.1 k ≤ R}
  let Large : Set ArrivalConfiguration := {ω | ENNReal.ofReal (δ / 2) < arrivalSum d F ω}
  have hM : ∀ᵐ ω ∂P, ∀ i, 0 ≤ ω.2 i := by
    apply ae_all_iff.mpr
    intro i
    exact (markedArrival_eval_preserving μ i).quasiMeasurePreserving.tendsto_ae.eventually hmarks
  have ar : {ω | δ ≤ |(arrivalWeightedSum β d ω).toReal -
        ∑ i ∈ Finset.range k, cavityTerm β d ω i|} ≤ᵐ[P] (Bad ∪ Large : Set ArrivalConfiguration) := by
    filter_upwards [ae_marked_positive_spacings μ, hfin, hM] with ω hpos htotal hm hω
    by_cases hlen : ω ∈ Bad
    · exact Or.inl hlen
    right
    let a : ℕ → ℝ≥0∞ := fun i ↦ ENNReal.ofReal (cavityTerm β d ω i)
    let B : Set ℕ := ((Finset.range k : Finset ℕ) : Set ℕ)ᶜ
    let T := ∑' i : B, a i
    have hnonneg (i : ℕ) : 0 ≤ cavityTerm β d ω i := mul_nonneg (Real.exp_nonneg _) (hm i)
    have hsplit : ENNReal.ofReal (∑ i ∈ Finset.range k, cavityTerm β d ω i) + T =
        arrivalWeightedSum β d ω := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ hnonneg i)]
      exact ENNReal.sum_add_tsum_compl (Finset.range k) a
    have hT : T ≠ ∞ :=
      ne_top_of_le_ne_top htotal (le_add_self.trans_eq hsplit)
    have hr := congrArg ENNReal.toReal hsplit
    rw [ENNReal.toReal_add ENNReal.ofReal_ne_top hT,
      ENNReal.toReal_ofReal (Finset.sum_nonneg (fun i _ ↦ hnonneg i))] at hr
    have hδT : δ ≤ T.toReal := by
      change δ ≤ |(arrivalWeightedSum β d ω).toReal -
        ∑ i ∈ Finset.range k, cavityTerm β d ω i| at hω
      rw [← hr, add_sub_cancel_left, abs_of_nonneg ENNReal.toReal_nonneg] at hω
      exact hω
    have htail : T ≤ arrivalSum d F ω := by
      unfold T
      rw [tsum_subtype]
      apply ENNReal.tsum_le_tsum
      intro i
      by_cases hi : i ∈ B
      · have hik : k ≤ i := le_of_not_gt fun h ↦ hi (Finset.mem_range.mpr h)
        have hRi := (lt_of_not_ge hlen).trans_le ((strictMono_arrivalLength hd hpos).monotone hik)
        rw [indicator_of_mem hi]
        exact (if_pos hRi).symm.le
      · rw [indicator_of_notMem hi]
        exact zero_le
    change ENNReal.ofReal (δ / 2) < arrivalSum d F ω
    exact (((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mpr
      ((half_lt_self hδ).trans_le hδT)).trans_eq (ENNReal.ofReal_toReal hT)).trans_le htail
  have hcut := measure_arrival_weight_tail_gt_le hd hβ le_rfl hR μ
    (show ENNReal.ofReal (δ / 2) ≠ 0 from (ENNReal.ofReal_pos.mpr (half_pos hδ)).ne')
    ENNReal.ofReal_ne_top
  calc
    _ ≤ P (Bad ∪ Large) := measure_mono_ae ar
    _ ≤ P Bad + P Large := measure_union_le _ _
    _ ≤ _ := by
      have h := add_le_add (measure_arrivalLength_le hd hR μ k) hcut
      simpa only [add_assoc] using h

/-- A common stretched-logarithmic upper tail makes the prefix
approximation uniform in the mark law. -/
theorem exists_uniform_cavity_prefix_error {β d c K : ℝ} (hβ : 0 < β) (hd : 0 < d)
    (hc : 0 < c) (hK : 0 ≤ K) {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∃ k : ℕ, ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
      (∀ᵐ x ∂μ, 0 ≤ x) →
      (∀ x > 0, μ (Ioi (Real.exp (β * x / 2))) ≤
        ENNReal.ofReal (K * Real.exp (-(c * x ^ d)))) →
      (markedSpacings μ).real {ω | δ ≤ |(arrivalWeightedSum β d ω).toReal -
        ∑ i ∈ Finset.range k, cavityTerm β d ω i|} ≤ η := by
  let e := ENNReal.ofReal (δ / 2)
  let E := ENNReal.ofReal η
  let f : ℝ → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (K * Real.exp (-(c * x ^ d)))
  let g : ℝ → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (Real.exp (-β * x / 2))
  let a (R : ℕ) := ∫⁻ x in Ioi (R : ℝ), f x ∂intensity d
  let b (R : ℕ) := ∫⁻ x in Ioi (R : ℝ), g x ∂intensity d
  have he : e ≠ 0 := (ENNReal.ofReal_pos.mpr (half_pos hδ)).ne'
  have hE : 0 < E / 2 := ENNReal.half_pos (ENNReal.ofReal_pos.mpr hη).ne'
  have hf : Measurable f := by unfold f; fun_prop
  have hg : Measurable g := by unfold g; fun_prop
  have hfinF : (∫⁻ x, f x ∂intensity d) ≠ ∞ := by
    have hI : Integrable (fun x : ℝ ↦ K * Real.exp (-(c * x ^ d))) (intensity d) := by
      simpa only [neg_mul] using (integrable_intensity_exp_rpow hd hd hc).const_mul K
    exact ((hasFiniteIntegral_iff_ofReal (.of_forall fun _ ↦
      mul_nonneg hK (Real.exp_nonneg _))).mp hI.2).ne
  have hfinG : (∫⁻ x, g x ∂intensity d) ≠ ∞ := by
    have hI : Integrable (fun x : ℝ ↦ Real.exp (-β * x / 2)) (intensity d) := by
      convert integrable_intensity_exp_rpow hd zero_lt_one (half_pos hβ) using 1
      ext x
      simp only [Real.rpow_one]
      congr 1
      ring
    exact ((hasFiniteIntegral_iff_ofReal (.of_forall fun _ ↦
      Real.exp_nonneg _)).mp hI.2).ne
  have ha : Tendsto a atTop (𝓝 0) := lintegral_Ioi_nat_tendsto_zero f hf hfinF
  have hb : Tendsto b atTop (𝓝 0) := lintegral_Ioi_nat_tendsto_zero g hg hfinG
  have hab : Tendsto (fun R ↦ a R + b R / e) atTop (𝓝 0) := by
    simpa only [ENNReal.zero_div, zero_add] using
      ha.add (ENNReal.Tendsto.div_const hb (Or.inr he))
  obtain ⟨R, hR⟩ := (hab.eventually (Iio_mem_nhds hE)).exists
  have hKlim : Tendsto (fun k : ℕ ↦ ENNReal.ofReal ((R : ℝ) ^ d) / ((k + 1 : ℕ) : ℝ≥0∞))
      atTop (𝓝 0) := by
    have ht := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal ((R : ℝ) ^ d))
      (ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1))
      (Or.inr ENNReal.ofReal_ne_top)
    simpa only [div_eq_mul_inv, Function.comp_apply, mul_zero] using ht
  obtain ⟨k, hk⟩ := (hKlim.eventually (Iio_mem_nhds hE)).exists
  refine ⟨k, fun μ _ hμ hTail ↦ ?_⟩
  have hp : ∀ᵐ ω ∂markedSpacings μ, ∀ i, 0 ≤ ω.2 i := by
    apply ae_all_iff.mpr
    intro i
    exact (markedArrival_eval_preserving μ i).quasiMeasurePreserving.tendsto_ae.eventually hμ
  have hfin : ∀ᵐ ω ∂markedSpacings μ, arrivalWeightedSum β d ω ≠ ∞ := by
    filter_upwards [ae_summable_cavityTerm_of_stretched_log_tail hd hβ hc hK μ hμ hTail, hp]
      with ω hs hNonneg
    unfold arrivalWeightedSum
    have hterm (i : ℕ) : 0 ≤ cavityTerm β d ω i :=
      mul_nonneg (Real.exp_nonneg _) (hNonneg i)
    rw [← ENNReal.ofReal_tsum_of_nonneg hterm hs]
    exact ENNReal.ofReal_ne_top
  have hcut := measure_weightedSum_sub_prefix_ge_le hd hβ (Nat.cast_nonneg R) hδ μ k hμ hfin
  have hint : (∫⁻ x in Ioi (R : ℝ), μ (Ioi (Real.exp (β * x / 2))) ∂intensity d) ≤ a R := by
    apply setLIntegral_mono' measurableSet_Ioi
    intro x hx
    exact hTail x ((Nat.cast_nonneg R).trans_lt hx)
  have hsmall := hcut.trans (by
    have hR' : a R + b R / e ≤ E / 2 := hR.le
    calc
      _ ≤ ENNReal.ofReal ((R : ℝ) ^ d) / ((k + 1 : ℕ) : ℝ≥0∞) + (a R + b R / e) := by
        rw [← add_assoc]
        gcongr
      _ ≤ E / 2 + E / 2 := add_le_add hk.le hR'
      _ = E := ENNReal.add_halves E)
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hsmall).trans_eq (ENNReal.toReal_ofReal hη.le)

end Certificate

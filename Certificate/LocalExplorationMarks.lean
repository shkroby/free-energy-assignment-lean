import Certificate.RootEdgeMarks
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-!
# Weak convergence of the retained lengths

The small-cost assumption excludes an atom at zero and determines the
limiting retained-length CDF at every point. Half-open intervals and their
finite-dimensional products give the required Portmanteau test systems.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology NNReal

namespace Certificate.LocalExploration

/-- The small-cost assumption rules out an atom at zero. -/
theorem cdf_zero_of_smallCostTail {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {d κ : ℝ} (hd : 0 < d) (hκ : 0 < κ) (h : SmallCostTail μ κ d) :
    cdf μ 0 = 0 := by
  have hid : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hpow := (hid.rpow_const_nhds_zero hd).const_mul κ
  have hmul := h.2.mul hpow
  simp only [mul_zero] at hmul
  have hlim : Tendsto (cdf μ) (𝓝[>] 0) (𝓝 0) := by
    refine hmul.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    exact div_mul_cancel₀ _ (mul_pos hκ (Real.rpow_pos_of_pos ht _)).ne'
  refine le_antisymm (ge_of_tendsto hlim ?_) (cdf_nonneg μ 0)
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  exact monotone_cdf μ ht.le

private theorem retainedLengthLaw_apply_nonpos {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {d κ R x : ℝ} (hd : 0 < d) (hκ : 0 < κ) (h : SmallCostTail μ κ d) (hx : x ≤ 0)
    {n : ℕ} (hn : 0 < n) :
    retainedLengthLaw μ d κ R n (Iic x) = 0 := by
  have hscale : 0 < lengthScale d κ n :=
    Real.rpow_pos_of_pos (mul_pos hκ (Nat.cast_pos.mpr hn)) _
  have hprob : shortEdgeProbability μ d κ x n = 0 := by
    unfold shortEdgeProbability
    apply le_antisymm _ (cdf_nonneg μ _)
    rw [← cdf_zero_of_smallCostTail hd hκ h]
    exact monotone_cdf μ (div_nonpos_of_nonpos_of_nonneg hx hscale.le)
  have hbase : scaledLengthLaw μ d κ n (Iic x) = 0 := by
    rw [scaledLengthLaw_Iic hκ hn, hprob, ENNReal.ofReal_zero]
  have hcut : scaledLengthLaw μ d κ n (Iic x ∩ Iic R) = 0 :=
    nonpos_iff_eq_zero.mp ((measure_mono Set.inter_subset_left).trans_eq hbase)
  rw [retainedLengthLaw, Measure.smul_apply, Measure.restrict_apply measurableSet_Iic, hcut, smul_zero]

private theorem retainedLengthLaw_apply_ge {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {d κ R x : ℝ} (hκ : 0 < κ) (hR : 0 < R) (h : SmallCostTail μ κ d) (hx : R ≤ x)
    {n : ℕ} (hn : 0 < n) :
    retainedLengthLaw μ d κ R n (Iic x) = 1 := by
  have hp := retainedLengthLaw_isProbabilityMeasure hκ hR h hn
  rw [← hp.measure_univ, retainedLengthLaw, Measure.smul_apply, Measure.smul_apply,
    Measure.restrict_apply measurableSet_Iic, Measure.restrict_apply_univ,
    Set.inter_eq_right.mpr (Iic_subset_Iic.mpr hx)]

/-- The limiting distribution of one length conditional on being retained. -/
noncomputable def truncatedIntensity (d R : ℝ) : Measure ℝ :=
  (ENNReal.ofReal (R ^ d))⁻¹ • (intensity d).restrict (Ioc 0 R)

theorem isProbabilityMeasure_truncatedIntensity {d R : ℝ} (hd : 0 < d) (hR : 0 < R) :
    IsProbabilityMeasure (truncatedIntensity d R) where
  measure_univ := by
    rw [truncatedIntensity, Measure.smul_apply, Measure.restrict_apply_univ, intensity_Ioc_zero hd hR.le]
    exact ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr (Real.rpow_pos_of_pos hR _))
      ENNReal.ofReal_ne_top

private theorem truncatedIntensity_apply_nonpos {d R x : ℝ} (hx : x ≤ 0) :
    truncatedIntensity d R (Iic x) = 0 := by
  have he : Iic x ∩ Ioc 0 R = ∅ := by
    ext y
    constructor
    · intro hy
      exact False.elim (hy.2.1.not_ge (hy.1.trans hx))
    · exact False.elim
  rw [truncatedIntensity, Measure.smul_apply, Measure.restrict_apply measurableSet_Iic,
    he, measure_empty, smul_zero]

private theorem truncatedIntensity_apply_ge {d R x : ℝ} (hd : 0 < d) (hR : 0 < R) (hx : R ≤ x) :
    truncatedIntensity d R (Iic x) = 1 := by
  have hp := isProbabilityMeasure_truncatedIntensity hd hR
  rw [← hp.measure_univ, truncatedIntensity, Measure.smul_apply, Measure.smul_apply,
    Measure.restrict_apply measurableSet_Iic, Measure.restrict_apply_univ]
  congr 1
  rw [Set.inter_eq_right.mpr (fun _ hy => hy.2.trans hx)]

private theorem truncatedIntensity_real_Iic {d R x : ℝ}
    (hd : 0 < d) (hR : 0 < R) (hx : 0 ≤ x) (hxR : x ≤ R) :
    (truncatedIntensity d R).real (Iic x) = (x / R) ^ d := by
  have he : Iic x ∩ Ioc 0 R = Ioc 0 x := by
    ext y
    exact ⟨fun hy => ⟨hy.2.1, hy.1⟩, fun hy => ⟨hy.2, hy.1, hy.2.trans hxR⟩⟩
  rw [measureReal_def, truncatedIntensity, Measure.smul_apply, Measure.restrict_apply measurableSet_Iic,
    he, intensity_Ioc_zero hd hx, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (Real.rpow_nonneg hR.le _),
    ENNReal.toReal_ofReal (Real.rpow_nonneg hx _), Real.div_rpow hx hR.le, div_eq_mul_inv, mul_comm]

/-- The CDF limit for the retained length at every real threshold, including
zero and the truncation endpoint. -/
theorem tendsto_retainedLengthLaw_real_Iic {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {d κ R : ℝ} (hd : 0 < d) (hκ : 0 < κ) (hR : 0 < R)
    (h : SmallCostTail μ κ d) (x : ℝ) :
    Tendsto (fun n : ℕ => (retainedLengthLaw μ d κ R n).real (Iic x)) atTop
      (𝓝 ((truncatedIntensity d R).real (Iic x))) := by
  by_cases h₀ : x ≤ 0
  · rw [measureReal_def, truncatedIntensity_apply_nonpos h₀, ENNReal.toReal_zero]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    rw [measureReal_def, retainedLengthLaw_apply_nonpos hd hκ h h₀ hn, ENNReal.toReal_zero]
  · by_cases h₁ : x ≤ R
    · rw [truncatedIntensity_real_Iic hd hR (le_of_not_ge h₀) h₁]
      exact tendsto_retainedLengthLaw_Iic hd hκ (lt_of_not_ge h₀) h₁ h
    · have hx : R ≤ x := le_of_not_ge h₁
      rw [measureReal_def, truncatedIntensity_apply_ge hd hR hx, ENNReal.toReal_one]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      rw [measureReal_def, retainedLengthLaw_apply_ge hκ hR h hx hn, ENNReal.toReal_one]

private theorem probabilityMeasure_real_Ioc (P : ProbabilityMeasure ℝ) {a b : ℝ} (h : a ≤ b) :
    ((P : Measure ℝ).real (Ioc a b)) =
      (P : Measure ℝ).real (Iic b) - (P : Measure ℝ).real (Iic a) := by
  rw [← Iic_sdiff_Iic, measureReal_sdiff (Iic_subset_Iic.mpr h) measurableSet_Iic]

private theorem tendsto_probabilityMeasure_Ioc {f : ℕ → ProbabilityMeasure ℝ} {G : ProbabilityMeasure ℝ}
    (h : ∀ x : ℝ, Tendsto (fun n => (f n : Measure ℝ).real (Iic x)) atTop
      (𝓝 ((G : Measure ℝ).real (Iic x)))) (a b : ℝ) :
    Tendsto (fun n => f n (Ioc a b)) atTop (𝓝 (G (Ioc a b))) := by
  by_cases hab : a ≤ b
  · apply NNReal.tendsto_coe.mp
    simpa only [← ProbabilityMeasure.measureReal_eq_coe_coeFn,
      probabilityMeasure_real_Ioc _ hab] using (h b).sub (h a)
  · simp [Ioc_eq_empty (by linarith : ¬ a < b)]

private theorem Ioc_half_subset_ball (x : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Ioc (x - δ / 2) (x + δ / 2) ⊆ Metric.ball x δ := by
  intro y hy
  rw [Metric.mem_ball, Real.dist_eq]
  exact abs_lt.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩

/-- Portmanteau with half-open intervals as the local pi-system. -/
theorem tendsto_probabilityMeasure_of_cdf {f : ℕ → ProbabilityMeasure ℝ} {G : ProbabilityMeasure ℝ}
    (h : ∀ x : ℝ, Tendsto (fun n => (f n : Measure ℝ).real (Iic x)) atTop
      (𝓝 ((G : Measure ℝ).real (Iic x)))) :
    Tendsto f atTop (𝓝 G) := by
  have hπ := isPiSystem_Ioc (id : ℝ → ℝ) (id : ℝ → ℝ)
  refine hπ.tendsto_probabilityMeasure_of_tendsto_of_mem ?_ ?_ ?_
  · rintro s ⟨a, b, hab, rfl⟩
    exact measurableSet_Ioc
  · intro s hs x hx
    obtain ⟨δ, hδ, hsub⟩ := Metric.isOpen_iff.mp hs x hx
    refine ⟨Ioc (x - δ / 2) (x + δ / 2),
      ⟨x - δ / 2, x + δ / 2, by change x - δ / 2 < x + δ / 2; linarith, rfl⟩,
      Ioc_mem_nhds (by linarith) (by linarith), (Ioc_half_subset_ball x hδ).trans hsub⟩
  · rintro s ⟨a, b, hab, rfl⟩
    exact tendsto_probabilityMeasure_Ioc h a b

/-- Actual retained edge length law for positive size `n+1`. -/
noncomputable def retainedMarkProbability {μ : Measure ℝ} [IsProbabilityMeasure μ] {d κ R : ℝ}
    (hκ : 0 < κ) (hR : 0 < R) (h : SmallCostTail μ κ d) (n : ℕ) : ProbabilityMeasure ℝ :=
  ⟨retainedLengthLaw μ d κ R (n + 1), retainedLengthLaw_isProbabilityMeasure hκ hR h (Nat.zero_lt_succ _)⟩

/-- The normalized restriction of the length intensity to `(0, R]`. -/
noncomputable def limitingMarkProbability {d R : ℝ}
    (hd : 0 < d) (hR : 0 < R) : ProbabilityMeasure ℝ :=
  ⟨truncatedIntensity d R, isProbabilityMeasure_truncatedIntensity hd hR⟩

/-- Weak convergence of the normalized retained-length law. -/
theorem tendsto_retainedMarkProbability {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {d κ R : ℝ} (hd : 0 < d) (hκ : 0 < κ) (hR : 0 < R) (h : SmallCostTail μ κ d) :
    Tendsto (retainedMarkProbability hκ hR h) atTop (𝓝 (limitingMarkProbability hd hR)) := by
  apply tendsto_probabilityMeasure_of_cdf
  intro x
  exact (tendsto_retainedLengthLaw_real_Iic hd hκ hR h x).comp (tendsto_add_atTop_nat 1)

/-- The probability law of finitely many independent marks. -/
noncomputable def finiteMarkProduct {I : Type*} [Fintype I]
    (P : I → ProbabilityMeasure ℝ) : ProbabilityMeasure (I → ℝ) :=
  ⟨Measure.infinitePi (fun i => (P i : Measure ℝ)), inferInstance⟩

theorem finiteMarkProduct_apply_pi {I : Type*} [Fintype I] (P : I → ProbabilityMeasure ℝ)
    (U : I → Set ℝ) (hU : ∀ i, MeasurableSet (U i)) :
    finiteMarkProduct P (Set.univ.pi U) = ∏ i, P i (U i) := by
  change (Measure.infinitePi (fun i => (P i : Measure ℝ)) (Set.univ.pi U)).toNNReal = _
  rw [Measure.infinitePi_pi_univ _ hU, tprod_fintype, ENNReal.toNNReal_prod]
  rfl

private def halfOpenBox (I : Type*) : Set (Set (I → ℝ)) :=
  {U | ∃ a b : I → ℝ, (Set.univ.pi fun i => Ioc (a i) (b i)) = U}

private theorem isPiSystem_halfOpenBox (I : Type*) : IsPiSystem (halfOpenBox I) := by
  rintro _ ⟨a, b, rfl⟩ _ ⟨a', b', rfl⟩ _
  refine ⟨fun i => max (a i) (a' i), fun i => min (b i) (b' i), ?_⟩
  rw [← Set.pi_inter_distrib]
  simp only [Ioc_inter_Ioc]

private theorem halfOpenBox_basis {I : Type*} [Fintype I] (U : Set (I → ℝ))
    (hU : IsOpen U) (x : I → ℝ) (hx : x ∈ U) :
    ∃ B ∈ halfOpenBox I, B ∈ 𝓝 x ∧ B ⊆ U := by
  obtain ⟨δ, hδ, hsub⟩ := Metric.isOpen_iff.mp hU x hx
  let a (i : I) := x i - δ / 2
  let b (i : I) := x i + δ / 2
  let B : Set (I → ℝ) := Set.univ.pi (fun i => Ioc (a i) (b i))
  refine ⟨B, ⟨a, b, rfl⟩, ?_, ?_⟩
  · apply set_pi_mem_nhds Set.finite_univ
    intro i _
    apply Ioc_mem_nhds <;> dsimp [a, b] <;> linarith
  · apply Subset.trans _ hsub
    rw [ball_pi x hδ]
    intro y hy i hi
    exact Ioc_half_subset_ball (x i) hδ (hy i hi)

/-- One-dimensional CDF convergence in each coordinate implies weak
convergence of the joint laws of finitely many independent coordinates. -/
theorem tendsto_finiteMarkProduct_of_cdf {I : Type*} [Fintype I]
    {f : ℕ → I → ProbabilityMeasure ℝ} {G : I → ProbabilityMeasure ℝ}
    (h : ∀ (i : I) (x : ℝ), Tendsto (fun n => (f n i : Measure ℝ).real (Iic x)) atTop
      (𝓝 ((G i : Measure ℝ).real (Iic x)))) :
    Tendsto (fun n => finiteMarkProduct (f n)) atTop (𝓝 (finiteMarkProduct G)) := by
  apply (isPiSystem_halfOpenBox I).tendsto_probabilityMeasure_of_tendsto_of_mem
  · rintro U ⟨a, b, rfl⟩
    exact MeasurableSet.univ_pi (fun _ => measurableSet_Ioc)
  · exact halfOpenBox_basis
  · rintro _ ⟨a, b, rfl⟩
    simp_rw [finiteMarkProduct_apply_pi _ _ (fun _ => measurableSet_Ioc)]
    exact tendsto_finsetProd Finset.univ (fun i _ => tendsto_probabilityMeasure_Ioc (h i) _ _)

/-- Weak convergence of any fixed finite collection of independent retained lengths. -/
theorem tendsto_retainedMarkProduct {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {d κ R : ℝ} (hd : 0 < d) (hκ : 0 < κ) (hR : 0 < R) (h : SmallCostTail μ κ d)
    (I : Type*) [Fintype I] :
    Tendsto (fun n => finiteMarkProduct (fun _ : I => retainedMarkProbability hκ hR h n)) atTop
      (𝓝 (finiteMarkProduct (fun _ : I => limitingMarkProbability hd hR))) := by
  apply tendsto_finiteMarkProduct_of_cdf
  intro _ x
  exact (tendsto_retainedLengthLaw_real_Iic hd hκ hR h x).comp (tendsto_add_atTop_nat 1)

end Certificate.LocalExploration

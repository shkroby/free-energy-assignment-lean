import Certificate.LocalExplorationMarks
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.Probability.Independence.InfinitePi

/-! Weak continuity of the canonical marked weighted sum restricted to its first finitely
many arrivals. The mark laws may have atoms. -/

open Filter MeasureTheory ProbabilityTheory Set Metric
open scoped Topology

namespace Certificate.LocalExploration

/-- A finite product of independently sampled real coordinates is weakly continuous
in the coordinate laws. -/
theorem tendsto_finiteMarkProduct_of_weak {I ι : Type*} [Fintype I]
    {νs : ι → I → ProbabilityMeasure ℝ} {ν : I → ProbabilityMeasure ℝ}
    {L : Filter ι} [L.IsCountablyGenerated]
    (h : ∀ i, Tendsto (fun n => νs n i) L (𝓝 (ν i))) :
    Tendsto (fun n => finiteMarkProduct (νs n)) L (𝓝 (finiteMarkProduct ν)) := by
  let S : Set (Set (I → ℝ)) := {s | ∃ U : I → Set ℝ,
    (∀ i, MeasurableSet (U i)) ∧ (∀ i, ν i (frontier (U i)) = 0) ∧ s = univ.pi U}
  have hS : IsPiSystem S := by
    rintro _ ⟨U, hU, hUn, rfl⟩ _ ⟨V, hV, hVn, rfl⟩ _
    refine ⟨fun i => U i ∩ V i, fun i => (hU i).inter (hV i), ?_, ?_⟩
    · intro i
      have hUi := hUn i
      have hVi := hVn i
      rw [ProbabilityMeasure.null_iff_toMeasure_null] at hUi hVi ⊢
      exact null_frontier_inter hUi hVi
    · exact Set.pi_inter_distrib.symm
  apply hS.tendsto_probabilityMeasure_of_tendsto_of_mem
  · rintro _ ⟨U, hU, _, rfl⟩
    exact MeasurableSet.univ_pi hU
  · intro G hG x hx
    obtain ⟨δ, hδ, hsub⟩ := Metric.isOpen_iff.mp hG x hx
    choose r hr hn using
      fun i => exists_null_frontier_thickening (ν i : Measure ℝ) {x i} hδ
    simp only [thickening_singleton] at hn
    refine ⟨univ.pi (fun i => ball (x i) (r i)), ⟨_, fun _ => measurableSet_ball, ?_, rfl⟩,
      ?_, ?_⟩
    · intro i
      rw [ProbabilityMeasure.null_iff_toMeasure_null]
      exact hn i
    · apply set_pi_mem_nhds Set.finite_univ
      intro i _
      exact ball_mem_nhds _ (hr i).1
    · apply Subset.trans _ hsub
      rw [ball_pi x hδ]
      intro y hy i hi
      exact ball_subset_ball (hr i).2.le (hy i hi)
  · rintro _ ⟨U, hU, hn, rfl⟩
    simp_rw [finiteMarkProduct_apply_pi _ _ hU]
    exact tendsto_finsetProd Finset.univ
      (fun i _ => ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto (h i) (hn i))

end Certificate.LocalExploration

namespace Certificate

open LocalExploration

instance markedSpacings_isProbabilityMeasure (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (markedSpacings μ) := by
  let : IsProbabilityMeasure exponentialSpacings := isProbabilityMeasure_exponentialSpacings
  unfold markedSpacings
  infer_instance

private noncomputable def unitExponentialProbability : ProbabilityMeasure ℝ :=
  ⟨expMeasure 1, isProbabilityMeasure_expMeasure zero_lt_one⟩

private def prefixProjection (k : ℕ) (ω : (ℕ → ℝ) × (ℕ → ℝ)) :
    (Fin k → ℝ) × (Fin k → ℝ) :=
  Prod.map (fun E i => E i.val) (fun M i => M i.val) ω

private theorem measurable_prefixProjection (k : ℕ) : Measurable (prefixProjection k) := by
  unfold prefixProjection
  fun_prop

private noncomputable def cavityPrefixJointProbability (k : ℕ) (P : ProbabilityMeasure ℝ) :
    ProbabilityMeasure ((Fin k → ℝ) × (Fin k → ℝ)) :=
  (finiteMarkProduct (fun _ : Fin k => unitExponentialProbability)).prod
    (finiteMarkProduct (fun _ : Fin k => P))

private theorem map_prefixProjection (k : ℕ) (P : ProbabilityMeasure ℝ) :
    (markedSpacings (P : Measure ℝ)).map (prefixProjection k) = cavityPrefixJointProbability k P := by
  let : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure zero_lt_one
  have hm : Measurable (fun (x : ℕ → ℝ) (i : Fin k) => x i.val) := by fun_prop
  unfold markedSpacings prefixProjection cavityPrefixJointProbability exponentialSpacings
  rw [← Measure.map_prod_map _ _ hm hm]
  rw [Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective,
    Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective]
  rfl

/-- Sum of the canonical cavity terms over the first `k` arrivals. -/
noncomputable def cavityPrefixSum (β d : ℝ) (k : ℕ) (ω : (ℕ → ℝ) × (ℕ → ℝ)) : ℝ :=
  ∑ i ∈ Finset.range k, cavityTerm β d ω i

private def extendPrefix {k : ℕ} (x : Fin k → ℝ) (j : ℕ) : ℝ :=
  if h : j < k then x ⟨j, h⟩ else 0

private theorem continuous_extendPrefix_apply {k : ℕ} (j : ℕ) :
    Continuous (fun (x : Fin k → ℝ) => extendPrefix x j) := by
  by_cases h : j < k
  · simp only [extendPrefix, dif_pos h]
    exact continuous_apply _
  · simp only [extendPrefix, dif_neg h]
    exact continuous_const

private noncomputable def finitePrefixWeightedSum (β d : ℝ) (k : ℕ)
    (p : (Fin k → ℝ) × (Fin k → ℝ)) : ℝ :=
  ∑ i : Fin k, cavityTerm β d (extendPrefix p.1, extendPrefix p.2) i.val

private theorem continuous_finitePrefixWeightedSum (β : ℝ) {d : ℝ} (hd : 0 < d) (k : ℕ) :
    Continuous (finitePrefixWeightedSum β d k) := by
  unfold finitePrefixWeightedSum
  apply continuous_finsetSum
  intro i _
  dsimp only [cavityTerm, arrivalLength]
  apply Continuous.mul
  · apply Real.continuous_exp.comp
    apply continuous_const.mul
    apply (Real.continuous_rpow_const (one_div_nonneg.mpr hd.le)).comp
    exact continuous_finsetSum _ (fun j _ => (continuous_extendPrefix_apply j).comp continuous_fst)
  · exact (continuous_extendPrefix_apply i.val).comp continuous_snd

private theorem cavityPrefixSum_eq_comp (β d : ℝ) (k : ℕ) :
    cavityPrefixSum β d k = finitePrefixWeightedSum β d k ∘ prefixProjection k := by
  funext ω
  unfold cavityPrefixSum
  rw [← Fin.sum_univ_eq_sum_range]
  change ∑ i : Fin k, cavityTerm β d ω i.val =
    ∑ i : Fin k,
      cavityTerm β d (extendPrefix (prefixProjection k ω).1,
        extendPrefix (prefixProjection k ω).2) i.val
  apply Finset.sum_congr rfl
  intro i _
  have hsum : (∑ j ∈ Finset.range (i.val + 1), ω.1 j) =
      ∑ j ∈ Finset.range (i.val + 1), extendPrefix (prefixProjection k ω).1 j := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j < k := lt_of_le_of_lt (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) i.isLt
    simp [prefixProjection, extendPrefix, hj']
  simp only [cavityTerm, arrivalLength, hsum]
  simp [prefixProjection, extendPrefix, i.isLt]

/-- The sum over finitely many canonical arrivals is measurable on the full mark space. -/
theorem measurable_cavityPrefixSum (β : ℝ) {d : ℝ} (hd : 0 < d) (k : ℕ) :
    Measurable (cavityPrefixSum β d k) := by
  rw [cavityPrefixSum_eq_comp]
  exact (continuous_finitePrefixWeightedSum β hd k).measurable.comp (measurable_prefixProjection k)

/-- Law of the sum over the first `k` weighted marked arrivals. -/
noncomputable def cavityPrefixProbability (β : ℝ) {d : ℝ} (hd : 0 < d) (k : ℕ)
    (P : ProbabilityMeasure ℝ) : ProbabilityMeasure ℝ :=
  (cavityPrefixJointProbability k P).map
    (continuous_finitePrefixWeightedSum β hd k).measurable.aemeasurable

theorem cavityPrefixProbability_toMeasure (β : ℝ) {d : ℝ} (hd : 0 < d) (k : ℕ)
    (P : ProbabilityMeasure ℝ) :
    (cavityPrefixProbability β hd k P : Measure ℝ) =
      (markedSpacings (P : Measure ℝ)).map (cavityPrefixSum β d k) := by
  rw [cavityPrefixProbability, ProbabilityMeasure.toMeasure_map, ← map_prefixProjection,
    Measure.map_map (continuous_finitePrefixWeightedSum β hd k).measurable
      (measurable_prefixProjection k), cavityPrefixSum_eq_comp]

/-- Weak convergence of the child-mark laws gives weak convergence of each actual finite
prefix of the weighted cavity sum. -/
theorem tendsto_cavityPrefixProbability {ι : Type*} {L : Filter ι} [L.IsCountablyGenerated]
    {νs : ι → ProbabilityMeasure ℝ} {ν : ProbabilityMeasure ℝ}
    (h : Tendsto νs L (𝓝 ν)) (β : ℝ) {d : ℝ} (hd : 0 < d) (k : ℕ) :
    Tendsto (fun n => cavityPrefixProbability β hd k (νs n)) L
      (𝓝 (cavityPrefixProbability β hd k ν)) := by
  apply ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
  · let Q := finiteMarkProduct (fun _ : Fin k => unitExponentialProbability)
    have hmark : Tendsto (fun n => finiteMarkProduct (fun _ : Fin k => νs n)) L
        (𝓝 (finiteMarkProduct (fun _ : Fin k => ν))) :=
      tendsto_finiteMarkProduct_of_weak (fun _ => h)
    have hjoint : Tendsto (fun n => (Q, finiteMarkProduct (fun _ : Fin k => νs n))) L
        (𝓝 (Q, finiteMarkProduct (fun _ : Fin k => ν))) :=
      tendsto_const_nhds.prodMk_nhds hmark
    exact ProbabilityMeasure.continuous_prod.continuousAt.tendsto.comp hjoint
  · exact continuous_finitePrefixWeightedSum β hd k

/-- A convergence-in-distribution version on the canonical infinite-array spaces. -/
theorem tendstoInDistribution_cavityPrefix {ι : Type*} {L : Filter ι}
    [L.IsCountablyGenerated] {νs : ι → ProbabilityMeasure ℝ} {ν : ProbabilityMeasure ℝ}
    (h : Tendsto νs L (𝓝 ν)) (β : ℝ) {d : ℝ} (hd : 0 < d) (k : ℕ) :
    TendstoInDistribution (fun _ : ι => cavityPrefixSum β d k) L (cavityPrefixSum β d k)
      (fun n => markedSpacings (νs n : Measure ℝ)) (markedSpacings (ν : Measure ℝ)) := by
  have hm (P : ProbabilityMeasure ℝ) :
      AEMeasurable (cavityPrefixSum β d k) (markedSpacings (P : Measure ℝ)) :=
    (measurable_cavityPrefixSum β hd k).aemeasurable
  refine ⟨fun n => hm (νs n), hm ν, ?_⟩
  have hcast (P : ProbabilityMeasure ℝ) :
      (⟨(markedSpacings (P : Measure ℝ)).map (cavityPrefixSum β d k),
        Measure.isProbabilityMeasure_map (hm P)⟩ : ProbabilityMeasure ℝ) =
      cavityPrefixProbability β hd k P :=
    Subtype.ext (cavityPrefixProbability_toMeasure β hd k P).symm
  simp only [hcast]
  exact tendsto_cavityPrefixProbability h β hd k

end Certificate

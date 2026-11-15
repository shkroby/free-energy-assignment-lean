import Certificate.SoftExpected
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! Expected pressure and uniform approximation for actual cutoff graphs. -/

open Filter Finset MeasureTheory Set
open scoped ENNReal Topology

namespace Certificate

namespace Tree

theorem monomerPartition_masked_weights {V E : Type*} [DecidableEq V] [DecidableEq E]
    (ends : E → Finset V) (vertices : Finset V) {kept edges : Finset E} (h : kept ⊆ edges)
    (w : E → ℝ) (z : ℝ) :
    monomerPartition ends vertices kept w z =
      monomerPartition ends vertices edges (fun e => if e ∈ kept then w e else 0) z := by
  classical
  have hsub : matchings ends vertices kept ⊆ matchings ends vertices edges := by
    intro M hM
    have hs := mem_matchings.mp hM
    exact mem_matchings.mpr ⟨hs.1.trans h, hs.2⟩
  unfold monomerPartition
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun M hM => ?_
    have hs := (mem_matchings.mp hM).1
    rw [show (∏ e ∈ M, if e ∈ kept then w e else 0) = ∏ e ∈ M, w e from
      Finset.prod_congr rfl (fun e he => if_pos (hs he))]
  · intro M hM hnot
    have hn : ¬ M ⊆ kept := fun hMk => hnot (mem_matchings.mpr ⟨hMk, (mem_matchings.mp hM).2⟩)
    obtain ⟨e, he, hne⟩ := Finset.not_subset.mp hn
    rw [Finset.prod_eq_zero he (if_neg hne), mul_zero]

end Tree

noncomputable def cutoffAssignmentGraph (β d κ R : ℝ) (n : ℕ) (C : CostArray) :
    WeightedGraph (Fin n ⊕ Fin n) (Fin n × Fin n) :=
  (assignmentGraph β d κ n C).retain (retainedEdges d κ R n C) (Finset.subset_univ _)

noncomputable def cutoffAssignmentPressure (β d κ R t : ℝ) (n : ℕ) (C : CostArray) : ℝ :=
  Real.log ((cutoffAssignmentGraph β d κ R n C).Z t) / n

theorem measurable_masked_assignment_weight (β d κ R : ℝ) (n : ℕ)
    (e : Fin n × Fin n) :
    Measurable (fun C : CostArray =>
      if e ∈ retainedEdges d κ R n C then Real.exp (-β * edgeLength d κ n C e) else 0) := by
  have hl : Measurable (fun C : CostArray => edgeLength d κ n C e) := by
    unfold edgeLength
    fun_prop
  simp only [retainedEdges, mem_filter, Finset.mem_univ, true_and]
  exact Measurable.ite (measurableSet_le hl measurable_const)
    (Real.measurable_exp.comp (hl.const_mul (-β))) measurable_const

theorem measurable_cutoff_assignment_partition (β d κ R : ℝ) (n : ℕ)
    (vertices : Finset (Fin n ⊕ Fin n)) :
    Measurable (fun p : CostArray × ℝ => Tree.monomerPartition Tree.Bipartite.ends
      vertices (retainedEdges d κ R n p.1) (fun e => Real.exp (-β * edgeLength d κ n p.1 e))
      (Real.exp p.2)) := by
  classical
  have heq : (fun p : CostArray × ℝ => Tree.monomerPartition Tree.Bipartite.ends
      vertices (retainedEdges d κ R n p.1) (fun e => Real.exp (-β * edgeLength d κ n p.1 e))
      (Real.exp p.2)) =
      fun p => Tree.monomerPartition Tree.Bipartite.ends vertices Finset.univ
        (fun e => if e ∈ retainedEdges d κ R n p.1 then Real.exp (-β * edgeLength d κ n p.1 e) else 0)
        (Real.exp p.2) :=
    funext fun _ => Tree.monomerPartition_masked_weights _ _ (Finset.subset_univ _) _ _
  rw [heq]
  unfold Tree.monomerPartition
  refine Finset.measurable_fun_sum _ fun M _ => ?_
  exact ((Real.measurable_exp.comp measurable_snd).pow_const _).mul
    (Finset.measurable_fun_prod _ fun e _ =>
      (measurable_masked_assignment_weight β d κ R n e).comp measurable_fst)

theorem measurable_cutoffAssignment_deficit (β d κ R : ℝ) (n : ℕ) :
    Measurable (fun p : CostArray × ℝ => (cutoffAssignmentGraph β d κ R n p.1).deficit p.2) := by
  let V := Fin n ⊕ Fin n
  let Z (s : Finset V) (p : CostArray × ℝ) :=
    Tree.monomerPartition Tree.Bipartite.ends s (retainedEdges d κ R n p.1)
      (fun e => Real.exp (-β * edgeLength d κ n p.1 e)) (Real.exp p.2)
  change Measurable (fun p : CostArray × ℝ => ((univ : Finset V).card : ℝ) -
    ∑ v : V, Real.exp p.2 * (Z (univ.erase v) p / Z univ p))
  apply measurable_const.sub
  refine Finset.measurable_fun_sum _ fun v _ => ?_
  exact (Real.measurable_exp.comp measurable_snd).mul
    ((measurable_cutoff_assignment_partition β d κ R n _).div
      (measurable_cutoff_assignment_partition β d κ R n _))

private theorem integrable_cutoffAssignment_weight {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {β d κ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hμ : SmallCostTail μ κ d) (R : ℝ) (n : ℕ) :
    Integrable (fun C => ∑ e ∈ (cutoffAssignmentGraph β d κ R n C).edges,
      (cutoffAssignmentGraph β d κ R n C).weight e) (iidCosts μ) := by
  refine (integrable_assignment_total_weight hμ.1 hβ.le hκ.le d n).mono' ?_ ?_
  · apply Measurable.aestronglyMeasurable
    change Measurable (fun C => ∑ e ∈ retainedEdges d κ R n C,
      Real.exp (-β * edgeLength d κ n C e))
    simp_rw [retainedEdges, Finset.sum_filter]
    refine Finset.measurable_fun_sum _ fun e _ => ?_
    simpa only [retainedEdges, mem_filter, Finset.mem_univ, true_and] using
      measurable_masked_assignment_weight β d κ R n e
  · filter_upwards with C
    let G := cutoffAssignmentGraph β d κ R n C
    rw [Real.norm_of_nonneg (Finset.sum_nonneg fun e _ => G.weight_nonneg e)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun e _ _ => G.weight_nonneg e)

/-- At each cutoff the local deficit profile determines the finite pressure limit. -/
theorem tendsto_expected_cutoffAssignmentPressure_of_local {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {β d κ : ℝ} (hβ : 0 < β) (hd : 0 < d) (hκ : 0 < κ) (hμ : SmallCostTail μ κ d)
    (R t : ℝ) (m : ℝ → ℝ)
    (hlocal : ∀ᵐ s ∂volume.restrict (Ioi t),
      Tendsto (fun n => ∫ C, (cutoffAssignmentGraph β d κ R n C).deficit s / n ∂iidCosts μ)
        atTop (𝓝 (2 * (1 - m s)))) :
    Tendsto (fun n => ∫ C, cutoffAssignmentPressure β d κ R t n C ∂iidCosts μ) atTop
      (𝓝 (2 * t + 2 * ∫ s in Ioi t, (1 - m s))) := by
  let : IsProbabilityMeasure (iidCosts μ) := by unfold iidCosts; infer_instance
  obtain ⟨A, hA⟩ := expected_assignment_total_weight_le hβ hd hκ hμ
  have hcard (n : ℕ) (C : CostArray) :
      ((cutoffAssignmentGraph β d κ R (n+1) C).vertices.card : ℝ) = 2 * ((n+1 : ℕ) : ℝ) := by
    simp [cutoffAssignmentGraph, WeightedGraph.retain, assignmentGraph]
    ring
  have hweight (n : ℕ) (hn : 0 < n) :
      (∫ C, ∑ e ∈ (cutoffAssignmentGraph β d κ R n C).edges,
        (cutoffAssignmentGraph β d κ R n C).weight e ∂iidCosts μ) ≤ A * n := by
    refine (integral_mono_ae (integrable_cutoffAssignment_weight hβ hκ hμ R n)
      (integrable_assignment_total_weight hμ.1 hβ.le hκ.le d n) ?_).trans (hA n hn)
    filter_upwards with C
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun e _ _ => Real.exp_nonneg _)
  have hshift := tendsto_expected_pressure_from_local_monomers
    (μ := iidCosts μ) (fun n C => cutoffAssignmentGraph β d κ R (n+1) C)
    (fun n => ((n+1 : ℕ) : ℝ)) (fun n => Nat.cast_pos.mpr (Nat.succ_pos n)) hcard
    (fun n => integrable_cutoffAssignment_weight hβ hκ hμ R (n+1))
    (C := A) (fun n => hweight (n+1) (Nat.succ_pos n))
    (fun n => measurable_cutoffAssignment_deficit β d κ R (n+1)) t m
    (hlocal.mono fun _ h => h.comp (tendsto_add_atTop_nat 1))
  exact (tendsto_add_atTop_iff_nat 1).mp hshift

private theorem integrable_normalizedPressure {Ω V E : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (G : Ω → WeightedGraph V E)
    {n : ℕ} (hn : 0 < n) (t : ℝ)
    (hcard : ∀ ω, ((G ω).vertices.card : ℝ) = 2 * n)
    (hmeas : Measurable (fun ω => (G ω).Z t))
    (hweight : Integrable (fun ω => ∑ e ∈ (G ω).edges, (G ω).weight e) μ) :
    Integrable (fun ω => Real.log ((G ω).Z t) / n) μ := by
  let W (ω : Ω) := ∑ e ∈ (G ω).edges, (G ω).weight e
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  refine ((integrable_const ‖2*t‖).add (hweight.mul_const (Real.exp (-2*t) / n))).mono'
    (hmeas.log.div_const _).aestronglyMeasurable ?_
  filter_upwards with ω
  have heq : Real.log ((G ω).Z t) / n = 2 * t + (G ω).logCorrected t / n := by
    rw [WeightedGraph.logCorrected, hcard]
    field_simp [hn'.ne']
    ring
  rw [heq]
  have hb := (G ω).logCorrected_bound t
  have hnorm : ‖(G ω).logCorrected t / n‖ ≤ W ω * (Real.exp (-2*t) / n) := by
    rw [Real.norm_of_nonneg (div_nonneg hb.1 hn'.le), ← mul_div_assoc]
    exact div_le_div_of_nonneg_right hb.2 hn'.le
  exact (norm_add_le _ _).trans (add_le_add le_rfl hnorm)

private theorem integrable_cutoffAssignmentPressure {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {β d κ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hμ : SmallCostTail μ κ d) (R t : ℝ) {n : ℕ}
    (hn : 0 < n) :
    Integrable (cutoffAssignmentPressure β d κ R t n) (iidCosts μ) := by
  let : IsProbabilityMeasure (iidCosts μ) := by unfold iidCosts; infer_instance
  refine integrable_normalizedPressure (cutoffAssignmentGraph β d κ R n) hn t ?_ ?_
    (integrable_cutoffAssignment_weight hβ hκ hμ R n)
  · intro C
    simp [cutoffAssignmentGraph, WeightedGraph.retain, assignmentGraph]
    ring
  · let Z (C : CostArray) (s : ℝ) := Tree.monomerPartition Tree.Bipartite.ends univ
      (retainedEdges d κ R n C) (fun e => Real.exp (-β * edgeLength d κ n C e)) (Real.exp s)
    have h : Measurable (Function.uncurry Z) := measurable_cutoff_assignment_partition β d κ R n univ
    change Measurable (fun C => Z C t)
    exact h.of_uncurry_right (y := t)

private theorem integrable_softAssignmentPressure {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {β d κ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hμ : SmallCostTail μ κ d) (t : ℝ) {n : ℕ}
    (hn : 0 < n) :
    Integrable (softAssignmentPressure β d κ t n) (iidCosts μ) := by
  let : IsProbabilityMeasure (iidCosts μ) := by unfold iidCosts; infer_instance
  refine integrable_normalizedPressure (assignmentGraph β d κ n) hn t ?_ ?_
    (integrable_assignment_total_weight hμ.1 hβ.le hκ.le d n)
  · intro C
    simp [assignmentGraph]
    ring
  · let Z (C : CostArray) (s : ℝ) := Tree.monomerPartition Tree.Bipartite.ends univ univ
      (fun e => (assignmentGraph β d κ n C).weight e) (Real.exp s)
    have h : Measurable (Function.uncurry Z) := measurable_assignment_Z β d κ n univ
    change Measurable (fun C => Z C t)
    exact h.of_uncurry_right (y := t)

theorem integrable_gamma_tail {β d : ℝ} (hβ : 0 < β) (hd : 0 < d) {R : ℝ}
    (hR : 0 ≤ R) :
    IntegrableOn (fun x : ℝ => β * x ^ d * Real.exp (-β * x)) (Ioi R) := by
  have hi := integrableOn_rpow_mul_exp_neg_mul_rpow
    (show (-1 : ℝ) < d by linarith) zero_lt_one hβ
  have hj : IntegrableOn (fun x : ℝ => β * x ^ d * Real.exp (-β * x)) (Ioi 0) := by
    change Integrable (fun x : ℝ => β * x ^ d * Real.exp (-β * x)) (volume.restrict (Ioi 0))
    simpa only [Real.rpow_one, neg_mul, mul_assoc] using hi.const_mul β
  exact hj.mono_set (Ioi_subset_Ioi hR)

/-- The uniform expected omitted-weight estimate transfers cutoff pressure limits
to the original expected pressure on the same iid array. -/
theorem tendsto_expected_softAssignmentPressure_of_cutoff_limits
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {β d κ : ℝ}
    (hβ : 0 < β) (hd : 0 < d) (hκ : 0 < κ) (hμ : SmallCostTail μ κ d)
    {t L : ℝ} {Lcut : ℕ → ℝ}
    (hcut : ∀ R : ℕ, Tendsto (fun n => ∫ C, cutoffAssignmentPressure β d κ R t n C ∂iidCosts μ)
      atTop (𝓝 (Lcut R)))
    (hlim : Tendsto Lcut atTop (𝓝 L)) :
    Tendsto (fun n => ∫ C, softAssignmentPressure β d κ t n C ∂iidCosts μ) atTop (𝓝 L) := by
  obtain ⟨K, hK, hgap⟩ := lintegral_cutoffPressureGap_le hκ hd hβ hμ
  let g (x : ℝ) := β * x ^ d * Real.exp (-β * x)
  let err (R : ℕ) := (K * Real.exp (-2*t)) * ∫ x in Ioi (R : ℝ), g x
  refine tendsto_of_uniform_pressure_cutoff hcut hlim (error := err) ?_ (fun R => ?_)
  · have ht := tendsto_integral_Ioi_zero (μ := volume) (f := g) tendsto_natCast_atTop_atTop
    simpa only [mul_zero] using ht.const_mul (K * Real.exp (-2*t))
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hi := integrable_softAssignmentPressure hβ hκ hμ t hn
    have hj := integrable_cutoffAssignmentPressure hβ hκ hμ R t hn
    have hdiff : ∀ᵐ C ∂iidCosts μ,
        0 ≤ softAssignmentPressure β d κ t n C - cutoffAssignmentPressure β d κ R t n C :=
      Eventually.of_forall fun C => cutoffPressureGap_nonneg β d κ R t hn C
    have hpos := integral_nonneg_of_ae hdiff
    rw [← integral_sub hi hj, abs_of_nonneg hpos]
    have hR : 0 ≤ (R : ℝ) := Nat.cast_nonneg _
    have hg : ∀ᵐ x ∂volume.restrict (Ioi (R : ℝ)), 0 ≤ g x := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact mul_nonneg (mul_nonneg hβ.le (Real.rpow_nonneg (hR.trans hx.le) _)) (Real.exp_nonneg _)
    have h := hgap n hn R hR t
    change (∫⁻ C, ENNReal.ofReal (softAssignmentPressure β d κ t n C -
      cutoffAssignmentPressure β d κ R t n C) ∂iidCosts μ) ≤ _ at h
    have hisub : Integrable (fun C => softAssignmentPressure β d κ t n C -
      cutoffAssignmentPressure β d κ R t n C) (iidCosts μ) := hi.sub hj
    rw [← ofReal_integral_eq_lintegral_ofReal hisub hdiff,
      ← ofReal_integral_eq_lintegral_ofReal (integrable_gamma_tail hβ hd hR) hg,
      ← ENNReal.ofReal_mul (by positivity)] at h
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by positivity) (integral_nonneg_of_ae hg))).mp h

end Certificate

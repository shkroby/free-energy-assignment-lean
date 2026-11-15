import Certificate.Arrivals
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-! From the uniform edge-statistic bound to quenched overlap concentration. -/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

namespace Certificate

instance (n : ℕ) : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤
instance (n : ℕ) : DiscreteMeasurableSpace (Equiv.Perm (Fin n)) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- Unnormalized Gibbs weight of a perfect assignment. -/
noncomputable def gibbsAssignmentWeight (β d κ : ℝ) (n : ℕ) (C : CostArray)
    (σ : Equiv.Perm (Fin n)) : ℝ :=
  ∏ i, Real.exp (-(β * lengthScale d κ n * C (i.val, (σ i).val)))

theorem gibbsAssignmentWeight_nonneg (β d κ : ℝ) (n : ℕ) (C : CostArray)
    (σ : Equiv.Perm (Fin n)) : 0 ≤ gibbsAssignmentWeight β d κ n C σ :=
  Finset.prod_nonneg fun _ _ => Real.exp_nonneg _

theorem sum_gibbsAssignmentWeight (β d κ : ℝ) (n : ℕ) (C : CostArray) :
    ∑ σ, gibbsAssignmentWeight β d κ n C σ = assignmentPartition β d κ n C := rfl

/-- The Gibbs mass function normalized by the actual assignment permanent. -/
noncomputable def gibbsAssignmentPMF (β d κ : ℝ) (n : ℕ) (C : CostArray) :
    PMF (Equiv.Perm (Fin n)) :=
  PMF.ofFintype
    (fun σ => ENNReal.ofReal (gibbsAssignmentWeight β d κ n C σ / assignmentPartition β d κ n C))
    (by
      have hZ := assignmentPartition_pos β d κ n C
      rw [← ENNReal.ofReal_sum_of_nonneg
        (fun σ _ => div_nonneg (gibbsAssignmentWeight_nonneg β d κ n C σ) hZ.le),
        ← Finset.sum_div, sum_gibbsAssignmentWeight, div_self hZ.ne', ENNReal.ofReal_one])

/-- Gibbs probability measure of a single assignment at fixed costs. -/
noncomputable def gibbsAssignment (β d κ : ℝ) (n : ℕ) (C : CostArray) :
    Measure (Equiv.Perm (Fin n)) :=
  (gibbsAssignmentPMF β d κ n C).toMeasure

instance gibbsAssignment_isProbabilityMeasure (β d κ : ℝ) (n : ℕ) (C : CostArray) :
    IsProbabilityMeasure (gibbsAssignment β d κ n C) := by
  unfold gibbsAssignment
  infer_instance

theorem gibbsAssignment_singleton (β d κ : ℝ) (n : ℕ) (C : CostArray)
    (σ : Equiv.Perm (Fin n)) :
    gibbsAssignment β d κ n C {σ} =
      ENNReal.ofReal (gibbsAssignmentWeight β d κ n C σ / assignmentPartition β d κ n C) := by
  rw [gibbsAssignment, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  rfl

/-- Two independent Gibbs assignments in a fixed cost array. -/
noncomputable def gibbsAssignmentPair (β d κ : ℝ) (n : ℕ) (C : CostArray) :
    Measure (Equiv.Perm (Fin n) × Equiv.Perm (Fin n)) :=
  (gibbsAssignment β d κ n C).prod (gibbsAssignment β d κ n C)

instance gibbsAssignmentPair_isProbabilityMeasure (β d κ : ℝ) (n : ℕ) (C : CostArray) :
    IsProbabilityMeasure (gibbsAssignmentPair β d κ n C) := by
  unfold gibbsAssignmentPair
  infer_instance

/-- A quenched sample pair for each positive matrix size, indexed from zero. -/
abbrev GibbsPairSample := (n : ℕ) → Equiv.Perm (Fin (n+1)) × Equiv.Perm (Fin (n+1))

/-- The product of the independent quenched pair laws over positive sizes. -/
noncomputable def gibbsPairSequence (β d κ : ℝ) (C : CostArray) : Measure GibbsPairSample :=
  Measure.infinitePi (fun n : ℕ => gibbsAssignmentPair β d κ (n+1) C)

instance gibbsPairSequence_isProbabilityMeasure (β d κ : ℝ) (C : CostArray) :
    IsProbabilityMeasure (gibbsPairSequence β d κ C) := by
  unfold gibbsPairSequence
  infer_instance

theorem gibbsPairSequence_map_eval (β d κ : ℝ) (C : CostArray) (n : ℕ) :
    (gibbsPairSequence β d κ C).map (fun ω : GibbsPairSample => ω n) =
      gibbsAssignmentPair β d κ (n+1) C :=
  Measure.infinitePi_map_eval _ _

/-- Indicator of a row-column edge in the permutation assignment. -/
def assignmentEdgeIndicator {n : ℕ} (σ : Equiv.Perm (Fin n)) (e : Fin n × Fin n) : ℝ :=
  if σ e.1 = e.2 then 1 else 0

theorem abs_assignmentEdgeIndicator_le_one {n : ℕ} (σ : Equiv.Perm (Fin n))
    (e : Fin n × Fin n) : |assignmentEdgeIndicator σ e| ≤ 1 := by
  unfold assignmentEdgeIndicator
  split <;> norm_num

/-- The shared edges divided by the matrix size. -/
noncomputable def assignmentOverlap {n : ℕ} (σ τ : Equiv.Perm (Fin n)) : ℝ :=
  ((Finset.univ.filter (fun e : Fin n × Fin n => σ e.1 = e.2 ∧ τ e.1 = e.2)).card : ℝ) / n

/-- Edge statistic with deterministic coefficients `f` centered at `γ`. -/
noncomputable def centeredAssignmentStatistic {n : ℕ}
    (f γ : Fin n × Fin n → ℝ) (σ : Equiv.Perm (Fin n)) : ℝ :=
  ∑ e, f e * (assignmentEdgeIndicator σ e - γ e)

private theorem sum_indicators_eq_shared_edges {n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    ∑ e, assignmentEdgeIndicator σ e * assignmentEdgeIndicator τ e =
      ((Finset.univ.filter (fun e : Fin n × Fin n => σ e.1 = e.2 ∧ τ e.1 = e.2)).card : ℝ) := by
  rw [show ((Finset.univ.filter (fun e : Fin n × Fin n => σ e.1 = e.2 ∧ τ e.1 = e.2)).card : ℝ) =
    ∑ e ∈ Finset.univ.filter (fun e : Fin n × Fin n => σ e.1 = e.2 ∧ τ e.1 = e.2), (1 : ℝ) from by simp,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hs : σ e.1 = e.2 <;> by_cases ht : τ e.1 = e.2 <;>
    simp [assignmentEdgeIndicator, hs, ht]

/-- The algebraic identity behind the two successive Gibbs tests. -/
theorem assignmentOverlap_centered_identity {n : ℕ} (hn : 0 < n)
    (σ τ : Equiv.Perm (Fin n)) (γ : Fin n × Fin n → ℝ) :
    (n : ℝ) * assignmentOverlap σ τ - ∑ e, (γ e)^2 =
      centeredAssignmentStatistic γ γ σ +
        centeredAssignmentStatistic (assignmentEdgeIndicator σ) γ τ := by
  have hn₀ : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [assignmentOverlap, mul_div_cancel₀ _ hn₀, ← sum_indicators_eq_shared_edges,
    centeredAssignmentStatistic, centeredAssignmentStatistic,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  ring

/-- The square bias and the uniform Gibbs tail at one cost array and size. -/
def EdgeStatisticBoundAt (β d κ Q δ c : ℝ) {n : ℕ}
    (γ : Fin n × Fin n → ℝ) (C : CostArray) : Prop :=
  |(∑ e, (γ e)^2) / (n : ℝ) - Q| < δ ∧
    ∀ f : Fin n × Fin n → ℝ, (∀ e, |f e| ≤ 1) →
      gibbsAssignment β d κ n C
          {σ | (n : ℝ) * δ < |centeredAssignmentStatistic f γ σ|} ≤
        ENNReal.ofReal (2 * Real.exp (-c * (n : ℝ)))

/-- The manuscript's uniform edge-statistic hypothesis, with deterministic
rate and cost-measurable, unit-interval centers for each positive tolerance. -/
def UniformEdgeStatisticBound (μ : Measure ℝ) (β d κ Q : ℝ) : Prop :=
  ∀ δ > 0, ∃ c > 0, ∃ γ : (n : ℕ) → CostArray → (Fin n × Fin n) → ℝ,
    (∀ n e, Measurable (fun C => γ n C e)) ∧
    (∀ n C e, γ n C e ∈ Icc 0 1) ∧
    (∀ᵐ C ∂iidCosts μ, ∀ᶠ n : ℕ in atTop, EdgeStatisticBoundAt β d κ Q δ c (γ n C) C)

/-- Conditional on one of the assignments, its edge indicators are admissible
coefficients for the second assignment. -/
theorem gibbsAssignmentPair_overlap_bound_of_edgeStatistic {β d κ Q δ c : ℝ}
    {n : ℕ} (hn : 0 < n) {C : CostArray} {γ : Fin n × Fin n → ℝ}
    (hγ : ∀ e, γ e ∈ Icc 0 1) (h : EdgeStatisticBoundAt β d κ Q δ c γ C) :
    gibbsAssignmentPair β d κ n C
        {p | 3 * δ < |assignmentOverlap p.1 p.2 - Q|} ≤
      ENNReal.ofReal (4 * Real.exp (-c * (n : ℝ))) := by
  let P := gibbsAssignment β d κ n C
  let t := 2 * Real.exp (-c * (n : ℝ))
  let A : Set (Equiv.Perm (Fin n)) := {σ | (n : ℝ) * δ < |centeredAssignmentStatistic γ γ σ|}
  let B : Set (Equiv.Perm (Fin n) × Equiv.Perm (Fin n)) :=
    {p | (n : ℝ) * δ < |centeredAssignmentStatistic (assignmentEdgeIndicator p.1) γ p.2|}
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hA : P.prod P (A ×ˢ univ) ≤ ENNReal.ofReal t := by
    rw [Measure.prod_prod, measure_univ, mul_one]
    exact h.2 γ (fun e => by rw [abs_of_nonneg (hγ e).1]; exact (hγ e).2)
  have hB : P.prod P B ≤ ENNReal.ofReal t := by
    rw [Measure.prod_apply MeasurableSet.of_discrete]
    calc
      _ ≤ ∫⁻ _ : Equiv.Perm (Fin n), ENNReal.ofReal t ∂P := by
        apply lintegral_mono
        intro σ
        exact h.2 (assignmentEdgeIndicator σ) (abs_assignmentEdgeIndicator_le_one σ)
      _ = _ := by simp
  have hsub : {p : Equiv.Perm (Fin n) × Equiv.Perm (Fin n) |
      3 * δ < |assignmentOverlap p.1 p.2 - Q|} ⊆ (A ×ˢ univ) ∪ B := by
    rintro ⟨σ,τ⟩ hp
    by_cases hs : σ ∈ A
    · exact Or.inl ⟨hs, mem_univ _⟩
    by_cases hst : (σ, τ) ∈ B
    · exact Or.inr hst
    have h1 : |centeredAssignmentStatistic γ γ σ| ≤ (n : ℝ) * δ := le_of_not_gt hs
    have h2 : |centeredAssignmentStatistic (assignmentEdgeIndicator σ) γ τ| ≤ (n : ℝ) * δ :=
      le_of_not_gt hst
    have hc : (n : ℝ) * ((∑ e, (γ e)^2) / (n : ℝ)) = ∑ e, (γ e)^2 :=
      mul_div_cancel₀ _ hn'.ne'
    have he : (n : ℝ) * (assignmentOverlap σ τ - Q) =
        centeredAssignmentStatistic γ γ σ +
          centeredAssignmentStatistic (assignmentEdgeIndicator σ) γ τ +
          (n : ℝ) * ((∑ e, (γ e)^2) / (n : ℝ) - Q) := by
      rw [← assignmentOverlap_centered_identity hn σ τ γ, mul_sub _ ((∑ e, (γ e)^2) /
        (n : ℝ)), hc]
      ring
    have h3 : (n : ℝ) * |(∑ e, (γ e)^2) / (n : ℝ) - Q| ≤ (n : ℝ) * δ :=
      mul_le_mul_of_nonneg_left h.1.le hn'.le
    have htot : (n : ℝ) * |assignmentOverlap σ τ - Q| ≤ (n : ℝ) * (3*δ) := by
      calc
        _ = |(n : ℝ) * (assignmentOverlap σ τ - Q)| := by
          rw [abs_mul, abs_of_nonneg hn'.le]
        _ = |centeredAssignmentStatistic γ γ σ +
            centeredAssignmentStatistic (assignmentEdgeIndicator σ) γ τ +
            (n : ℝ) * ((∑ e, (γ e)^2) / (n : ℝ) - Q)| := congrArg abs he
        _ ≤ |centeredAssignmentStatistic γ γ σ| +
            |centeredAssignmentStatistic (assignmentEdgeIndicator σ) γ τ| +
            |(n : ℝ) * ((∑ e, (γ e)^2) / (n : ℝ) - Q)| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
        _ ≤ _ := by
          rw [abs_mul, abs_of_nonneg hn'.le]
          linarith only [h1,h2,h3]
    exact ((not_lt_of_ge (le_of_mul_le_mul_left htot hn')) hp).elim
  change P.prod P _ ≤ _
  calc
    _ ≤ P.prod P ((A ×ˢ univ) ∪ B) := measure_mono hsub
    _ ≤ P.prod P (A ×ˢ univ) + P.prod P B := measure_union_le _ _
    _ ≤ ENNReal.ofReal t + ENNReal.ofReal t := add_le_add hA hB
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity : 0 ≤ t) (by positivity : 0 ≤ t)]
      congr 1
      dsimp [t]
      ring

/-- Exponential quenched tails for the pair overlap of the two Gibbs samples. -/
theorem quenched_overlap_concentration_of_uniformEdgeStatisticBound
    {μ : Measure ℝ} {β d κ Q : ℝ} (h : UniformEdgeStatisticBound μ β d κ Q) :
    ∀ ε > 0, ∃ c > 0, ∀ᵐ C ∂iidCosts μ, ∀ᶠ n : ℕ in atTop,
      gibbsAssignmentPair β d κ n C {p | ε < |assignmentOverlap p.1 p.2 - Q|} ≤
        ENNReal.ofReal (4 * Real.exp (-c * (n : ℝ))) := by
  intro ε hε
  obtain ⟨c, hc, γ, _, hγ, htail⟩ := h (ε / 3) (by positivity)
  refine ⟨c, hc, ?_⟩
  filter_upwards [htail] with C hC
  filter_upwards [hC, eventually_gt_atTop (0 : ℕ)] with n hn hn₀
  have hb := gibbsAssignmentPair_overlap_bound_of_edgeStatistic hn₀ (hγ n C) hn
  rwa [show 3 * (ε / 3) = ε by ring] at hb

private theorem tsum_measure_ne_top_of_eventually_le_summable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (A : ℕ → Set Ω) {q : ℕ → ℝ}
    (hq : ∀ n, 0 ≤ q n) (hs : Summable q)
    (h : ∀ᶠ n : ℕ in atTop, P (A n) ≤ ENNReal.ofReal (q n)) :
    (∑' n, P (A n)) ≠ ∞ := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  have hs' : Summable (fun n : ℕ => q (n+N)) := (summable_nat_add_iff N).mpr hs
  have htail : Summable (fun n : ℕ => (P (A (n+N))).toReal) := by
    apply Summable.of_nonneg_of_le (fun _ => ENNReal.toReal_nonneg) _ hs'
    intro n
    have hu := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hN (n+N) (Nat.le_add_left N n))
    rwa [ENNReal.toReal_ofReal (hq (n+N))] at hu
  have hfull : Summable (fun n : ℕ => (P (A n)).toReal) := (summable_nat_add_iff N).mp htail
  simpa only [ENNReal.ofReal_toReal (measure_ne_top P _)] using hfull.tsum_ofReal_ne_top

private theorem tsum_measure_ne_top_of_eventually_le_exp {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (A : ℕ → Set Ω) {c : ℝ} (hc : 0 < c)
    (h : ∀ᶠ n : ℕ in atTop, P (A n) ≤
      ENNReal.ofReal (4 * Real.exp (-c * ((n+1 : ℕ) : ℝ)))) :
    (∑' n, P (A n)) ≠ ∞ := by
  have hbase : Summable (fun n : ℕ => 4 * Real.exp (-c * (n : ℝ))) := by
    simpa only [Real.rpow_one, neg_mul] using
      (summable_nat_stretchedExp hc (zero_lt_one : (0 : ℝ) < 1)).mul_left (4 : ℝ)
  exact tsum_measure_ne_top_of_eventually_le_summable P A (fun _ => by positivity)
    ((summable_nat_add_iff 1).mpr hbase) h

/-- The geometric quenched tails imply almost-sure overlap convergence on
the infinite product of quenched Gibbs pair laws. -/
theorem ae_tendsto_gibbsPairSequence_overlap_of_quenched_bounds
    {μ : Measure ℝ} {β d κ Q : ℝ}
    (h : ∀ ε > 0, ∃ c > 0, ∀ᵐ C ∂iidCosts μ, ∀ᶠ n : ℕ in atTop,
      gibbsAssignmentPair β d κ n C {p | ε < |assignmentOverlap p.1 p.2 - Q|} ≤
        ENNReal.ofReal (4 * Real.exp (-c * (n : ℝ)))) :
    ∀ᵐ C ∂iidCosts μ, ∀ᵐ ω ∂gibbsPairSequence β d κ C,
      Tendsto (fun n => assignmentOverlap (ω n).1 (ω n).2) atTop (𝓝 Q) := by
  let tol (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)
  have htol (j : ℕ) : 0 < tol j := by dsimp [tol]; positivity
  choose c hc hb using fun j => h (tol j) (htol j)
  filter_upwards [ae_all_iff.mpr hb] with C hC
  let P := gibbsPairSequence β d κ C
  let X (n : ℕ) (ω : GibbsPairSample) := assignmentOverlap (ω n).1 (ω n).2
  have hx (j : ℕ) : ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, |X n ω - Q| ≤ tol j := by
    let A (n : ℕ) : Set GibbsPairSample := {ω | tol j < |X n ω - Q|}
    have hbound : ∀ᶠ n : ℕ in atTop, P (A n) ≤
        ENNReal.ofReal (4 * Real.exp (-c j * ((n+1 : ℕ) : ℝ))) := by
      filter_upwards [(tendsto_add_atTop_nat 1).eventually (hC j)] with n hn
      let B : Set (Equiv.Perm (Fin (n+1)) × Equiv.Perm (Fin (n+1))) :=
        {p | tol j < |assignmentOverlap p.1 p.2 - Q|}
      have hB : MeasurableSet B := MeasurableSet.of_discrete
      change P ((fun ω : GibbsPairSample => ω n) ⁻¹' B) ≤ _
      rw [← Measure.map_apply (measurable_pi_apply n) hB, gibbsPairSequence_map_eval]
      exact hn
    have hborel := ae_eventually_notMem (tsum_measure_ne_top_of_eventually_le_exp P A (hc j) hbound)
    simpa only [A, mem_ofPred_eq, not_lt] using hborel
  filter_upwards [ae_all_iff.mpr hx] with ω hω
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hε
  filter_upwards [hω j] with n hn
  simpa only [Real.dist_eq, X] using hn.trans_lt hj

/-- The endpoint of the quenched overlap corollary, conditional on the
uniform edge-statistic estimate and the cavity target lying in `(0,1)`. -/
theorem quenchedOverlap_of_uniformEdgeStatisticBound
    {μ : Measure ℝ} {β d κ Q : ℝ} (hQ : Q ∈ Ioo 0 1)
    (h : UniformEdgeStatisticBound μ β d κ Q) :
    Q ∈ Ioo 0 1 ∧
      (∀ ε > 0, ∃ c > 0, ∀ᵐ C ∂iidCosts μ, ∀ᶠ n : ℕ in atTop,
        gibbsAssignmentPair β d κ n C {p | ε < |assignmentOverlap p.1 p.2 - Q|} ≤
          ENNReal.ofReal (4 * Real.exp (-c * (n : ℝ)))) ∧
      (∀ᵐ C ∂iidCosts μ, gibbsPairSequence β d κ C
        {ω | Tendsto (fun n => assignmentOverlap (ω n).1 (ω n).2) atTop (𝓝 Q)} = 1) := by
  have ht := quenched_overlap_concentration_of_uniformEdgeStatisticBound h
  refine ⟨hQ, ht, ?_⟩
  filter_upwards [ae_tendsto_gibbsPairSequence_overlap_of_quenched_bounds ht] with C hC
  let E : Set GibbsPairSample := {ω |
    Tendsto (fun n => assignmentOverlap (ω n).1 (ω n).2) atTop (𝓝 Q)}
  have hE : (univ : Set GibbsPairSample) ≤ᵐ[gibbsPairSequence β d κ C] E :=
    hC.mono fun _ hω _ => hω
  exact le_antisymm prob_le_one (by simpa only [measure_univ] using measure_mono_ae hE)

end Certificate

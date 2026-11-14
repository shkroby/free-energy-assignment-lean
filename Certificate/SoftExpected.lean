import Certificate.SoftAssignment
import Certificate.PressurePositive

/-!
# Expected monomer pressure of the scaled iid assignment model

For the actual cost array, the pressure interpolation needs only convergence
of the local monomer probabilities. The CDF hypothesis supplies the averaged
edge-weight bound; finite partition sums supply the required measurability.
-/

open Finset Filter Set MeasureTheory
open scoped BigOperators Topology

namespace Certificate

private theorem measurable_assignment_Z (β d κ : ℝ) (n : ℕ)
    (vertices : Finset (Fin n ⊕ Fin n)) :
    Measurable (fun p : CostArray × ℝ => Tree.monomerPartition Tree.Bipartite.ends
      vertices (univ : Finset (Fin n × Fin n))
      (fun e => (assignmentGraph β d κ n p.1).weight e) (Real.exp p.2)) := by
  unfold Tree.monomerPartition assignmentGraph edgeLength
  fun_prop

theorem measurable_assignment_deficit (β d κ : ℝ) (n : ℕ) :
    Measurable (fun p : CostArray × ℝ => (assignmentGraph β d κ n p.1).deficit p.2) := by
  let V := Fin n ⊕ Fin n
  let E := Fin n × Fin n
  let Z (s : Finset V) (p : CostArray × ℝ) :=
    Tree.monomerPartition Tree.Bipartite.ends s (univ : Finset E)
      (fun e => (assignmentGraph β d κ n p.1).weight e) (Real.exp p.2)
  change Measurable (fun p : CostArray × ℝ => ((univ : Finset V).card : ℝ) -
    ∑ v : V, Real.exp p.2 * (Z (univ.erase v) p / Z univ p))
  apply measurable_const.sub
  refine Finset.measurable_fun_sum _ fun v _ => ?_
  exact (Real.measurable_exp.comp measurable_snd).mul
    ((measurable_assignment_Z β d κ n _).div (measurable_assignment_Z β d κ n _))

private theorem integrable_assignment_edge {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : μ (Iio 0) = 0) {β κ : ℝ} (hβ : 0 ≤ β) (hκ : 0 ≤ κ) (d : ℝ)
    (n : ℕ) (e : Fin n × Fin n) :
    Integrable (fun C => (assignmentGraph β d κ n C).weight e) (iidCosts μ) := by
  let : IsProbabilityMeasure (iidCosts μ) := by unfold iidCosts; infer_instance
  have hm : Measurable (fun C => (assignmentGraph β d κ n C).weight e) := by
    unfold assignmentGraph edgeLength
    fun_prop
  apply Integrable.of_mem_Icc 0 1 hm.aemeasurable
  filter_upwards [ae_cost_nonneg μ hμ] with C hC
  change Real.exp (-β * edgeLength d κ n C e) ∈ Icc (0 : ℝ) 1
  have hs : 0 ≤ lengthScale d κ n := by unfold lengthScale; positivity
  exact ⟨Real.exp_nonneg _, Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hβ)
      (mul_nonneg hs (hC (e.1.val, e.2.val))))⟩

theorem integrable_assignment_total_weight {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : μ (Iio 0) = 0) {β κ : ℝ} (hβ : 0 ≤ β) (hκ : 0 ≤ κ) (d : ℝ) (n : ℕ) :
    Integrable (fun C => ∑ e ∈ (assignmentGraph β d κ n C).edges,
      (assignmentGraph β d κ n C).weight e) (iidCosts μ) := by
  change Integrable (fun C => ∑ e : Fin n × Fin n, (assignmentGraph β d κ n C).weight e) (iidCosts μ)
  exact integrable_finsetSum _ (fun e _ => integrable_assignment_edge hμ hβ hκ d n e)

private theorem expected_assignment_total_weight_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {β d κ : ℝ} (hβ : 0 < β) (hd : 0 < d) (hκ : 0 < κ) (hμ : SmallCostTail μ κ d) :
    ∃ A : ℝ, ∀ n : ℕ, 0 < n →
      (∫ C, ∑ e ∈ (assignmentGraph β d κ n C).edges, (assignmentGraph β d κ n C).weight e
        ∂iidCosts μ) ≤ A * n := by
  obtain ⟨A, _, hA⟩ := integral_edgeWeight_le_div_size hβ hd hκ hμ
  refine ⟨A, fun n hn => ?_⟩
  let X : ℝ → ℝ := fun c => Real.exp (-β * (lengthScale d κ n * c))
  have hX : Measurable X := by unfold X; fun_prop
  have hEdge (e : Fin n × Fin n) :
      (∫ C, (assignmentGraph β d κ n C).weight e ∂iidCosts μ) ≤ A / n := by
    let idx : ℕ × ℕ := (e.1.val,e.2.val)
    have hmap : (iidCosts μ).map (fun C => C idx) = μ :=
      Measure.infinitePi_map_eval (fun _ : ℕ × ℕ => μ) idx
    have h := integral_map (μ := iidCosts μ) (measurable_pi_apply idx).aemeasurable
      hX.aestronglyMeasurable
    rw [hmap] at h
    change (∫ C, X (C idx) ∂iidCosts μ) ≤ A / n
    rw [← h]
    exact hA n hn
  change (∫ C, ∑ e : Fin n × Fin n, (assignmentGraph β d κ n C).weight e ∂iidCosts μ) ≤ _
  rw [integral_finsetSum _ (fun e _ => integrable_assignment_edge hμ.1 hβ.le hκ.le d n e)]
  calc
    _ ≤ ∑ _e : Fin n × Fin n, A / n := Finset.sum_le_sum fun e _ => hEdge e
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_mul]
      field_simp [(show (0 : ℝ) < n from Nat.cast_pos.mpr hn).ne']

/-- For the actual iid array, the expected soft pressure converges whenever
the normalized expected local deficit converges to the designated profile.
The small-cost CDF is the only assumption used for domination. -/
theorem tendsto_expected_softAssignmentPressure_of_local
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {β d κ : ℝ} (hβ : 0 < β) (hd : 0 < d) (hκ : 0 < κ) (hμ : SmallCostTail μ κ d)
    (t : ℝ) (m : ℝ → ℝ)
    (hlocal : ∀ᵐ s ∂volume.restrict (Ioi t),
      Tendsto (fun n : ℕ => ∫ C, (assignmentGraph β d κ n C).deficit s / n ∂iidCosts μ)
        atTop (𝓝 (2 * (1 - m s)))) :
    Tendsto (fun n => ∫ C, softAssignmentPressure β d κ t n C ∂iidCosts μ) atTop
      (𝓝 (2 * t + 2 * ∫ s in Ioi t, (1 - m s))) := by
  let : IsProbabilityMeasure (iidCosts μ) := by unfold iidCosts; infer_instance
  obtain ⟨A, hA⟩ := expected_assignment_total_weight_le hβ hd hκ hμ
  have hcard (n : ℕ) (C : CostArray) :
      ((assignmentGraph β d κ (n + 1) C).vertices.card : ℝ) = 2 * ((n + 1 : ℕ) : ℝ) := by
    simp [assignmentGraph]
    ring
  have hshift := tendsto_expected_pressure_from_local_monomers
    (μ := iidCosts μ) (fun n C => assignmentGraph β d κ (n + 1) C)
    (fun n => ((n + 1 : ℕ) : ℝ)) (fun n => Nat.cast_pos.mpr (Nat.succ_pos n)) hcard
    (fun n => integrable_assignment_total_weight hμ.1 hβ.le hκ.le d (n + 1))
    (C := A) (fun n => hA (n + 1) (Nat.succ_pos n))
    (fun n => measurable_assignment_deficit β d κ (n + 1)) t m
    (hlocal.mono fun _ h => h.comp (tendsto_add_atTop_nat 1))
  apply (tendsto_add_atTop_iff_nat 1).mp
  exact hshift

end Certificate

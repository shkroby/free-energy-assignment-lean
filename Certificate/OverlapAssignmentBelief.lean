import Certificate.OverlapTrim
import Certificate.OverlapBeliefMeasurable
import Certificate.OverlapGibbsTilt

/-! Belief propagation on the actual retained assignment graph. -/

open Finset Filter MeasureTheory Set
open scoped Topology

namespace Certificate.Overlap

open OverlapBelief

theorem card_incident_trimmedAssignment_le (β d κ R : ℝ) (n D : ℕ)
    (C : CostArray) (v : Fin n ⊕ Fin n) :
    (incidentEdges (trimmedAssignmentGraph β d κ R n D C) v).card ≤ D := by
  let S := retainedEdges d κ R n C
  cases v with
  | inl i =>
    have h : incidentEdges (trimmedAssignmentGraph β d κ R n D C) (Sum.inl i) =
        rowEdges (trimDegrees D S) i := by
      ext e
      simp [incidentEdges, trimmedAssignmentGraph, WeightedGraph.retain, assignmentGraph,
        Tree.Bipartite.ends, rowEdges, S, eq_comm]
    rw [h]
    exact rowEdges_trimDegrees_card_le D S i
  | inr j =>
    have h : incidentEdges (trimmedAssignmentGraph β d κ R n D C) (Sum.inr j) =
        colEdges (trimDegrees D S) j := by
      ext e
      simp [incidentEdges, trimmedAssignmentGraph, WeightedGraph.retain, assignmentGraph,
        Tree.Bipartite.ends, colEdges, S, eq_comm]
    rw [h]
    exact colEdges_trimDegrees_card_le D S j

private theorem trimmedAssignment_weight_bounds {β d κ R : ℝ} {n D : ℕ}
    (hβ : 0 ≤ β) (hκ : 0 ≤ κ) {C : CostArray} (hC : ∀ p, 0 ≤ C p) (e : Fin n × Fin n) :
    let w := (trimmedAssignmentGraph β d κ R n D C).weight e
    0 < w ∧ w ≤ 1 := by
  change 0 < Real.exp (-β * (lengthScale d κ n * C (e.1.val,e.2.val))) ∧
    Real.exp (-β * (lengthScale d κ n * C (e.1.val,e.2.val))) ≤ 1
  refine ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr ?_⟩
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hβ)
    (mul_nonneg (Real.rpow_nonneg (mul_nonneg hκ (Nat.cast_nonneg n)) _) (hC _))

/-- A common deterministic bound for untilted and exponentially tilted
retained graphs, valid whenever the input costs are nonnegative. -/
theorem trimmedAssignment_incidentWeightBound {β d κ R : ℝ} {n D : ℕ}
    (hβ : 0 ≤ β) (hκ : 0 ≤ κ) {C : CostArray} (hC : ∀ p, 0 ≤ C p) :
    IncidentWeightBound (trimmedAssignmentGraph β d κ R n D C) ((D : ℝ) * Real.exp 1) :=
  incidentWeightBound_of_degree _ (Real.exp_nonneg _) (card_incident_trimmedAssignment_le β d κ R n D C)
    fun e _ => (trimmedAssignment_weight_bounds hβ hκ hC e).2.trans (Real.one_le_exp (by norm_num))

theorem trimmedAssignment_incidentWeightBound_tilt {β d κ R : ℝ} {n D : ℕ}
    (hβ : 0 ≤ β) (hκ : 0 ≤ κ) {C : CostArray} (hC : ∀ p, 0 ≤ C p)
    {t : ℝ} (ht : |t| ≤ 1) {f : Fin n × Fin n → ℝ} (hf : ∀ e, |f e| ≤ 1) :
    IncidentWeightBound (tilt (trimmedAssignmentGraph β d κ R n D C) t f)
      ((D : ℝ) * Real.exp 1) := by
  refine incidentWeightBound_of_degree _ (Real.exp_nonneg _) ?_ ?_
  · exact card_incident_trimmedAssignment_le β d κ R n D C
  · intro e he
    have h := tilt_weight_bounds (trimmedAssignmentGraph β d κ R n D C) ht
      (fun e _ => hf e) (fun e _ => trimmedAssignment_weight_bounds hβ hκ hC e) e he
    simpa only [one_mul] using h.2

private def clampedOverlapCosts (C : CostArray) : CostArray := fun e => max 0 (C e)

private theorem clampedOverlapCosts_eq {C : CostArray} (hC : ∀ p, 0 ≤ C p) :
    clampedOverlapCosts C = C :=
  funext fun e => max_eq_right (hC e)

private theorem measurable_clampedOverlapCosts : Measurable clampedOverlapCosts :=
  measurable_pi_iff.mpr fun e => measurable_const.max (measurable_pi_apply e)

private theorem clampedOverlapCosts_nonneg (C : CostArray) : ∀ p, 0 ≤ clampedOverlapCosts C p :=
  fun p => le_max_left 0 (C p)

private theorem overlapIncidentBound_nonneg (D : ℕ) : 0 ≤ (D : ℝ) * Real.exp 1 := by positivity

/-- The measurable finite-size center, extended to all arrays by clamping
costs below at zero. Clamping agrees with the actual iid law almost surely. -/
noncomputable def trimmedAssignmentCenter (β d κ R z : ℝ) (n D : ℕ)
    (hβ : 0 ≤ β) (hκ : 0 ≤ κ) (hz : 0 < z) (C : CostArray) (e : Fin n × Fin n) : ℝ :=
  occupation (trimmedAssignmentGraph β d κ R n D (clampedOverlapCosts C)) hz
    (overlapIncidentBound_nonneg D)
    (trimmedAssignment_incidentWeightBound hβ hκ (clampedOverlapCosts_nonneg C)) e

set_option maxHeartbeats 700000 in
/-- On nonnegative costs the center is the exact belief-propagation occupation. -/
theorem trimmedAssignmentCenter_eq_occupation (β d κ R z : ℝ) (n D : ℕ)
    (hβ : 0 ≤ β) (hκ : 0 ≤ κ) (hz : 0 < z) (C : CostArray) (hC : ∀ p, 0 ≤ C p)
    (e : Fin n × Fin n) :
    trimmedAssignmentCenter β d κ R z n D hβ hκ hz C e =
      occupation (trimmedAssignmentGraph β d κ R n D C) hz
        (overlapIncidentBound_nonneg D) (trimmedAssignment_incidentWeightBound hβ hκ hC) e := by
  let GoodCosts := {C : CostArray // ∀ p, 0 ≤ C p}
  let f (B : GoodCosts) := occupation (trimmedAssignmentGraph β d κ R n D B.1) hz
    (overlapIncidentBound_nonneg D) (trimmedAssignment_incidentWeightBound hβ hκ B.2) e
  change f ⟨clampedOverlapCosts C, clampedOverlapCosts_nonneg C⟩ = f ⟨C,hC⟩
  exact congrArg f (Subtype.ext (clampedOverlapCosts_eq hC))

theorem trimmedAssignmentCenter_mem (β d κ R z : ℝ) (n D : ℕ)
    (hβ : 0 ≤ β) (hκ : 0 ≤ κ) (hz : 0 < z) (C : CostArray) (e : Fin n × Fin n) :
    trimmedAssignmentCenter β d κ R z n D hβ hκ hz C e ∈ Set.Icc 0 1 := by
  let G := trimmedAssignmentGraph β d κ R n D (clampedOverlapCosts C)
  by_cases he : e ∈ G.edges
  · have ho := occupation_mem_Ioo G hz (overlapIncidentBound_nonneg D)
      (trimmedAssignment_incidentWeightBound hβ hκ (clampedOverlapCosts_nonneg C)) he
      (trimmedAssignment_weight_bounds hβ hκ (clampedOverlapCosts_nonneg C) e).1
    exact ⟨ho.1.le, ho.2.le⟩
  · unfold trimmedAssignmentCenter occupation
    rw [dif_neg he]
    exact ⟨le_rfl, zero_le_one⟩

theorem trimmedAssignmentCenter_eq_zero_off_edges (β d κ R z : ℝ) (n D : ℕ)
    (hβ : 0 ≤ β) (hκ : 0 ≤ κ) (hz : 0 < z) (C : CostArray) (hC : ∀ p, 0 ≤ C p)
    (e : Fin n × Fin n) (he : e ∉ (trimmedAssignmentGraph β d κ R n D C).edges) :
    trimmedAssignmentCenter β d κ R z n D hβ hκ hz C e = 0 := by
  rw [trimmedAssignmentCenter_eq_occupation β d κ R z n D hβ hκ hz C hC e, occupation,
    dif_neg he]

private theorem measurable_retainedEdges (d κ R : ℝ) (n : ℕ) :
    Measurable (retainedEdges d κ R n) := by
  apply measurable_finset_iff.mpr
  intro e
  rw [← measurableSet_setOfPred]
  have hSet : {C : CostArray | e ∈ retainedEdges d κ R n C} =
      {C : CostArray | lengthScale d κ n * C (e.1.val,e.2.val) ≤ R} := by
    ext C
    unfold retainedEdges
    exact Finset.mem_filter.trans (and_iff_right (Finset.mem_univ e))
  rw [hSet]
  exact measurableSet_le (measurable_const.mul (measurable_pi_apply _)) measurable_const

theorem measurable_trimmedEdges (β d κ R : ℝ) (n D : ℕ) :
    Measurable (fun C : CostArray => (trimmedAssignmentGraph β d κ R n D C).edges) :=
  (measurable_of_countable (trimDegrees D)).comp (measurable_retainedEdges d κ R n)

private theorem measurable_trimmedWeight (β d κ R : ℝ) (n D : ℕ) (e : Fin n × Fin n) :
    Measurable (fun C => (trimmedAssignmentGraph β d κ R n D C).weight e) := by
  change Measurable (fun C : CostArray =>
    Real.exp (-β * (lengthScale d κ n * C (e.1.val,e.2.val))))
  exact (measurable_const.mul (measurable_const.mul (measurable_pi_apply _))).exp

/-- Each exact center coordinate is measurable in the iid cost array. -/
theorem measurable_trimmedAssignmentCenter (β d κ R z : ℝ) (n D : ℕ)
    (hβ : 0 ≤ β) (hκ : 0 ≤ κ) (hz : 0 < z) (e : Fin n × Fin n) :
    Measurable (fun C => trimmedAssignmentCenter β d κ R z n D hβ hκ hz C e) := by
  let G (C : CostArray) := trimmedAssignmentGraph β d κ R n D (clampedOverlapCosts C)
  have hEdges : Measurable (fun C : CostArray => (G C).edges) :=
    (measurable_trimmedEdges ..).comp measurable_clampedOverlapCosts
  exact measurable_occupation G (ends := Tree.Bipartite.ends) (fun _ => rfl)
    (fun e => (measurableSet_mem_finset e).preimage hEdges)
    (fun e => (measurable_trimmedWeight ..).comp measurable_clampedOverlapCosts)
    hz (overlapIncidentBound_nonneg D)
    (fun C => trimmedAssignment_incidentWeightBound hβ hκ (clampedOverlapCosts_nonneg C)) e

end Certificate.Overlap

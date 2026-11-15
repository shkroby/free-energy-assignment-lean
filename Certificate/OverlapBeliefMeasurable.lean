import Certificate.OverlapBeliefIterate
import Certificate.OverlapBeliefOccupations
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-! Fixed-point belief messages and occupations are measurable under
measurable edge retention and weights with a fixed endpoint map. -/

open Filter Finset Set
open scoped Topology

namespace Certificate.OverlapBelief

variable {X V E : Type*} [MeasurableSpace X] [DecidableEq V] [DecidableEq E]
variable [Fintype V] [Fintype E]
variable (G : X → WeightedGraph V E) {ends : E → Finset V}
variable (hEnds : ∀ x, (G x).ends = ends)
variable (hEdge : ∀ e, MeasurableSet {x | e ∈ (G x).edges})
variable (hWeight : ∀ e, Measurable (fun x => (G x).weight e))

include hEnds hEdge in
omit [Fintype V] [Fintype E] in
private theorem measurableSet_incomingEdges (q : State V E) (e : E) :
    MeasurableSet {x | e ∈ incomingEdges (G x) q} := by
  rcases q with ⟨v,q⟩
  cases q with
  | none =>
    by_cases hv : v ∈ ends e
    · simpa [incomingEdges, incidentEdges, hEnds, hv] using hEdge e
    · simp [incomingEdges, incidentEdges, hEnds, hv]
  | some j =>
    by_cases h : e ≠ j ∧ v ∈ ends e
    · simpa [incomingEdges, incidentEdges, hEnds, h.1, h.2] using hEdge e
    · have heq : {x | e ∈ incomingEdges (G x) (v,some j)} = (∅ : Set X) := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, incomingEdges,
          mem_erase, incidentEdges, mem_filter, hEnds]
        exact fun ⟨hne,_,hv⟩ => h ⟨hne,hv⟩
      rw [heq]
      exact MeasurableSet.empty

include hEnds hEdge hWeight in
omit [Fintype V] in
/-- Finite-depth BP messages are measurable in the underlying weighted graph. -/
theorem measurable_logIterate {u : ℝ} (hu : 0 < u) (k : ℕ) (q : State V E) :
    Measurable (fun x => logIterate (G x) u k q) := by
  induction k generalizing q with
  | zero => exact measurable_const
  | succ k hk =>
    simp only [logIterate_succ _ hu, logUpdate]
    let child (e : E) : State V E := (Tree.otherEnd ends e q.1, some e)
    have hchild (x : X) (e : E) : incomingState (G x) q.1 e = child e := by
      simp only [incomingState, child, hEnds]
    have hterm (e : E) : Measurable (fun x => (G x).weight e *
        Real.exp (logIterate (G x) u k (child e))) :=
      (hWeight e).mul (hk (child e)).exp
    have hSum (x : X) :
        (∑ e ∈ incomingEdges (G x) q, (G x).weight e *
          Real.exp (logIterate (G x) u k (incomingState (G x) q.1 e))) =
        ∑ e, if e ∈ incomingEdges (G x) q then
          (G x).weight e * Real.exp (logIterate (G x) u k (child e)) else 0 := by
      simp_rw [hchild]
      rw [← Finset.sum_filter]
      congr 1
      ext e
      simp
    simp_rw [hSum]
    exact (measurable_const.add (Finset.measurable_fun_sum _ fun e _ =>
      Measurable.ite (measurableSet_incomingEdges G hEnds hEdge q e) (hterm e) measurable_const)).log.neg

/-- Finite iterates converge to the unique logarithmic fixed point. -/
theorem tendsto_logIterate (H : WeightedGraph V E) {u A : ℝ} (hu : 0 < u) (hA : 0 ≤ A)
    (hBound : IncidentWeightBound H A) :
    Tendsto (fun k => logIterate H u k) atTop (𝓝 (logMessage H hu hA hBound)) := by
  have h (k : ℕ) : logIterate H u k =
      (update H u (-Real.log u))^[k] (fun _ => -Real.log u) := by
    induction k with
    | zero => rfl
    | succ k hk => simp only [logIterate, Function.iterate_succ_apply', ← hk]
  simp_rw [h]
  exact (update_contracting H hu hA hBound).tendsto_iterate_fixedPoint _

include hEnds hEdge hWeight in
theorem measurable_logMessage {u A : ℝ} (hu : 0 < u) (hA : 0 ≤ A)
    (hBound : ∀ x, IncidentWeightBound (G x) A) (q : State V E) :
    Measurable (fun x => logMessage (G x) hu hA (hBound x) q) := by
  apply measurable_of_tendsto_metrizable (f := fun k x => logIterate (G x) u k q)
    (fun k => measurable_logIterate G hEnds hEdge hWeight hu k q)
  apply tendsto_pi_nhds.mpr
  intro x
  exact ((continuous_apply q).tendsto _).comp (tendsto_logIterate (G x) hu hA (hBound x))

include hEnds hEdge hWeight in
theorem measurable_occupation {u A : ℝ} (hu : 0 < u) (hA : 0 ≤ A)
    (hBound : ∀ x, IncidentWeightBound (G x) A) (e : E) :
    Measurable (fun x => occupation (G x) hu hA (hBound x) e) := by
  by_cases h : ∃ x, e ∈ (G x).edges
  · obtain ⟨x₀, he₀⟩ := h
    let a := endpoints (G x₀) ⟨e,he₀⟩
    have ha₀ : a.1 ∈ (G x₀).ends e := by
      rw [(endpoints_spec (G x₀) ⟨e,he₀⟩).2]
      exact mem_insert_self _ _
    have ha (x : X) : a.1 ∈ (G x).ends e := by
      rw [hEnds x, ← hEnds x₀]
      exact ha₀
    let child : State V E := (Tree.otherEnd ends e a.1, some e)
    let p (x : X) :=
      edgeOccupation ((G x).weight e)
        (message (G x) hu hA (hBound x) (a.1,some e))
        (message (G x) hu hA (hBound x) child)
    have hp : Measurable p := by
      have hm (q : State V E) : Measurable (fun x => message (G x) hu hA (hBound x) q) :=
        (measurable_logMessage G hEnds hEdge hWeight hu hA hBound q).exp
      have hterm := ((hWeight e).mul (hm (a.1,some e))).mul (hm child)
      exact hterm.div (measurable_const.add hterm)
    have heq (x : X) : occupation (G x) hu hA (hBound x) e =
        if e ∈ (G x).edges then p x else 0 := by
      split_ifs with he
      · have hi : e ∈ incidentEdges (G x) a.1 := Finset.mem_filter.mpr ⟨he,ha x⟩
        rw [occupation_eq_for_incident _ _ _ _ hi]
        simp only [p, incomingState, child, hEnds]
      · simp only [occupation, dif_neg he]
    simp_rw [heq]
    exact Measurable.ite (hEdge e) hp measurable_const
  · push Not at h
    simp only [occupation, dif_neg (h _)]
    exact measurable_const

end Certificate.OverlapBelief

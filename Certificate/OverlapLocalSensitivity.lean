import Certificate.OverlapBeliefIterateOccupations
import Certificate.OverlapBeliefLocal

/-! Changing a bounded number of edges affects only a bounded number of neighborhoods. -/

open Finset
namespace Certificate.Overlap

open OverlapBelief

variable {V E : Type*} [DecidableEq V] [DecidableEq E]

/-- Vertices incident to at least one edge in a finite edge set. -/
def touchedVertices (ends : E → Finset V) (bad : Finset E) : Finset V :=
  bad.biUnion ends

/-- Add the neighbors of every vertex in the marked set. -/
def growVertices (ends : E → Finset V) (edges : Finset E) (U : Finset V) : Finset V :=
  U ∪ U.biUnion (fun v => touchedVertices ends (edges.filter fun e => v ∈ ends e))

/-- The vertices within a prescribed distance of a changed edge. -/
def affectedVertices (ends : E → Finset V) (edges bad : Finset E) : ℕ → Finset V
  | 0 => touchedVertices ends bad
  | k+1 => growVertices ends edges (affectedVertices ends edges bad k)

omit [DecidableEq E] in
theorem card_touchedVertices_le (ends : E → Finset V) (bad : Finset E)
    (hends : ∀ e ∈ bad, (ends e).card ≤ 2) :
    (touchedVertices ends bad).card ≤ bad.card * 2 :=
  card_biUnion_le_card_mul _ _ _ hends

theorem card_growVertices_le (ends : E → Finset V) (edges : Finset E) (U : Finset V)
    (hends : ∀ e ∈ edges, (ends e).card ≤ 2) {D : ℕ}
    (hdegree : ∀ v, (edges.filter fun e => v ∈ ends e).card ≤ D) :
    (growVertices ends edges U).card ≤ U.card * (1+2*D) := by
  have htemp (v : V) :
      (touchedVertices ends (edges.filter fun e => v ∈ ends e)).card ≤ 2*D := by
    refine (card_touchedVertices_le _ _ (fun e he => hends e (mem_filter.mp he).1)).trans ?_
    simpa only [mul_comm _ 2] using Nat.mul_le_mul_right 2 (hdegree v)
  calc
    _ ≤ U.card + (U.biUnion (fun v => touchedVertices ends (edges.filter fun e => v ∈ ends e))).card :=
      card_union_le _ _
    _ ≤ U.card + U.card * (2*D) :=
      add_le_add_right (card_biUnion_le_card_mul _ _ _ (fun v _ => htemp v)) _
    _ = _ := by ring

/-- The number of affected roots is controlled by a deterministic ball
volume bound under a degree cap. -/
theorem card_affectedVertices_le (ends : E → Finset V) (edges bad : Finset E)
    (hbad : bad ⊆ edges) (hends : ∀ e ∈ edges, (ends e).card ≤ 2) {D : ℕ}
    (hdegree : ∀ v, (edges.filter fun e => v ∈ ends e).card ≤ D) (k : ℕ) :
    (affectedVertices ends edges bad k).card ≤ 2 * bad.card * (1+2*D)^k := by
  induction k with
  | zero =>
    simpa only [affectedVertices, pow_zero, mul_one, Nat.mul_comm] using
      card_touchedVertices_le ends bad (fun e he => hends e (hbad he))
  | succ k ih =>
    rw [affectedVertices]
    exact (card_growVertices_le ends edges _ hends hdegree).trans
      (by rw [pow_succ, ← mul_assoc]; exact Nat.mul_le_mul_right _ ih)

omit [DecidableEq E] in
private theorem notMem_previous_of_notMem_affected
    (ends : E → Finset V) (edges bad : Finset E) {k : ℕ} {v : V}
    (h : v ∉ affectedVertices ends edges bad k) : v ∉ touchedVertices ends bad := by
  induction k with
  | zero => exact h
  | succ k ih =>
    apply ih
    exact fun hv => h (mem_union_left _ hv)

omit [DecidableEq E] in
private theorem notMem_neighbor_of_notMem_grow
    (ends : E → Finset V) (edges : Finset E) (U : Finset V)
    {v w : V} {e : E} (hv : v ∉ growVertices ends edges U)
    (he : e ∈ edges) (hve : v ∈ ends e) (hwe : w ∈ ends e) : w ∉ U := by
  intro hw
  exact hv (mem_union_right _ (mem_biUnion.mpr ⟨w,hw,
    mem_biUnion.mpr ⟨e,mem_filter.mpr ⟨he,hwe⟩,hve⟩⟩))

section Agreement

variable {G H : WeightedGraph V E} (hends : G.ends = H.ends)
variable (bad : Finset E)
variable (hagree : ∀ e ∉ bad, (e ∈ G.edges ↔ e ∈ H.edges) ∧
  (e ∈ G.edges → G.weight e = H.weight e))

private theorem bad_notMem_of_notMem_affected {k : ℕ} {v : V} {e : E}
    (hv : v ∉ affectedVertices G.ends (G.edges ∪ H.edges) bad k)
    (he : v ∈ G.ends e) : e ∉ bad := by
  intro he'
  exact (notMem_previous_of_notMem_affected _ _ _ hv)
    (mem_biUnion.mpr ⟨e,he',he⟩)

include hends hagree in
private theorem incomingEdges_eq_of_notMem_affected {k : ℕ} {v : V} (o : Option E)
    (hv : v ∉ affectedVertices G.ends (G.edges ∪ H.edges) bad k) :
    incomingEdges G (v,o) = incomingEdges H (v,o) := by
  have hi : incidentEdges G v = incidentEdges H v := by
    ext e
    simp only [incidentEdges, mem_filter, ← hends]
    by_cases h : v ∈ G.ends e
    · rw [(hagree e (bad_notMem_of_notMem_affected bad hv h)).1]
    · simp [h]
  cases o <;> simp [incomingEdges, hi]

include hends hagree in
private theorem incident_eq_of_notMem_affected {k : ℕ} {v : V} (s : Finset V)
    (hv : v ∉ affectedVertices G.ends (G.edges ∪ H.edges) bad k) :
    Tree.incident G.ends s G.edges v = Tree.incident H.ends s H.edges v := by
  ext e
  simp only [Tree.incident, mem_filter, ← hends]
  by_cases h : v ∈ G.ends e
  · rw [(hagree e (bad_notMem_of_notMem_affected bad hv h)).1]
  · simp [h]

private theorem incoming_mem_incidentEdges {G : WeightedGraph V E} {v : V} {o : Option E} {e : E}
    (he : e ∈ incomingEdges G (v,o)) : e ∈ G.edges ∧ v ∈ G.ends e := by
  cases o
  · exact mem_filter.mp he
  · exact mem_filter.mp (mem_erase.mp he).2

private theorem otherEnd_mem_of_incident {G : WeightedGraph V E} {v : V} {e : E}
    (he : e ∈ G.edges) (hv : v ∈ G.ends e) :
    Tree.otherEnd G.ends e v ∈ G.ends e := by
  have hp : ((G.ends e).erase v).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem hv, G.ends_card e he]
    decide
  unfold Tree.otherEnd
  rw [dif_pos hp]
  exact (mem_erase.mp hp.choose_spec).2

private theorem outside_affected_of_incoming {k : ℕ} {v : V} {e : E} {o : Option E}
    (hv : v ∉ affectedVertices G.ends (G.edges ∪ H.edges) bad (k+1))
    (he : e ∈ incomingEdges G (v,o)) :
    Tree.otherEnd G.ends e v ∉ affectedVertices G.ends (G.edges ∪ H.edges) bad k := by
  obtain ⟨heG,hve⟩ := incoming_mem_incidentEdges he
  exact notMem_neighbor_of_notMem_grow _ _ _ hv
    (mem_union_left _ heG) hve (otherEnd_mem_of_incident heG hve)

include hends hagree in
/-- The tree condition at a root is unaffected by changes beyond its
finite neighborhood. -/
theorem walkCompatible_iff_of_notMem_affectedVertices (k : ℕ) (remain : Finset V)
    (v : V) (o : Option E)
    (hv : v ∉ affectedVertices G.ends (G.edges ∪ H.edges) bad k) :
    walkCompatible G k remain (v,o) ↔ walkCompatible H k remain (v,o) := by
  induction k generalizing remain v o with
  | zero => rfl
  | succ k ih =>
    have hI := incomingEdges_eq_of_notMem_affected hends bad hagree o hv
    have hD := incident_eq_of_notMem_affected hends bad hagree remain hv
    have hs (e : E) : incomingState G v e = incomingState H v e := by simp [incomingState, hends]
    rw [walkCompatible, walkCompatible, ← hI, ← hD]
    refine and_congr_right fun _ => forall₂_congr fun e he => ?_
    rw [← hs e]
    exact ih _ _ _ (outside_affected_of_incoming bad hv he)

variable [Fintype V] [Fintype E]

include hends hagree in
/-- The finite belief-propagation log-message iterates agree at a vertex
whose neighborhood is disjoint from the changed edges. -/
theorem logIterate_eq_of_notMem_affectedVertices {u : ℝ} (hu : 0 < u)
    (k : ℕ) (v : V) (o : Option E)
    (hv : v ∉ affectedVertices G.ends (G.edges ∪ H.edges) bad k) :
    logIterate G u k (v,o) = logIterate H u k (v,o) := by
  induction k generalizing v o with
  | zero => rfl
  | succ k ih =>
    rw [logIterate_succ G hu, logIterate_succ H hu]
    have hI := incomingEdges_eq_of_notMem_affected hends bad hagree o hv
    unfold logUpdate
    rw [← hI]
    apply congrArg (fun x : ℝ => -Real.log (u+x))
    apply Finset.sum_congr rfl
    intro e he
    obtain ⟨heG,hve⟩ := incoming_mem_incidentEdges he
    rw [(hagree e (bad_notMem_of_notMem_affected bad hv hve)).2 heG]
    have hs : incomingState H v e = incomingState G v e := by simp [incomingState, hends]
    change H.weight e * Real.exp (logIterate G u k (incomingState G v e)) =
      H.weight e * Real.exp (logIterate H u k (incomingState H v e))
    rw [hs]
    exact congrArg (fun x : ℝ => H.weight e * Real.exp x)
      (ih _ _ (outside_affected_of_incoming bad hv he))

include hends hagree in
/-- The incident edges and their finite-iterate occupations are unchanged
outside the affected neighborhood of radius one beyond the iterate depth. -/
theorem incidentOccupationIterate_agree_of_notMem_affectedVertices {u : ℝ} (hu : 0 < u)
    (k : ℕ) (v : V)
    (hv : v ∉ affectedVertices G.ends (G.edges ∪ H.edges) bad (k+1)) :
    incidentEdges G v = incidentEdges H v ∧
      Set.EqOn (incidentOccupationIterate G u k v) (incidentOccupationIterate H u k v)
        (incidentEdges G v) := by
  have hI := incomingEdges_eq_of_notMem_affected hends bad hagree none hv
  change incidentEdges G v = incidentEdges H v at hI
  refine ⟨hI, ?_⟩
  intro e he
  have hIn : e ∈ incomingEdges G (v, none) := he
  have hv' : v ∉ affectedVertices G.ends (G.edges ∪ H.edges) bad k :=
    fun h => hv (mem_union_left _ h)
  obtain ⟨heG,hve⟩ := incoming_mem_incidentEdges hIn
  have hw := (hagree e (bad_notMem_of_notMem_affected bad hv hve)).2 heG
  have hq : incomingState H v e = incomingState G v e := by simp [incomingState, hends]
  have hfirst := logIterate_eq_of_notMem_affectedVertices hends bad hagree hu k v (some e) hv'
  have hlast := logIterate_eq_of_notMem_affectedVertices hends bad hagree hu k
    (Tree.otherEnd G.ends e v) (some e) (outside_affected_of_incoming bad hv hIn)
  change logIterate G u k (incomingState G v e) = logIterate H u k (incomingState G v e) at hlast
  unfold incidentOccupationIterate
  rw [hw,hfirst,hq,hlast]

end Agreement
end Certificate.Overlap

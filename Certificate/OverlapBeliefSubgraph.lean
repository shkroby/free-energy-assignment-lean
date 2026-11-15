import Certificate.OverlapBeliefLocal
import Certificate.SoftCutoff

/-! Compatible neighborhoods are preserved by removing edges and changing weights. -/

open Finset Set
open scoped BigOperators

namespace Certificate.OverlapBelief

variable {V E : Type*} [DecidableEq V] [DecidableEq E]
variable (G H : WeightedGraph V E)

/-- Edge deletion preserves the agreement between the nonbacktracking and
vertex-deletion recursions. The graph weights play no role. -/
theorem walkCompatible_of_edges_subset (hends : H.ends = G.ends) (hes : H.edges ⊆ G.edges)
    {k : ℕ} {s : Finset V} {q : State V E} (hq : walkCompatible G k s q) :
    walkCompatible H k s q := by
  have hin (q' : State V E) : incomingEdges H q' =
      (incomingEdges G q').filter (fun e => e ∈ H.edges) := by
    rcases q' with ⟨v, q'⟩
    cases q' with
    | none =>
      ext e
      simp only [incomingEdges, incidentEdges, mem_filter, hends]
      exact ⟨fun ⟨he,hv⟩ => ⟨⟨hes he,hv⟩,he⟩, fun ⟨⟨_,hv⟩,he⟩ => ⟨he,hv⟩⟩
    | some e' =>
      ext e
      simp only [incomingEdges, incidentEdges, mem_filter, mem_erase, hends]
      exact ⟨fun ⟨hne,he,hv⟩ => ⟨⟨hne,hes he,hv⟩,he⟩, fun ⟨⟨hne,_,hv⟩,he⟩ => ⟨hne,he,hv⟩⟩
  have hinc (s' : Finset V) (v : V) : Tree.incident H.ends s' H.edges v =
      (Tree.incident G.ends s' G.edges v).filter (fun e => e ∈ H.edges) := by
    ext e
    simp only [Tree.incident, mem_filter, hends]
    exact ⟨fun ⟨he,hv,hs⟩ => ⟨⟨hes he,hv,hs⟩,he⟩, fun ⟨⟨_,hv,hs⟩,he⟩ => ⟨he,hv,hs⟩⟩
  have hchild (v : V) (e : E) : incomingState H v e = incomingState G v e := by
    simp only [incomingState, hends]
  induction k generalizing s q with
  | zero => trivial
  | succ k ih =>
    obtain ⟨hEq, hNext⟩ := hq
    refine ⟨?_, ?_⟩
    · rw [hin, hinc, hEq]
    · intro e he
      rw [hchild]
      exact ih (hNext e (Finset.mem_filter.mp ((hin q) ▸ he)).1)

/-- Compatibility at a root is inherited by any spanning subgraph. -/
theorem goodRoot_of_edges_subset (hends : H.ends = G.ends) (hv : H.vertices = G.vertices)
    (hes : H.edges ⊆ G.edges) {k : ℕ} {v : V} (h : goodRoot G k v) :
    goodRoot H k v := by
  unfold goodRoot
  rw [hv]
  exact walkCompatible_of_edges_subset G H hends hes h

theorem goodRoot_retain {kept : Finset E} (hkept : kept ⊆ G.edges) {k : ℕ} {v : V}
    (h : goodRoot G k v) : goodRoot (G.retain kept hkept) k v :=
  goodRoot_of_edges_subset G (G.retain kept hkept) rfl rfl hkept h

theorem goodRoot_tilt {τ : ℝ} {f : E → ℝ} {k : ℕ} {v : V}
    (h : goodRoot G k v) : goodRoot (tilt G τ f) k v :=
  goodRoot_of_edges_subset G (tilt G τ f) rfl rfl (subset_refl _) h

omit [DecidableEq E] in
theorem incidentWeightBound_tilt {A τ : ℝ} {f : E → ℝ}
    (h : IncidentWeightBound G A) (hf : ∀ e ∈ G.edges, |f e| ≤ 1) :
    IncidentWeightBound (tilt G τ f) (A * Real.exp |τ|) := by
  intro v
  change (∑ e ∈ incidentEdges G v, G.weight e * Real.exp (τ * f e)) ≤ _
  calc
    _ ≤ ∑ e ∈ incidentEdges G v, G.weight e * Real.exp |τ| := by
      apply Finset.sum_le_sum
      intro e he
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (G.weight_nonneg e)
      calc
        _ ≤ |τ*f e| := le_abs_self _
        _ = |τ| * |f e| := abs_mul _ _
        _ ≤ _ := mul_le_of_le_one_right (abs_nonneg _) (hf e (Finset.mem_filter.mp he).1)
    _ ≤ _ := by
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (h v) (Real.exp_nonneg _)

end Certificate.OverlapBelief

import Certificate.OverlapAssignmentBelief
import Certificate.OverlapBeliefIterateOccupations
import Certificate.OverlapRowTests

/-! Measurability of the finite-depth row occupation observables. -/

open Finset Function Set
open scoped BigOperators

namespace Certificate.Overlap

open Certificate.OverlapBelief

private theorem measurable_incidentOccupationIterate (β d κ R : ℝ)
    (n D k : ℕ) {u : ℝ} (hu : 0 < u) (root : Fin n) (e : Fin n × Fin n) :
    Measurable (fun C => incidentOccupationIterate
      (trimmedAssignmentGraph β d κ R n D C) u k (Sum.inl root) e) := by
  let G := trimmedAssignmentGraph β d κ R n D
  have hEdge (f : Fin n × Fin n) : MeasurableSet {C | f ∈ (G C).edges} :=
    (measurableSet_mem_finset f).preimage (measurable_trimmedEdges β d κ R n D)
  have hWeight (f : Fin n × Fin n) : Measurable (fun C => (G C).weight f) := by
    change Measurable (fun C : CostArray =>
      Real.exp (-β * (lengthScale d κ n * C (f.1.val,f.2.val))))
    exact (measurable_const.mul (measurable_const.mul (measurable_pi_apply _))).exp
  let q₁ : State (Fin n ⊕ Fin n) (Fin n × Fin n) := (Sum.inl root,some e)
  let q₂ : State (Fin n ⊕ Fin n) (Fin n × Fin n) :=
    (Tree.otherEnd Tree.Bipartite.ends e (Sum.inl root), some e)
  have hIter (q : State (Fin n ⊕ Fin n) (Fin n × Fin n)) :
      Measurable (fun C => Real.exp (logIterate (G C) u k q)) :=
    (measurable_logIterate G (ends := Tree.Bipartite.ends) (fun _ => rfl) hEdge hWeight hu k q).exp
  have h := ((hWeight e).mul (hIter q₁)).mul (hIter q₂)
  exact h.div (measurable_const.add h)

private theorem measurable_of_finite_sections {X E : Type*} [MeasurableSpace X]
    [Fintype E] [DecidableEq E] (s : X → Finset E) (hs : Measurable s)
    (f : Finset E → X → ℝ) (hf : ∀ b, Measurable (f b)) :
    Measurable (fun x => f (s x) x) := by
  classical
  let g (b : Finset E) (x : X) := if s x = b then f b x else 0
  have hg (b : Finset E) : Measurable (g b) :=
    Measurable.ite ((measurableSet_singleton b).preimage hs) (hf b) measurable_const
  have hsum : Measurable (fun x => ∑ b : Finset E, g b x) :=
    Finset.measurable_fun_sum _ fun b _ => hg b
  convert hsum using 1
  funext x
  rw [Finset.sum_eq_single (s x)]
  · simp [g]
  · intro b _ hb
    simp [g, hb.symm]
  · simp

private theorem measurable_trimmed_incidentEdges (β d κ R : ℝ) (n D : ℕ) (root : Fin n) :
    Measurable (fun C : CostArray =>
      incidentEdges (trimmedAssignmentGraph β d κ R n D C) (Sum.inl root)) :=
  (measurable_of_countable fun (s : Finset (Fin n × Fin n)) =>
    s.filter (fun e => Sum.inl root ∈ Tree.Bipartite.ends e)).comp
      (measurable_trimmedEdges β d κ R n D)

/-- The finite square-row iterate test is measurable in the cost array. -/
theorem measurable_trimmedIterate_square (β d κ R : ℝ) (n D k : ℕ) {u : ℝ}
    (hu : 0 < u) (root : Fin n) :
    Measurable (fun C => squareRowTest
      (incidentEdges (trimmedAssignmentGraph β d κ R n D C) (Sum.inl root))
      (incidentOccupationIterate (trimmedAssignmentGraph β d κ R n D C) u k (Sum.inl root))) := by
  refine measurable_of_finite_sections _ (measurable_trimmed_incidentEdges β d κ R n D root)
    (fun s C => squareRowTest s
      (incidentOccupationIterate (trimmedAssignmentGraph β d κ R n D C) u k (Sum.inl root))) ?_
  intro s
  exact (continuous_squareRowTest s id (fun e _ => continuous_apply e)).measurable.comp
    (measurable_pi_lambda _ (measurable_incidentOccupationIterate β d κ R n D k hu root))

/-- The finite small-third iterate test is measurable in the cost array. -/
theorem measurable_trimmedIterate_smallThird (β d κ R : ℝ) (n D k : ℕ) (η : ℝ)
    {u : ℝ} (hu : 0 < u) (root : Fin n) :
    Measurable (fun C => smallOccupationTest η
      (thirdOccupation (incidentEdges (trimmedAssignmentGraph β d κ R n D C) (Sum.inl root))
        (incidentOccupationIterate (trimmedAssignmentGraph β d κ R n D C) u k (Sum.inl root)))) := by
  refine measurable_of_finite_sections _ (measurable_trimmed_incidentEdges β d κ R n D root)
    (fun s C => smallOccupationTest η (thirdOccupation s
      (incidentOccupationIterate (trimmedAssignmentGraph β d κ R n D C) u k (Sum.inl root)))) ?_
  intro s
  exact ((continuous_smallOccupationTest η).comp
    (continuous_thirdOccupation s id (fun e _ => continuous_apply e))).measurable.comp
    (measurable_pi_lambda _ (measurable_incidentOccupationIterate β d κ R n D k hu root))

end Certificate.Overlap

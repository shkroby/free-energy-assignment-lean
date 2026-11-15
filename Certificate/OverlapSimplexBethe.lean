import Certificate.OverlapSimplexEntropy
import Certificate.SoftPressure

/-!
# Stationary finite Bethe optimization

The feasible edge occupancies extend to one probability vector at each
vertex by adding the unmatched mass. The incidence identity combines
their entropy tangents with the binary slack entropy tangents.
-/

open Finset Set
open scoped BigOperators

namespace Certificate.Overlap

variable {V E : Type*} [DecidableEq V] [DecidableEq E]

/-- Edges incident to the vertex in the given finite graph. -/
abbrev incidentEdges (G : WeightedGraph V E) (v : V) : Finset E :=
  Tree.incident G.ends G.vertices G.edges v

/-- Unmatched mass at a vertex of the finite graph Bethe functional. -/
def vertexSlack (G : WeightedGraph V E) (p : E → ℝ) (v : V) : ℝ :=
  1 - ∑ e ∈ incidentEdges G v, p e

/-- Nonnegative edge masses whose sums at each vertex are at most one. -/
def Feasible (G : WeightedGraph V E) (p : E → ℝ) : Prop :=
  (∀ e ∈ G.edges, 0 ≤ p e) ∧ ∀ v ∈ G.vertices, 0 ≤ vertexSlack G p v

/-- The finite graph Bethe objective at positive monomer fugacity. -/
noncomputable def finiteBethe (G : WeightedGraph V E) (z : ℝ) (p : E → ℝ) : ℝ :=
  (∑ e ∈ G.edges, (p e * Real.log (G.weight e) + betheAtom (p e))) +
  ∑ v ∈ G.vertices, (vertexSlack G p v * Real.log z -
    vertexSlack G p v * Real.log (vertexSlack G p v))

/-- The derivative of the scalar monomer contribution at the slack mass. -/
noncomputable def vertexBetheSlope (G : WeightedGraph V E) (z : ℝ)
    (γ : E → ℝ) (v : V) : ℝ :=
  Real.log z - Real.log (vertexSlack G γ v) - 1

/-- Edge derivatives cancel the two endpoint derivatives at an interior
stationary occupation. -/
def BetheStationary (G : WeightedGraph V E) (z : ℝ) (γ : E → ℝ) : Prop :=
  ∀ e ∈ G.edges, Real.log (G.weight e) + betheAtomSlope (γ e) =
    ∑ v ∈ G.ends e, vertexBetheSlope G z γ v

/-- The edge displacement in total variation without the factor of one half. -/
def vertexL1 (G : WeightedGraph V E) (γ p : E → ℝ) (v : V) : ℝ :=
  ∑ e ∈ incidentEdges G v, |p e - γ e|

omit [DecidableEq E] in
theorem mem_incidentEdges_iff {G : WeightedGraph V E} {v : V} {e : E} :
    e ∈ incidentEdges G v ↔ e ∈ G.edges ∧ v ∈ G.ends e := by
  change e ∈ Tree.incident G.ends G.vertices G.edges v ↔ _
  unfold Tree.incident
  rw [Finset.mem_filter]
  exact ⟨fun h => ⟨h.1,h.2.1⟩, fun h => ⟨h.1,h.2,G.ends_subset e h.1⟩⟩

omit [DecidableEq E] in
theorem sum_incident_comm (G : WeightedGraph V E) (rows : Finset V) (f : V → E → ℝ) :
    (∑ v ∈ rows, ∑ e ∈ incidentEdges G v, f v e) =
      ∑ e ∈ G.edges, ∑ v ∈ rows ∩ G.ends e, f v e := by
  classical
  have hI (v : V) : incidentEdges G v = G.edges.filter (fun e => v ∈ G.ends e) := by
    ext e
    simp only [mem_incidentEdges_iff, Finset.mem_filter]
  simp_rw [hI, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [← Finset.sum_filter]
  rfl

omit [DecidableEq E] in
theorem sum_incident_vertices (G : WeightedGraph V E) (f : V → E → ℝ) :
    (∑ v ∈ G.vertices, ∑ e ∈ incidentEdges G v, f v e) =
      ∑ e ∈ G.edges, ∑ v ∈ G.ends e, f v e := by
  rw [sum_incident_comm]
  exact Finset.sum_congr rfl (fun e he => by
    rw [Finset.inter_eq_right.mpr (G.ends_subset e he)])

omit [DecidableEq E] in
private theorem sum_incident_twice (G : WeightedGraph V E) (f : E → ℝ) :
    (∑ v ∈ G.vertices, ∑ e ∈ incidentEdges G v, f e) = 2 * ∑ e ∈ G.edges, f e := by
  rw [sum_incident_vertices, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  simp [G.ends_card e he, two_mul]

private def someEmbedding (E : Type*) : E ↪ Option E := ⟨some, Option.some_injective E⟩

private def vertexCoordinates (G : WeightedGraph V E) (v : V) : Finset (Option E) :=
  insert none ((incidentEdges G v).map (someEmbedding E))

private def vertexVector (G : WeightedGraph V E) (p : E → ℝ) (v : V) : Option E → ℝ
  | none => vertexSlack G p v
  | some e => p e

private theorem sum_vertexCoordinates (G : WeightedGraph V E) (v : V) (f : Option E → ℝ) :
    (∑ i ∈ vertexCoordinates G v, f i) = f none + ∑ e ∈ incidentEdges G v, f (some e) := by
  have hn : none ∉ (incidentEdges G v).map (someEmbedding E) := by
    simp [someEmbedding]
  simp only [vertexCoordinates, Finset.sum_insert hn, Finset.sum_map]
  rfl

private theorem vertexVector_simplex {G : WeightedGraph V E} {p : E → ℝ} (hp : Feasible G p)
    {v : V} (hv : v ∈ G.vertices) :
    SimplexOn (vertexCoordinates G v) (vertexVector G p v) := by
  constructor
  · intro i hi
    cases i with
    | none => exact hp.2 v hv
    | some e =>
      have h : e ∈ incidentEdges G v := by
        simpa [vertexCoordinates, someEmbedding] using hi
      exact hp.1 e ((mem_incidentEdges_iff (G := G)).mp h).1
  · rw [sum_vertexCoordinates]
    change vertexSlack G p v + ∑ e ∈ incidentEdges G v, p e = 1
    unfold vertexSlack
    ring

omit [DecidableEq E] in
private theorem vertexSlack_le_one {G : WeightedGraph V E} {p : E → ℝ} (hp : Feasible G p) (v : V) :
    vertexSlack G p v ≤ 1 :=
  sub_le_self _ (Finset.sum_nonneg fun e he => hp.1 e ((mem_incidentEdges_iff (G := G)).mp he).1)

omit [DecidableEq E] in
private theorem vertexSlack_lt_one_of_nonempty {G : WeightedGraph V E} {γ : E → ℝ}
    (hγ : ∀ e ∈ G.edges, γ e ∈ Ioo (0 : ℝ) 1) {v : V} (hn : (incidentEdges G v).Nonempty) :
    vertexSlack G γ v < 1 := by
  obtain ⟨e,he⟩ := hn
  have hs : γ e ≤ ∑ i ∈ incidentEdges G v, γ i :=
    Finset.single_le_sum (fun i hi => (hγ i ((mem_incidentEdges_iff (G := G)).mp hi).1).1.le) he
  unfold vertexSlack
  linarith only [hs, (hγ e ((mem_incidentEdges_iff (G := G)).mp he).1).1]

private theorem vertexVector_interior_of_nonempty {G : WeightedGraph V E} {γ : E → ℝ} {v : V}
    (hγ : ∀ e ∈ G.edges, γ e ∈ Ioo (0 : ℝ) 1) (hSlack : 0 < vertexSlack G γ v)
    (hn : (incidentEdges G v).Nonempty) :
    ∀ i ∈ vertexCoordinates G v, vertexVector G γ v i ∈ Ioo (0 : ℝ) 1 := by
  intro i hi
  cases i with
  | none => exact ⟨hSlack, vertexSlack_lt_one_of_nonempty hγ hn⟩
  | some e =>
    have he : e ∈ incidentEdges G v := by
      simpa [vertexCoordinates, someEmbedding] using hi
    exact hγ e ((mem_incidentEdges_iff (G := G)).mp he).1

private theorem threeLarge_vertexVector {G : WeightedGraph V E} {γ : E → ℝ} {v : V} {η : ℝ}
    (h : ThreeLargeOn (incidentEdges G v) γ η) :
    ThreeLargeOn (vertexCoordinates G v) (vertexVector G γ v) η := by
  obtain ⟨i,hi,j,hj,k,hk,hij,hik,hjk,hI,hJ,hK⟩ := h
  exact ⟨some i, by simp [vertexCoordinates,someEmbedding,hi],
    some j, by simp [vertexCoordinates,someEmbedding,hj],
    some k, by simp [vertexCoordinates,someEmbedding,hk],
    fun h => hij (Option.some.inj h), fun h => hik (Option.some.inj h),
    fun h => hjk (Option.some.inj h), hI,hJ,hK⟩

private theorem simplexEntropy_vertex_eq (G : WeightedGraph V E) (p : E → ℝ) (v : V) :
    simplexEntropy (vertexCoordinates G v) (vertexVector G p v) =
      betheAtom (vertexSlack G p v) + ∑ e ∈ incidentEdges G v, betheAtom (p e) :=
  sum_vertexCoordinates G v (fun i => betheAtom (vertexVector G p v i))

private theorem simplexTangent_vertex_eq (G : WeightedGraph V E) (γ p : E → ℝ) (v : V) :
    simplexTangent (vertexCoordinates G v) (vertexVector G γ v) (vertexVector G p v) =
      betheAtomSlope (vertexSlack G γ v) * (vertexSlack G p v - vertexSlack G γ v) +
      ∑ e ∈ incidentEdges G v, betheAtomSlope (γ e) * (p e - γ e) :=
  sum_vertexCoordinates G v (fun i => betheAtomSlope (vertexVector G γ v i) *
    (vertexVector G p v i - vertexVector G γ v i))

private theorem finiteBethe_as_vertex_entropies (G : WeightedGraph V E) (z : ℝ) (p : E → ℝ) :
    finiteBethe G z p =
      (∑ e ∈ G.edges, p e * Real.log (G.weight e)) +
      (1/2) * (∑ v ∈ G.vertices, simplexEntropy (vertexCoordinates G v) (vertexVector G p v)) +
      ∑ v ∈ G.vertices, (vertexSlack G p v * Real.log z + (1/2)*binaryEntropy (vertexSlack G p v)) := by
  simp_rw [simplexEntropy_vertex_eq, Finset.sum_add_distrib, sum_incident_twice]
  unfold finiteBethe
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hAtom (v : V) : (1/2) * betheAtom (vertexSlack G p v) +
      (1/2) * binaryEntropy (vertexSlack G p v) =
      -(vertexSlack G p v * Real.log (vertexSlack G p v)) := by
    unfold betheAtom binaryEntropy Real.negMulLog
    ring
  have hSum := Finset.sum_congr (s₁ := G.vertices) rfl (fun v _ => hAtom v)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_neg_distrib] at hSum
  linarith only [hSum]

private theorem vertexEntropy_tangent_loss {G : WeightedGraph V E} {γ p : E → ℝ} {η : ℝ}
    (hγ : Feasible G γ) (hp : Feasible G p)
    (hInt : ∀ e ∈ G.edges, γ e ∈ Ioo (0 : ℝ) 1)
    (hSlack : ∀ v ∈ G.vertices, 0 < vertexSlack G γ v) (hη : 0 ≤ η)
    (good : Finset V) (hGood : ∀ v ∈ good, ThreeLargeOn (incidentEdges G v) γ η)
    {v : V} (hv : v ∈ G.vertices) :
    simplexEntropy (vertexCoordinates G v) (vertexVector G p v) ≤
      simplexEntropy (vertexCoordinates G v) (vertexVector G γ v) +
        simplexTangent (vertexCoordinates G v) (vertexVector G γ v) (vertexVector G p v) -
        (if v ∈ good then (η/32) * (vertexL1 G γ p v)^2 else 0) := by
  classical
  by_cases hvg : v ∈ good
  · have ht := hGood v hvg
    have hn : (incidentEdges G v).Nonempty := by
      obtain ⟨e,he,_⟩ := ht
      exact ⟨e,he⟩
    have hrow := simplexEntropy_tangent_loss (vertexVector_simplex hγ hv) (vertexVector_simplex hp hv)
      (vertexVector_interior_of_nonempty hInt (hSlack v hv) hn) hη (threeLarge_vertexVector ht)
    rw [if_pos hvg]
    apply hrow.trans
    have hAbs : (∑ i ∈ vertexCoordinates G v, |vertexVector G p v i - vertexVector G γ v i|) =
        |vertexSlack G p v - vertexSlack G γ v| + vertexL1 G γ p v :=
      sum_vertexCoordinates G v (fun i => |vertexVector G p v i - vertexVector G γ v i|)
    rw [hAbs]
    have hnorm : 0 ≤ vertexL1 G γ p v := Finset.sum_nonneg fun _ _ => abs_nonneg _
    exact sub_le_sub_left (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hnorm (le_add_of_nonneg_left (abs_nonneg _)) 2)
      (div_nonneg hη (by norm_num))) _
  · rw [if_neg hvg, sub_zero]
    by_cases hn : (incidentEdges G v).Nonempty
    · exact simplexEntropy_tangent (vertexVector_simplex hγ hv) (vertexVector_simplex hp hv)
        (vertexVector_interior_of_nonempty hInt (hSlack v hv) hn)
    · have he := Finset.not_nonempty_iff_eq_empty.mp hn
      simp only [simplexEntropy_vertex_eq, simplexTangent_vertex_eq, vertexSlack, he,
        Finset.sum_empty, sub_zero, sub_self, mul_zero, add_zero, le_refl]

omit [DecidableEq E] in
private theorem vertexBinary_tangent {G : WeightedGraph V E} {γ p : E → ℝ}
    (hp : Feasible G p) (hInt : ∀ e ∈ G.edges, γ e ∈ Ioo (0 : ℝ) 1) {v : V} (hv : v ∈ G.vertices)
    (hSlack : 0 < vertexSlack G γ v) :
    binaryEntropy (vertexSlack G p v) ≤ binaryEntropy (vertexSlack G γ v) +
      binaryEntropySlope (vertexSlack G γ v) * (vertexSlack G p v - vertexSlack G γ v) := by
  by_cases hn : (incidentEdges G v).Nonempty
  · exact binaryEntropy_tangent ⟨hSlack, vertexSlack_lt_one_of_nonempty hInt hn⟩
      ⟨hp.2 v hv, vertexSlack_le_one hp v⟩
  · have he := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [vertexSlack, he, Finset.sum_empty, sub_zero, sub_self, mul_zero, add_zero, le_refl]

omit [DecidableEq E] in
private theorem vertexCombined_tangent {G : WeightedGraph V E} {γ p : E → ℝ}
    (hInt : ∀ e ∈ G.edges, γ e ∈ Ioo (0 : ℝ) 1) (z : ℝ) {v : V}
    (hSlack : 0 < vertexSlack G γ v) :
    (1/2) * (betheAtomSlope (vertexSlack G γ v) * (vertexSlack G p v - vertexSlack G γ v)) +
      (1/2) * (binaryEntropySlope (vertexSlack G γ v) * (vertexSlack G p v - vertexSlack G γ v)) +
      Real.log z * (vertexSlack G p v - vertexSlack G γ v) =
      vertexBetheSlope G z γ v * (vertexSlack G p v - vertexSlack G γ v) := by
  by_cases hn : (incidentEdges G v).Nonempty
  · have hOne : 0 < 1-vertexSlack G γ v := sub_pos.mpr (vertexSlack_lt_one_of_nonempty hInt hn)
    unfold betheAtomSlope binaryEntropySlope vertexBetheSlope
    rw [Real.log_mul hSlack.ne' hOne.ne']
    ring
  · have he := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [vertexSlack, he, Finset.sum_empty, sub_zero, sub_self, mul_zero, add_zero]

omit [DecidableEq E] in
private theorem stationary_sum_eq_zero {G : WeightedGraph V E} {γ p : E → ℝ} {z : ℝ}
    (hstat : BetheStationary G z γ) :
    (∑ e ∈ G.edges, (Real.log (G.weight e) + betheAtomSlope (γ e)) * (p e - γ e)) +
      ∑ v ∈ G.vertices, vertexBetheSlope G z γ v * (vertexSlack G p v - vertexSlack G γ v) = 0 := by
  have he : (∑ e ∈ G.edges, (Real.log (G.weight e) + betheAtomSlope (γ e)) * (p e - γ e)) =
      ∑ e ∈ G.edges, ∑ v ∈ G.ends e, vertexBetheSlope G z γ v * (p e - γ e) := by
    apply Finset.sum_congr rfl
    intro e he
    rw [hstat e he, Finset.sum_mul]
  rw [he, ← sum_incident_vertices, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro v _
  rw [← Finset.mul_sum]
  unfold vertexSlack
  rw [Finset.sum_sub_distrib]
  ring

/-- A stationary interior edge occupation has a quadratic loss on any
selected vertices with at least three eta-large occupations. -/
theorem finiteBethe_stationary_loss (G : WeightedGraph V E) {z η : ℝ} {γ p : E → ℝ}
    (hγ : Feasible G γ) (hp : Feasible G p) (hInt : ∀ e ∈ G.edges, γ e ∈ Ioo (0 : ℝ) 1)
    (hSlack : ∀ v ∈ G.vertices, 0 < vertexSlack G γ v)
    (hstat : BetheStationary G z γ) (hη : 0 ≤ η)
    (good : Finset V) (hGoodV : good ⊆ G.vertices)
    (hGood : ∀ v ∈ good, ThreeLargeOn (incidentEdges G v) γ η) :
    finiteBethe G z p ≤ finiteBethe G z γ -
      (η/64) * ∑ v ∈ good, (vertexL1 G γ p v)^2 := by
  classical
  have hRow := Finset.sum_le_sum (fun v hv =>
    vertexEntropy_tangent_loss hγ hp hInt hSlack hη good hGood hv)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, simplexTangent_vertex_eq,
    sum_incident_twice] at hRow
  have hPenalty :
      (∑ v ∈ G.vertices, if v ∈ good then (η/32)*vertexL1 G γ p v ^2 else 0) =
        (η/32) * ∑ v ∈ good, vertexL1 G γ p v ^2 := by
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hGoodV, Finset.mul_sum]
  rw [hPenalty] at hRow
  have hBinary := Finset.sum_le_sum (fun v hv => vertexBinary_tangent hp hInt hv (hSlack v hv))
  simp only [Finset.sum_add_distrib] at hBinary
  have hCombined := Finset.sum_congr (s₁ := G.vertices) rfl
    (fun v hv => vertexCombined_tangent (p := p) hInt z (hSlack v hv))
  simp only [Finset.sum_add_distrib] at hCombined
  have hStat := stationary_sum_eq_zero (p := p) hstat
  simp only [add_mul, Finset.sum_add_distrib] at hStat
  have hEdgeEnergy :
      (∑ e ∈ G.edges, Real.log (G.weight e) * (p e - γ e)) =
      (∑ e ∈ G.edges, p e * Real.log (G.weight e)) -
        (∑ e ∈ G.edges, γ e * Real.log (G.weight e)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  have hVertexEnergy :
      (∑ v ∈ G.vertices, Real.log z * (vertexSlack G p v - vertexSlack G γ v)) =
      (∑ v ∈ G.vertices, vertexSlack G p v * Real.log z) -
        (∑ v ∈ G.vertices, vertexSlack G γ v * Real.log z) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [hEdgeEnergy] at hStat
  rw [hVertexEnergy] at hCombined
  simp only [← Finset.mul_sum] at hCombined
  simp only [finiteBethe_as_vertex_entropies, Finset.sum_add_distrib, ← Finset.mul_sum]
  nlinarith only [hRow, hBinary, hCombined, hStat]

/-- An interior stationary occupation maximizes the finite Bethe functional. -/
theorem finiteBethe_le_of_stationary {G : WeightedGraph V E} {z : ℝ} {γ p : E → ℝ}
    (hγ : Feasible G γ) (hp : Feasible G p) (hInt : ∀ e ∈ G.edges, γ e ∈ Ioo (0 : ℝ) 1)
    (hSlack : ∀ v ∈ G.vertices, 0 < vertexSlack G γ v)
    (hstat : BetheStationary G z γ) :
    finiteBethe G z p ≤ finiteBethe G z γ := by
  simpa using finiteBethe_stationary_loss G hγ hp hInt hSlack hstat (show 0 ≤ (0 : ℝ) from le_rfl)
    ∅ (Finset.empty_subset _) (by simp)

end Certificate.Overlap

import Certificate.OverlapBeliefContraction
import Certificate.Endpoints

/-! The edge occupations and vertex slack induced by belief propagation. -/

open Finset Set

namespace Certificate.OverlapBelief

section Graph

variable {V E : Type*} [DecidableEq V] [DecidableEq E]
variable (G : WeightedGraph V E)

omit [DecidableEq E] in
theorem incidentEdges_eq_incident (v : V) :
    incidentEdges G v = Tree.incident G.ends G.vertices G.edges v := by
  ext e
  simp only [incidentEdges, Tree.incident, Finset.mem_filter]
  exact ⟨fun ⟨he, hv⟩ => ⟨he, hv, G.ends_subset e he⟩, fun ⟨he, hv, _⟩ => ⟨he, hv⟩⟩

omit [DecidableEq E] in
/-- Degree and edge-weight bounds imply a bound on total incident weight. -/
theorem incidentWeightBound_of_degree {D : ℕ} {W : ℝ} (hW₀ : 0 ≤ W)
    (hD : ∀ v, (incidentEdges G v).card ≤ D) (hW : ∀ e ∈ G.edges, G.weight e ≤ W) :
    IncidentWeightBound G ((D : ℝ) * W) := by
  intro v
  calc
    _ ≤ ∑ e ∈ incidentEdges G v, W := Finset.sum_le_sum fun e he =>
      hW e (Finset.mem_filter.mp he).1
    _ = ((incidentEdges G v).card : ℝ) * W := by simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hD v)) hW₀

/-- Exponential tilt of the edge weights with graph structure fixed. -/
noncomputable def tilt (τ : ℝ) (f : E → ℝ) : WeightedGraph V E :=
  { G with
    weight := fun e => G.weight e * Real.exp (τ * f e)
    weight_nonneg := fun e => mul_nonneg (G.weight_nonneg e) (Real.exp_nonneg _) }

omit [DecidableEq V] [DecidableEq E] in
theorem tilt_weight_bounds {τ : ℝ} {f : E → ℝ} {W : ℝ}
    (hτ : |τ| ≤ 1) (hf : ∀ e ∈ G.edges, |f e| ≤ 1)
    (hw : ∀ e ∈ G.edges, 0 < G.weight e ∧ G.weight e ≤ W) :
    ∀ e ∈ (tilt G τ f).edges,
      0 < (tilt G τ f).weight e ∧ (tilt G τ f).weight e ≤ W * Real.exp 1 := by
  intro e he
  change 0 < G.weight e * Real.exp (τ * f e) ∧ G.weight e * Real.exp (τ * f e) ≤ _
  have hProd : τ * f e ≤ 1 := by
    calc
      _ ≤ |τ * f e| := le_abs_self _
      _ = |τ| * |f e| := abs_mul _ _
      _ ≤ 1 * 1 := mul_le_mul hτ (hf e he) (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  exact ⟨mul_pos (hw e he).1 (Real.exp_pos _),
    mul_le_mul (hw e he).2 (Real.exp_le_exp.mpr hProd) (Real.exp_nonneg _)
      ((hw e he).1.le.trans (hw e he).2)⟩

/-- Choose an orientation of each retained edge. The occupation will be
independent of this orientation. -/
noncomputable def endpoints (e : ↥G.edges) : V × V :=
  let h := Finset.card_eq_two.mp (G.ends_card e.val e.property)
  (h.choose, h.choose_spec.choose)

omit [DecidableEq E] in
theorem endpoints_spec (e : ↥G.edges) :
    (endpoints G e).1 ≠ (endpoints G e).2 ∧
      G.ends e.val = {(endpoints G e).1, (endpoints G e).2} :=
  (Finset.card_eq_two.mp (G.ends_card e.val e.property)).choose_spec.choose_spec

omit [DecidableEq E] in
theorem otherEnd_of_endpoints {e : E} {a b : V} (h : G.ends e = {a,b}) (hne : a ≠ b) :
    Tree.otherEnd G.ends e a = b := by
  have hs : (G.ends e).erase a = {b} := by
    rw [h, Finset.erase_insert (by simpa using hne)]
  have hn : ((G.ends e).erase a).Nonempty := hs ▸ Finset.singleton_nonempty b
  have hm : hn.choose = b := Finset.mem_singleton.mp ((le_of_eq hs) hn.choose_spec)
  simpa only [Tree.otherEnd, dif_pos hn] using hm

omit [DecidableEq E] in
theorem otherEnd_swap_of_endpoints {e : E} {a b : V} (h : G.ends e = {a,b}) (hne : a ≠ b) :
    Tree.otherEnd G.ends e b = a := by
  rw [show ({a,b} : Finset V) = {b,a} from Finset.pair_comm a b] at h
  exact otherEnd_of_endpoints G h hne.symm

section Finite

variable [Fintype V] [Fintype E] {u A : ℝ}
variable (hu : 0 < u) (hA : 0 ≤ A) (hW : IncidentWeightBound G A)

private theorem message_pos' (q : State V E) : 0 < message G hu hA hW q := Real.exp_pos _

/-- The marginal predicted for an edge by the two directed messages. -/
noncomputable def occupation (e : E) : ℝ :=
  if he : e ∈ G.edges then
    let a := endpoints G ⟨e, he⟩
    edgeOccupation (G.weight e) (message G hu hA hW (a.1, some e))
      (message G hu hA hW (a.2, some e))
  else 0

theorem occupation_eq_for_incident {v : V} {e : E} (he : e ∈ incidentEdges G v) :
    occupation G hu hA hW e = edgeOccupation (G.weight e)
      (message G hu hA hW (v, some e)) (message G hu hA hW (incomingState G v e)) := by
  obtain ⟨heG, hv⟩ := Finset.mem_filter.mp he
  let p := endpoints G ⟨e, heG⟩
  obtain ⟨hne, hp⟩ := endpoints_spec G ⟨e, heG⟩
  change p.1 ≠ p.2 at hne
  change G.ends e = {p.1,p.2} at hp
  rw [hp, Finset.mem_insert, Finset.mem_singleton] at hv
  rw [occupation, dif_pos heG]
  change edgeOccupation (G.weight e) (message G hu hA hW (p.1, some e))
    (message G hu hA hW (p.2, some e)) = _
  rcases hv with hv | hv
  · rw [hv, incomingState, otherEnd_of_endpoints G hp hne]
  · rw [hv, incomingState, otherEnd_swap_of_endpoints G hp hne,
      edgeOccupation_swap (G.weight e) (message G hu hA hW (p.1, some e))]

/-- Adding the directed edge back relates the cavity message to the root
message at its source. -/
theorem rootMessage_eq_fullEndpoint {v : V} {e : E} (he : e ∈ incidentEdges G v) :
    message G hu hA hW (v, none) =
      fullEndpoint (G.weight e) (message G hu hA hW (v, some e))
        (message G hu hA hW (incomingState G v e)) := by
  let f (j : E) := G.weight j * message G hu hA hW (incomingState G v j)
  let B := ∑ j ∈ (incidentEdges G v).erase e, f j
  have hB : 0 ≤ B := Finset.sum_nonneg fun j _ =>
    mul_nonneg (G.weight_nonneg j) (message_pos' G hu hA hW _).le
  have hD : 0 < u + B := add_pos_of_pos_of_nonneg hu hB
  have hD' : 0 < u + B + f e := add_pos_of_pos_of_nonneg hD
    (mul_nonneg (G.weight_nonneg e) (message_pos' G hu hA hW _).le)
  have hRoot : message G hu hA hW (v, none) = (u + (B + f e))⁻¹ := by
    have h := message_recursion G hu hA hW (v, none)
    change _ = (u + ∑ j ∈ incidentEdges G v, f j)⁻¹ at h
    rw [← Finset.sum_erase_add (incidentEdges G v) f he] at h
    exact h
  have hCavity : message G hu hA hW (v, some e) = (u + B)⁻¹ :=
    message_recursion G hu hA hW (v, some e)
  rw [hRoot, hCavity, fullEndpoint]
  have hf : 0 ≤ f e := mul_nonneg (G.weight_nonneg e) (message_pos' G hu hA hW _).le
  have hDen : 0 < 1 + (u + B)⁻¹ * f e :=
    add_pos_of_pos_of_nonneg one_pos (mul_nonneg (inv_nonneg.mpr hD.le) hf)
  have harg : G.weight e * (u + B)⁻¹ * message G hu hA hW (incomingState G v e) =
      (u + B)⁻¹ * f e := by dsimp only [f]; ring
  rw [← add_assoc, harg]
  field_simp [hD.ne', hD'.ne', hDen.ne']

theorem occupation_eq_weight_mul_root {v : V} {e : E} (he : e ∈ incidentEdges G v) :
    occupation G hu hA hW e = G.weight e * message G hu hA hW (v, none) *
      message G hu hA hW (incomingState G v e) := by
  rw [occupation_eq_for_incident G hu hA hW he, rootMessage_eq_fullEndpoint G hu hA hW he]
  unfold fullEndpoint edgeOccupation
  ring

/-- The remaining incident mass is the root monomer probability. -/
theorem occupation_slack (v : V) :
    1 - ∑ e ∈ incidentEdges G v, occupation G hu hA hW e =
      u * message G hu hA hW (v, none) := by
  let f (e : E) := G.weight e * message G hu hA hW (incomingState G v e)
  let S := ∑ e ∈ incidentEdges G v, f e
  have hsum : (∑ e ∈ incidentEdges G v, occupation G hu hA hW e) =
      S * message G hu hA hW (v, none) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun e he => (occupation_eq_weight_mul_root G hu hA hW he).trans (by
      dsimp [f]; ring)
  rw [hsum, message_recursion G hu hA hW (v, none)]
  change 1 - S * (u + S)⁻¹ = u * (u + S)⁻¹
  have hs : 0 ≤ S := Finset.sum_nonneg fun j _ =>
    mul_nonneg (G.weight_nonneg j) (message_pos' G hu hA hW _).le
  field_simp [(add_pos_of_pos_of_nonneg hu hs).ne']
  ring

theorem occupation_mem_Ioo {e : E} (he : e ∈ G.edges) (hw : 0 < G.weight e) :
    occupation G hu hA hW e ∈ Set.Ioo 0 1 := by
  rw [occupation, dif_pos he]
  exact ⟨edgeOccupation_pos hw (message_pos' G hu hA hW _) (message_pos' G hu hA hW _),
    edgeOccupation_lt_one hw (message_pos' G hu hA hW _) (message_pos' G hu hA hW _)⟩

/-- The stationarity identity in multiplicative form. -/
theorem occupation_mul_compl {e : E} (he : e ∈ G.edges) (hw : 0 < G.weight e) :
    let p := endpoints G ⟨e, he⟩
    occupation G hu hA hW e * (1 - occupation G hu hA hW e) =
      G.weight e * message G hu hA hW (p.1, none) * message G hu hA hW (p.2, none) := by
  let p := endpoints G ⟨e, he⟩
  obtain ⟨hne, hp⟩ := endpoints_spec G ⟨e, he⟩
  change p.1 ≠ p.2 at hne
  change G.ends e = {p.1,p.2} at hp
  have ha : e ∈ incidentEdges G p.1 := Finset.mem_filter.mpr ⟨he, by rw [hp]; simp⟩
  have hb : e ∈ incidentEdges G p.2 := Finset.mem_filter.mpr ⟨he, by rw [hp]; simp⟩
  change occupation G hu hA hW e * (1 - occupation G hu hA hW e) =
    G.weight e * message G hu hA hW (p.1, none) * message G hu hA hW (p.2, none)
  rw [rootMessage_eq_fullEndpoint G hu hA hW ha, rootMessage_eq_fullEndpoint G hu hA hW hb,
    occupation, dif_pos he]
  simp only [incomingState, otherEnd_of_endpoints G hp hne, otherEnd_swap_of_endpoints G hp hne]
  exact occupation_factorization hw (message_pos' G hu hA hW _) (message_pos' G hu hA hW _)

theorem occupation_le_weight_div_sq {e : E} (he : e ∈ G.edges) :
    occupation G hu hA hW e ≤ G.weight e / u^2 := by
  let p := endpoints G ⟨e, he⟩
  let a := message G hu hA hW (p.1,some e)
  let b := message G hu hA hW (p.2,some e)
  have h : 0 ≤ G.weight e * a * b := mul_nonneg
    (mul_nonneg (G.weight_nonneg e) (message_pos' G hu hA hW _).le) (message_pos' G hu hA hW _).le
  rw [occupation, dif_pos he]
  change edgeOccupation (G.weight e) a b ≤ _
  unfold edgeOccupation
  calc
    _ ≤ G.weight e * a * b := div_le_self h (le_add_of_nonneg_right h)
    _ ≤ G.weight e * (u⁻¹ * u⁻¹) := by
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left (mul_le_mul ?_ ?_ (message_pos' G hu hA hW _).le
        (inv_nonneg.mpr hu.le)) (G.weight_nonneg e)
      · exact (message_mem G hu hA hW _).2
      · exact (message_mem G hu hA hW _).2
    _ = _ := by rw [div_eq_mul_inv, pow_two, mul_inv_rev]

theorem rootMonomer_mem (v : V) :
    u * message G hu hA hW (v, none) ∈ Set.Ioc 0 1 := by
  exact ⟨mul_pos hu (message_pos' G hu hA hW _),
    (mul_le_mul_of_nonneg_left (message_mem G hu hA hW _).2 hu.le).trans_eq (mul_inv_cancel₀ hu.ne')⟩

theorem rootMonomer_deficit_le (v : V) :
    1 - u * message G hu hA hW (v, none) ≤ A / u^2 := by
  have h : 1 - u * message G hu hA hW (v, none) =
      ∑ e ∈ incidentEdges G v, occupation G hu hA hW e := by
    linarith only [occupation_slack G hu hA hW v]
  rw [h]
  calc
    _ ≤ ∑ e ∈ incidentEdges G v, G.weight e / u^2 :=
      Finset.sum_le_sum fun e he => occupation_le_weight_div_sq G hu hA hW (Finset.mem_filter.mp he).1
    _ ≤ _ := by
      rw [← Finset.sum_div]
      exact div_le_div_of_nonneg_right (hW v) (sq_nonneg u)

end Finite
end Graph
end Certificate.OverlapBelief

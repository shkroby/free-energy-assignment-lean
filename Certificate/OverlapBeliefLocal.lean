import Certificate.OverlapBeliefOccupations

/-! Local comparison of belief propagation and the exact deletion recursion. -/

open Finset
open scoped NNReal

namespace Certificate.OverlapBelief

section Graph

variable {V E : Type*} [DecidableEq V] [DecidableEq E]
variable (G : WeightedGraph V E)

/-- Up to the given depth, the nonbacktracking unfolding uses the same edges
as the vertex-deletion unfolding. This is the local tree condition needed
for the deterministic pressure estimate. -/
def walkCompatible : ℕ → Finset V → State V E → Prop
  | 0, _, _ => True
  | k+1, remain, q =>
    incomingEdges G q = Tree.incident G.ends remain G.edges q.1 ∧
    ∀ e ∈ incomingEdges G q,
      walkCompatible k (remain.erase q.1) (incomingState G q.1 e)

/-- Local tree condition at a root, including all retained graph vertices
before the first deletion. -/
def goodRoot (k : ℕ) (v : V) : Prop := walkCompatible G k G.vertices (v, none)

omit [DecidableEq E] in
private theorem otherEnd_pair {e : E} {v : V} (he : e ∈ G.edges) (hv : v ∈ G.ends e) :
    v ≠ Tree.otherEnd G.ends e v ∧ G.ends e = {v, Tree.otherEnd G.ends e v} := by
  let p := endpoints G ⟨e,he⟩
  obtain ⟨hp₀, hp₁⟩ := endpoints_spec G ⟨e,he⟩
  change p.1 ≠ p.2 at hp₀
  change G.ends e = {p.1,p.2} at hp₁
  rw [hp₁, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with hh | hh
  · rw [hh, otherEnd_of_endpoints G hp₁ hp₀]
    exact ⟨hp₀, hp₁⟩
  · rw [hh, otherEnd_swap_of_endpoints G hp₁ hp₀]
    exact ⟨hp₀.symm, hp₁.trans (Finset.pair_comm _ _)⟩

omit [DecidableEq E] in
private theorem incident_otherEnd {remain : Finset V} {v : V} {e : E}
    (he : e ∈ Tree.incident G.ends remain G.edges v) :
    Tree.otherEnd G.ends e v ∈ remain.erase v ∧
      (remain.erase v).erase (Tree.otherEnd G.ends e v) = remain \ G.ends e := by
  obtain ⟨heG, hv, hs⟩ := Finset.mem_filter.mp he
  obtain ⟨hne, hp⟩ := otherEnd_pair G heG hv
  refine ⟨Finset.mem_erase.mpr ⟨hne.symm, hs (by rw [hp]; simp)⟩, ?_⟩
  ext a
  simp only [Finset.mem_erase, hp, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
  tauto

omit [DecidableEq E] in
private theorem sum_weight_incident_le {A : ℝ} (hW : IncidentWeightBound G A)
    (s : Finset V) (v : V) :
    ∑ e ∈ Tree.incident G.ends s G.edges v, G.weight e ≤ A := by
  refine (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun e _ _ => G.weight_nonneg e)).trans (hW v)
  intro e he
  obtain ⟨heG,hv,_⟩ := Finset.mem_filter.mp he
  exact Finset.mem_filter.mpr ⟨heG,hv⟩

/-- The quotient of two finite matching partition functions obeys exactly
the incident-edge recursion after deleting the root. -/
theorem deletionRatio_recursion_otherEnd {u : ℝ} (hu : 0 < u) {s : Finset V} {v : V}
    (hv : v ∈ s) :
    Tree.deletionRatio G.ends s G.edges G.weight u v =
      (u + ∑ e ∈ Tree.incident G.ends s G.edges v, G.weight e *
        Tree.deletionRatio G.ends (s.erase v) G.edges G.weight u (Tree.otherEnd G.ends e v))⁻¹ := by
  rw [Tree.deletionRatio_recursion G.ends G.edges G.weight G.weight_nonneg hu G.ends_card hv]
  congr 2
  refine Finset.sum_congr rfl fun e he => ?_
  unfold Tree.deletionRatio
  rw [(incident_otherEnd G he).2]

theorem deletionRatio_mem {u A : ℝ} (hu : 0 < u) (_hA : 0 ≤ A)
    (hW : IncidentWeightBound G A) {s : Finset V} {v : V} (hv : v ∈ s) :
    Tree.deletionRatio G.ends s G.edges G.weight u v ∈ Set.Icc (u + A/u)⁻¹ u⁻¹ := by
  have hU := Tree.deletionRatio_pos_le G.ends G.edges G.weight G.weight_nonneg hu G.ends_card hv
  refine ⟨?_, hU.2⟩
  rw [deletionRatio_recursion_otherEnd G hu hv]
  have hD (e : E) (he : e ∈ Tree.incident G.ends s G.edges v) :=
    Tree.deletionRatio_pos_le G.ends G.edges G.weight G.weight_nonneg hu G.ends_card (incident_otherEnd G he).1
  apply inv_anti₀ (add_pos_of_pos_of_nonneg hu (Finset.sum_nonneg fun e he =>
    mul_nonneg (G.weight_nonneg e) (hD e he).1.le))
  refine add_le_add le_rfl ?_
  calc
    _ ≤ ∑ e ∈ Tree.incident G.ends s G.edges v, G.weight e * u⁻¹ :=
      Finset.sum_le_sum fun e he => mul_le_mul_of_nonneg_left (hD e he).2 (G.weight_nonneg e)
    _ = (∑ e ∈ Tree.incident G.ends s G.edges v, G.weight e) * u⁻¹ :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ A / u := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (sum_weight_incident_le G hW s v) (inv_nonneg.mpr hu.le)

private theorem norm_log_sub_log_of_mem {u A x y : ℝ} (hu : 0 < u) (hA : 0 ≤ A)
    (hx : x ∈ Set.Icc (u+A/u)⁻¹ u⁻¹) (hy : y ∈ Set.Icc (u+A/u)⁻¹ u⁻¹) :
    ‖Real.log x - Real.log y‖ ≤ A/u^2 := by
  have hu' : 0 < u + A/u := add_pos_of_pos_of_nonneg hu (div_nonneg hA hu.le)
  have hl : 0 < (u + A/u)⁻¹ := inv_pos.mpr hu'
  have hX₁ := Real.log_le_log hl hx.1
  have hX₂ := Real.log_le_log (hl.trans_le hx.1) hx.2
  have hY₁ := Real.log_le_log hl hy.1
  have hY₂ := Real.log_le_log (hl.trans_le hy.1) hy.2
  simp only [Real.log_inv] at hX₁ hX₂ hY₁ hY₂
  have hWidth : Real.log (u + A/u) - Real.log u ≤ A/u^2 := by
    rw [← Real.log_div hu'.ne' hu.ne']
    have h : Real.log ((u + A/u)/u) ≤ (u + A/u)/u - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hu' hu)
    have heq : (u+A/u)/u - 1 = A/u^2 := by field_simp [hu.ne']; ring
    exact h.trans_eq heq
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith only [hX₁,hY₂,hWidth], by linarith only [hX₂,hY₁,hWidth]⟩

variable [Fintype V] [Fintype E]

set_option maxHeartbeats 600000 in
/-- On a compatible depth-k neighborhood, the logarithmic deletion message
and the belief-propagation message differ by at most the contraction raised
to depth k times the initial logarithmic spread. -/
theorem norm_log_deletionRatio_sub_logMessage_le {u A : ℝ} (hu : 0 < u) (hA : 0 ≤ A)
    (hW : IncidentWeightBound G A) {k : ℕ} {s : Finset V} {q : State V E}
    (hq : q.1 ∈ s) (hCompat : walkCompatible G k s q) :
    ‖Real.log (Tree.deletionRatio G.ends s G.edges G.weight u q.1) -
      Real.log (message G hu hA hW q)‖ ≤
      (contractionRate u A : ℝ)^k * (A/u^2) := by
  induction k generalizing s q with
  | zero =>
    simp only [pow_zero, one_mul]
    exact norm_log_sub_log_of_mem hu hA (deletionRatio_mem G hu hA hW hq)
      (message_mem G hu hA hW q)
  | succ k ih =>
    obtain ⟨hS, hRest⟩ := hCompat
    let f (e : E) := Tree.deletionRatio G.ends (s.erase q.1) G.edges G.weight u
      (Tree.otherEnd G.ends e q.1)
    let g (e : E) := message G hu hA hW (incomingState G q.1 e)
    have hf (e : E) (he : e ∈ incomingEdges G q) : f e ∈
        Set.Icc (u + A / u)⁻¹ u⁻¹ :=
      deletionRatio_mem G hu hA hW (incident_otherEnd G (hS ▸ he)).1
    have hp (e : E) (he : e ∈ incomingEdges G q) : 0 < f e :=
      (inv_pos.mpr (add_pos_of_pos_of_nonneg hu (div_nonneg hA hu.le))).trans_le (hf e he).1
    have hExact : Real.log (Tree.deletionRatio G.ends s G.edges G.weight u q.1) =
        logUpdate u (incomingEdges G q) G.weight (fun e => Real.log (f e)) := by
      rw [deletionRatio_recursion_otherEnd G hu hq, ← hS, Real.log_inv]
      unfold logUpdate
      apply congrArg (fun x : ℝ => -Real.log (u+x))
      refine Finset.sum_congr rfl fun e he => ?_
      rw [Real.exp_log (hp e he)]
    have hBP : Real.log (message G hu hA hW q) =
        logUpdate u (incomingEdges G q) G.weight (fun e => Real.log (g e)) := by
      rw [message_recursion G hu hA hW q, Real.log_inv]
      unfold logUpdate
      simp only [g, message, Real.log_exp]
    have hX (e : E) (he : e ∈ incomingEdges G q) : Real.log (f e) ≤ -Real.log u := by
      rw [← Real.log_inv]
      exact Real.log_le_log (hp e he) (hf e he).2
    have hY (e : E) : Real.log (g e) ≤ -Real.log u := by
      rw [← Real.log_inv]
      exact Real.log_le_log (Real.exp_pos _) (message_mem G hu hA hW _).2
    have hChild (e : E) (he : e ∈ incomingEdges G q) :
        ‖Real.log (f e) - Real.log (g e)‖ ≤ (contractionRate u A : ℝ)^k * (A/u^2) := by
      have he' : e ∈ Tree.incident G.ends s G.edges q.1 := hS ▸ he
      have hs : (incomingState G q.1 e).1 ∈ s.erase q.1 := (incident_otherEnd G he').1
      exact ih (s := s.erase q.1) (q := incomingState G q.1 e) hs (hRest e he)
    rw [hExact, hBP]
    have hL : 0 ≤ (contractionRate u A : ℝ)^k * (A/u^2) :=
      mul_nonneg (pow_nonneg (contractionRate u A).coe_nonneg _) (div_nonneg hA (sq_nonneg _))
    have hb := norm_logUpdate_sub_le (incomingEdges G q) hu hA hL
      G.weight (fun e => Real.log (f e)) (fun e => Real.log (g e))
      (fun i _ => G.weight_nonneg i) (sum_weight_incoming_le G hW q) hX (fun i _ => hY i) hChild
    have hRate : Real.exp (-Real.log u) * A / (u + Real.exp (-Real.log u) * A) =
        (contractionRate u A : ℝ) := by
      rw [coe_contractionRate hu hA, Real.exp_neg, Real.exp_log hu]
      have hd : 0 < u + u⁻¹ * A := add_pos_of_pos_of_nonneg hu (mul_nonneg (inv_nonneg.mpr hu.le) hA)
      have he : 0 < u^2+A := by positivity
      field_simp [hu.ne', hd.ne', he.ne']
    rw [hRate] at hb
    exact hb.trans_eq (by rw [pow_succ]; ring)

private theorem norm_exp_sub_exp_le_on_Iic_zero {a b : ℝ} (ha : a ≤ 0) (hb : b ≤ 0) :
    ‖Real.exp a - Real.exp b‖ ≤ ‖a-b‖ := by
  have h := (convex_Iic (0 : ℝ)).norm_image_sub_le_of_norm_deriv_le
    (fun x _ => (Real.hasDerivAt_exp x).differentiableAt)
    (C := 1) (fun x (hx : x ≤ 0) => by
      rw [(Real.hasDerivAt_exp x).deriv, Real.norm_of_nonneg (Real.exp_nonneg _)]
      exact Real.exp_le_one_iff.mpr hx) hb ha
  simpa only [one_mul] using h

set_option maxHeartbeats 600000 in
/-- The corresponding monomer probabilities are at least as close as the
logarithmic messages. -/
theorem norm_rootMonomer_sub_exact_le {u A : ℝ} (hu : 0 < u) (hA : 0 ≤ A)
    (hW : IncidentWeightBound G A) {k : ℕ} {v : V}
    (hv : v ∈ G.vertices) (hg : goodRoot G k v) :
    ‖u * Tree.deletionRatio G.ends G.vertices G.edges G.weight u v -
      u * message G hu hA hW (v, none)‖ ≤
      (contractionRate u A : ℝ)^k * (A/u^2) := by
  let x := Tree.deletionRatio G.ends G.vertices G.edges G.weight u v
  let y := message G hu hA hW (v, none)
  have hX := Tree.deletionRatio_pos_le G.ends G.edges G.weight G.weight_nonneg hu G.ends_card hv
  have hY := rootMonomer_mem G hu hA hW v
  have hx : 0 < u * x := mul_pos hu hX.1
  have hxu : u * x ≤ 1 := (mul_le_mul_of_nonneg_left hX.2 hu.le).trans_eq (mul_inv_cancel₀ hu.ne')
  have hxl : Real.log (u*x) ≤ 0 := Real.log_nonpos hx.le hxu
  have hyl : Real.log (u*y) ≤ 0 := Real.log_nonpos hY.1.le hY.2
  have hc := norm_exp_sub_exp_le_on_Iic_zero hxl hyl
  have hym : 0 < y := Real.exp_pos _
  rw [Real.exp_log hx, Real.exp_log hY.1,
    Real.log_mul hu.ne' hX.1.ne', Real.log_mul hu.ne' hym.ne'] at hc
  have he : Real.log u + Real.log x - (Real.log u + Real.log y) = Real.log x - Real.log y := by ring
  rw [he] at hc
  exact hc.trans (norm_log_deletionRatio_sub_logMessage_le G hu hA hW (s := G.vertices) (q := (v, none)) hv hg)

end Graph
end Certificate.OverlapBelief

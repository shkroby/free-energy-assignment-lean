import Certificate.SoftPressure
import Certificate.FiniteRootBounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Topology.MetricSpace.Contracting

/-! Bounded-weight belief propagation at positive monomer activity. -/

open Finset Function Set
open scoped NNReal Topology

namespace Certificate.OverlapBelief

/-- A single logarithmic cavity update. -/
noncomputable def logUpdate {I : Type*} (u : ℝ) (s : Finset I) (w x : I → ℝ) : ℝ :=
  -Real.log (u + ∑ i ∈ s, w i * Real.exp (x i))

/-- The absolute logarithmic slope is at most the matched mass, uniformly over
all admissible log messages. -/
theorem norm_logUpdate_sub_le {I : Type*} (s : Finset I) {u A c L : ℝ}
    (hu : 0 < u) (hA : 0 ≤ A) (hL : 0 ≤ L) (w x y : I → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hs : ∑ i ∈ s, w i ≤ A)
    (hx : ∀ i ∈ s, x i ≤ c) (hy : ∀ i ∈ s, y i ≤ c)
    (hxy : ∀ i ∈ s, ‖x i - y i‖ ≤ L) :
    ‖logUpdate u s w x - logUpdate u s w y‖ ≤
      (Real.exp c * A / (u + Real.exp c * A)) * L := by
  let a (t : ℝ) (i : I) := y i + t * (x i - y i)
  let b (t : ℝ) := ∑ i ∈ s, w i * Real.exp (a t i)
  let D (t : ℝ) := ∑ i ∈ s, w i * Real.exp (a t i) * (x i - y i)
  let g (t : ℝ) := -Real.log (u + b t)
  have hb (t : ℝ) : 0 ≤ b t := Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (Real.exp_nonneg _)
  have hd (t : ℝ) : 0 < u + b t := add_pos_of_pos_of_nonneg hu (hb t)
  have hDeriv (t : ℝ) : HasDerivAt g (-(D t / (u + b t))) t := by
    have ha (i : I) : HasDerivAt (fun t => a t i) (x i - y i) t := by
      change HasDerivAt (fun t : ℝ => y i + t * (x i - y i)) (x i - y i) t
      simpa only [id_eq, one_mul] using (((hasDerivAt_id t).mul_const (x i - y i)).const_add (y i))
    have hTerm (i : I) :
        HasDerivAt (fun t => w i * Real.exp (a t i))
          (w i * Real.exp (a t i) * (x i - y i)) t := by
      refine ((ha i).exp.const_mul (w i)).congr_deriv ?_
      ring
    have hB : HasDerivAt b (D t) t := HasDerivAt.fun_sum fun i _ => hTerm i
    exact ((hB.const_add u).log (hd t).ne').neg
  have hBnd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : b t ≤ Real.exp c * A := by
    have ha (i : I) (hi : i ∈ s) : a t i ≤ c := by
      calc
        a t i = (1 - t) * y i + t * x i := by dsimp [a]; ring
        _ ≤ (1 - t) * c + t * c := add_le_add
          (mul_le_mul_of_nonneg_left (hy i hi) (sub_nonneg.mpr ht.2))
          (mul_le_mul_of_nonneg_left (hx i hi) ht.1)
        _ = c := by ring
    calc
      _ ≤ ∑ i ∈ s, w i * Real.exp c := Finset.sum_le_sum fun i hi =>
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (ha i hi)) (hw i hi)
      _ = Real.exp c * ∑ i ∈ s, w i := by rw [← Finset.sum_mul, mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left hs (Real.exp_nonneg _)
  have hND (t : ℝ) : ‖D t‖ ≤ b t * L := by
    calc
      _ ≤ ∑ i ∈ s, ‖w i * Real.exp (a t i) * (x i - y i)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ s, (w i * Real.exp (a t i)) * L := by
        apply Finset.sum_le_sum
        intro i hi
        have hp := mul_nonneg (hw i hi) (Real.exp_nonneg (a t i))
        rw [norm_mul, Real.norm_of_nonneg hp]
        exact mul_le_mul_of_nonneg_left (hxy i hi) hp
      _ = _ := (Finset.sum_mul _ _ _).symm
  have hSlope (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖deriv g t‖ ≤ (Real.exp c * A / (u + Real.exp c * A)) * L := by
    rw [(hDeriv t).deriv, norm_neg, norm_div, Real.norm_of_nonneg (hd t).le]
    have hr : b t / (u + b t) ≤ Real.exp c * A / (u + Real.exp c * A) := by
      apply (div_le_div_iff₀ (hd t) (add_pos_of_pos_of_nonneg hu (mul_nonneg (Real.exp_nonneg _) hA))).mpr
      have h := mul_le_mul_of_nonneg_right (hBnd t ht) hu.le
      nlinarith only [h]
    calc
      _ ≤ (b t * L) / (u + b t) := div_le_div_of_nonneg_right (hND t) (hd t).le
      _ = (b t / (u + b t)) * L := by simp only [div_eq_mul_inv]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hr hL
  have hg := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
    (fun t _ => (hDeriv t).differentiableAt) hSlope (left_mem_Icc.mpr zero_le_one)
    (right_mem_Icc.mpr zero_le_one)
  have hx' : g 1 = logUpdate u s w x := by
    have ha (i : I) : a 1 i = x i := by dsimp [a]; ring
    simp only [g, b, ha, logUpdate]
  have hy' : g 0 = logUpdate u s w y := by simp only [g, b, a, zero_mul, add_zero, logUpdate]
  simpa only [hx', hy', sub_zero, norm_one, mul_one] using hg

private theorem norm_min_sub_min_le (c x y : ℝ) :
    ‖min x c - min y c‖ ≤ ‖x - y‖ := by
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  calc
    _ ≤ max |x-y| |c-c| := abs_min_sub_min_le_max x c y c
    _ = _ := by rw [sub_self, abs_zero]; exact max_eq_left (abs_nonneg _)

theorem lipschitzWith_log_exp_add {B : ℝ} (hB : 0 ≤ B) :
    LipschitzWith 1 (fun t : ℝ => Real.log (Real.exp t + B)) := by
  have h (t : ℝ) :
      HasDerivAt (fun t : ℝ => Real.log (Real.exp t + B)) (Real.exp t / (Real.exp t + B)) t :=
    ((Real.hasDerivAt_exp t).add_const B).log
      (add_pos_of_pos_of_nonneg (Real.exp_pos t) hB).ne'
  apply lipschitzWith_of_nnnorm_deriv_le (fun t => (h t).differentiableAt)
  intro t
  apply NNReal.coe_le_coe.mp
  rw [NNReal.coe_one, coe_nnnorm, (h t).deriv, Real.norm_of_nonneg (by positivity)]
  exact (div_le_one (add_pos_of_pos_of_nonneg (Real.exp_pos t) hB)).mpr
    (le_add_of_nonneg_right hB)

section Graph

variable {V E : Type*} [DecidableEq V] [DecidableEq E]
variable (G : WeightedGraph V E)

/-- A root has no excluded edge. A directed message excludes its outgoing
edge, so the same update handles roots and directed messages. -/
abbrev State (V E : Type*) := V × Option E

def incidentEdges (v : V) : Finset E := G.edges.filter fun e => v ∈ G.ends e

def incomingEdges (q : State V E) : Finset E :=
  match q.2 with
  | none => incidentEdges G q.1
  | some e => (incidentEdges G q.1).erase e

noncomputable def incomingState (v : V) (e : E) : State V E :=
  (Tree.otherEnd G.ends e v, some e)

/-- Total incident weight is bounded uniformly over vertices. -/
def IncidentWeightBound (A : ℝ) : Prop :=
  ∀ v, ∑ e ∈ incidentEdges G v, G.weight e ≤ A

theorem sum_weight_incoming_le {A : ℝ} (hA : IncidentWeightBound G A) (q : State V E) :
    ∑ e ∈ incomingEdges G q, G.weight e ≤ A := by
  obtain ⟨v, _ | e⟩ := q
  · exact hA v
  · exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      (fun f _ _ => G.weight_nonneg f)).trans (hA v)

/-- A capped logarithmic update, defined on the whole Euclidean space. -/
noncomputable def update (u c : ℝ) (x : State V E → ℝ) (q : State V E) : ℝ :=
  logUpdate u (incomingEdges G q) G.weight (fun e => min (x (incomingState G q.1 e)) c)

noncomputable def contractionRate (u A : ℝ) : ℝ≥0 :=
  Real.toNNReal (A / (u ^ 2 + A))

theorem coe_contractionRate {u A : ℝ} (hu : 0 < u) (hA : 0 ≤ A) :
    (contractionRate u A : ℝ) = A / (u ^ 2 + A) :=
  Real.coe_toNNReal _ (div_nonneg hA (by positivity))

theorem contractionRate_lt_one {u A : ℝ} (hu : 0 < u) (hA : 0 ≤ A) :
    contractionRate u A < 1 := by
  apply NNReal.coe_lt_coe.mp
  rw [coe_contractionRate hu hA, NNReal.coe_one, div_lt_one (by positivity)]
  exact lt_add_of_pos_left _ (sq_pos_of_pos hu)

theorem update_contracting [Fintype V] [Fintype E] {u A : ℝ}
    (hu : 0 < u) (hA : 0 ≤ A) (hWeight : IncidentWeightBound G A) :
    ContractingWith (contractionRate u A) (update G u (-Real.log u)) := by
  refine ⟨contractionRate_lt_one hu hA, lipschitzWith_iff_dist_le_mul.mpr fun x y => ?_⟩
  rw [dist_eq_norm, dist_eq_norm, coe_contractionRate hu hA]
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro q
  have h := norm_logUpdate_sub_le (incomingEdges G q) hu hA (norm_nonneg (x-y)) G.weight
    (fun e => min (x (incomingState G q.1 e)) (-Real.log u))
    (fun e => min (y (incomingState G q.1 e)) (-Real.log u))
    (fun e _ => G.weight_nonneg e) (sum_weight_incoming_le G hWeight q)
    (fun _ _ => min_le_right _ _) (fun _ _ => min_le_right _ _)
    (fun e _ => (norm_min_sub_min_le _ _ _).trans (norm_le_pi_norm (x-y) _))
  have hc : Real.exp (-Real.log u) * A / (u + Real.exp (-Real.log u) * A) = A / (u^2 + A) := by
    rw [Real.exp_neg, Real.exp_log hu]
    have hd : 0 < u + u⁻¹ * A := add_pos_of_pos_of_nonneg hu (mul_nonneg (inv_nonneg.mpr hu.le) hA)
    have he : 0 < u^2 + A := by positivity
    field_simp [hu.ne', hd.ne', he.ne']
  rw [hc] at h
  exact h

theorem update_le_upper {u c : ℝ} (hu : 0 < u) (x : State V E → ℝ) (q : State V E) :
    update G u c x q ≤ -Real.log u := by
  unfold update logUpdate
  have h : u ≤ u + ∑ e ∈ incomingEdges G q, G.weight e *
      Real.exp (min (x (incomingState G q.1 e)) c) :=
    le_add_of_nonneg_right (Finset.sum_nonneg fun e _ => mul_nonneg (G.weight_nonneg e) (Real.exp_nonneg _))
  exact neg_le_neg (Real.log_le_log hu h)

theorem update_ge_lower {u A : ℝ} (hu : 0 < u) (hW : IncidentWeightBound G A)
    (x : State V E → ℝ) (q : State V E) :
    -Real.log (u + A / u) ≤ update G u (-Real.log u) x q := by
  let D := ∑ e ∈ incomingEdges G q, G.weight e * Real.exp (min (x (incomingState G q.1 e)) (-Real.log u))
  have hD : 0 ≤ D := Finset.sum_nonneg fun e _ => mul_nonneg (G.weight_nonneg e) (Real.exp_nonneg _)
  have h : D ≤ A / u := by
    have hc : Real.exp (-Real.log u) = u⁻¹ := by rw [Real.exp_neg, Real.exp_log hu]
    calc
      _ ≤ ∑ e ∈ incomingEdges G q, G.weight e * u⁻¹ := by
        apply Finset.sum_le_sum
        intro e _
        refine mul_le_mul_of_nonneg_left ?_ (G.weight_nonneg e)
        rw [← hc]
        exact Real.exp_le_exp.mpr (min_le_right _ _)
      _ = (∑ e ∈ incomingEdges G q, G.weight e) * u⁻¹ := (Finset.sum_mul _ _ _).symm
      _ ≤ _ := by
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (sum_weight_incoming_le G hW q) (inv_nonneg.mpr hu.le)
  exact neg_le_neg (Real.log_le_log (add_pos_of_pos_of_nonneg hu hD) (add_le_add le_rfl h))

/-- The logarithmic belief-propagation messages. -/
noncomputable def logMessage [Fintype V] [Fintype E] {u A : ℝ}
    (hu : 0 < u) (hA : 0 ≤ A) (hWeight : IncidentWeightBound G A) : State V E → ℝ :=
  (update_contracting G hu hA hWeight).fixedPoint

theorem logMessage_fixed [Fintype V] [Fintype E] {u A : ℝ}
    (hu : 0 < u) (hA : 0 ≤ A) (hWeight : IncidentWeightBound G A) :
    update G u (-Real.log u) (logMessage G hu hA hWeight) = logMessage G hu hA hWeight :=
  (update_contracting G hu hA hWeight).fixedPoint_isFixedPt

/-- Exponentiating the fixed point gives the cavity and root messages on
the same positive reciprocal scale. -/
noncomputable def message [Fintype V] [Fintype E] {u A : ℝ}
    (hu : 0 < u) (hA : 0 ≤ A) (hWeight : IncidentWeightBound G A) (q : State V E) : ℝ :=
  Real.exp (logMessage G hu hA hWeight q)

theorem message_mem [Fintype V] [Fintype E] {u A : ℝ}
    (hu : 0 < u) (hA : 0 ≤ A) (hWeight : IncidentWeightBound G A) (q : State V E) :
    message G hu hA hWeight q ∈ Icc (u + A/u)⁻¹ u⁻¹ := by
  have h := congrFun (logMessage_fixed G hu hA hWeight) q
  have hL := update_ge_lower G hu hWeight (logMessage G hu hA hWeight) q
  have hU := update_le_upper G (c := -Real.log u) hu (logMessage G hu hA hWeight) q
  rw [h] at hL hU
  have lo : Real.exp (-Real.log (u + A/u)) = (u + A/u)⁻¹ := by
    rw [Real.exp_neg, Real.exp_log (add_pos_of_pos_of_nonneg hu (div_nonneg hA hu.le))]
  have hi : Real.exp (-Real.log u) = u⁻¹ := by rw [Real.exp_neg, Real.exp_log hu]
  exact ⟨lo ▸ Real.exp_le_exp.mpr hL, hi ▸ Real.exp_le_exp.mpr hU⟩

theorem message_recursion [Fintype V] [Fintype E] {u A : ℝ}
    (hu : 0 < u) (hA : 0 ≤ A) (hWeight : IncidentWeightBound G A) (q : State V E) :
    message G hu hA hWeight q =
      (u + ∑ e ∈ incomingEdges G q, G.weight e *
        message G hu hA hWeight (incomingState G q.1 e))⁻¹ := by
  let x := logMessage G hu hA hWeight
  have hfix : update G u (-Real.log u) x = x := logMessage_fixed G hu hA hWeight
  have hx (q' : State V E) : x q' ≤ -Real.log u := by
    rw [← congrFun hfix q']
    exact update_le_upper G hu x q'
  have h : logUpdate u (incomingEdges G q) G.weight
      (fun e => min (x (incomingState G q.1 e)) (-Real.log u)) = x q := congrFun hfix q
  unfold logUpdate at h
  have hD : 0 < u + ∑ e ∈ incomingEdges G q, G.weight e * Real.exp (x (incomingState G q.1 e)) :=
    add_pos_of_pos_of_nonneg hu (Finset.sum_nonneg fun e _ =>
      mul_nonneg (G.weight_nonneg e) (Real.exp_nonneg _))
  have hc (q' : State V E) : min (x q') (-Real.log u) = x q' := min_eq_left (hx q')
  simp_rw [hc] at h
  change Real.exp (x q) = _
  rw [← h, Real.exp_neg, Real.exp_log hD]
  rfl

theorem existsUnique_positive_message [Fintype V] [Fintype E] {u A : ℝ}
    (hu : 0 < u) (hA : 0 ≤ A) (hWeight : IncidentWeightBound G A) :
    ∃! h : State V E → ℝ, (∀ q, 0 < h q) ∧
      ∀ q, h q = (u + ∑ e ∈ incomingEdges G q, G.weight e * h (incomingState G q.1 e))⁻¹ := by
  refine ⟨message G hu hA hWeight, ⟨fun q => Real.exp_pos _, message_recursion G hu hA hWeight⟩, ?_⟩
  intro f hf
  let x (q : State V E) := Real.log (f q)
  have hpos (q : State V E) :
      0 < u + ∑ e ∈ incomingEdges G q, G.weight e * f (incomingState G q.1 e) :=
    add_pos_of_pos_of_nonneg hu (Finset.sum_nonneg fun e _ =>
      mul_nonneg (G.weight_nonneg e) (hf.1 _).le)
  have hx (q : State V E) : x q ≤ -Real.log u := by
    dsimp [x]
    rw [hf.2 q, Real.log_inv]
    exact neg_le_neg (Real.log_le_log hu (le_add_of_nonneg_right
      (Finset.sum_nonneg fun e _ => mul_nonneg (G.weight_nonneg e) (hf.1 _).le)))
  have hfix : IsFixedPt (update G u (-Real.log u)) x := by
    change update G u (-Real.log u) x = x
    funext q
    unfold update logUpdate
    have hc (q' : State V E) : min (x q') (-Real.log u) = x q' := min_eq_left (hx q')
    have h (q' : State V E) : Real.exp (x q') = f q' := Real.exp_log (hf.1 q')
    simp_rw [hc, h]
    change _ = Real.log (f q)
    rw [hf.2 q, Real.log_inv]
  have hh : x = logMessage G hu hA hWeight :=
    (update_contracting G hu hA hWeight).fixedPoint_unique hfix
  funext q
  change f q = Real.exp (logMessage G hu hA hWeight q)
  rw [← congrFun hh q]
  exact (Real.exp_log (hf.1 q)).symm

end Graph
end Certificate.OverlapBelief

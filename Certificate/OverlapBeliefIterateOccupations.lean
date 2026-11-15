import Certificate.OverlapBeliefIterate
import Certificate.OverlapBeliefOccupations
import Mathlib.Analysis.SpecialFunctions.Sigmoid

/-! Uniform approximation of the BP occupation by a finite-depth test. -/

open Finset Set

namespace Certificate.OverlapBelief

theorem norm_sigmoid_sub_sigmoid_le (a b : ℝ) :
    ‖Real.sigmoid a - Real.sigmoid b‖ ≤ (1/4) * ‖a-b‖ := by
  apply (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
    (fun x _ => (Real.hasDerivAt_sigmoid x).differentiableAt) (C := 1/4) _ (mem_univ b) (mem_univ a)
  intro x _
  rw [(Real.hasDerivAt_sigmoid x).deriv, Real.norm_of_nonneg
    (mul_nonneg (Real.sigmoid_nonneg _) (sub_nonneg.mpr (Real.sigmoid_le_one _)))]
  nlinarith only [sq_nonneg (Real.sigmoid x - 1/2)]

theorem edgeOccupation_exp_eq_sigmoid {w : ℝ} (hw : 0 < w) (a b : ℝ) :
    edgeOccupation w (Real.exp a) (Real.exp b) = Real.sigmoid (Real.log w+a+b) := by
  rw [edgeOccupation, Real.sigmoid_def, Real.exp_neg, Real.exp_add, Real.exp_add, Real.exp_log hw]
  have h : 0 < w * Real.exp a * Real.exp b := by positivity
  field_simp [h.ne', (by positivity : 0 < 1 + w * Real.exp a * Real.exp b).ne']
  ring

variable {V E : Type*} [DecidableEq V] [DecidableEq E] (G : WeightedGraph V E)

/-- Occupation inferred from the two depth-k directed iterates at an incident
edge. Its value is independent of which endpoint is used. -/
noncomputable def incidentOccupationIterate (u : ℝ) (k : ℕ) (v : V) (e : E) : ℝ :=
  edgeOccupation (G.weight e) (Real.exp (logIterate G u k (v, some e)))
    (Real.exp (logIterate G u k (incomingState G v e)))

/-- The finite-depth edge test has geometric error in the depth, uniformly
over graphs with a common incident weight bound. -/
theorem norm_occIterate_sub_occupation_le [Fintype V] [Fintype E]
    {u A : ℝ} (hu : 0 < u) (hA : 0 ≤ A) (hW : IncidentWeightBound G A)
    (k : ℕ) {v : V} {e : E} (he : e ∈ incidentEdges G v) (hw : 0 < G.weight e) :
    ‖incidentOccupationIterate G u k v e - occupation G hu hA hW e‖ ≤
      (1/2) * ((contractionRate u A : ℝ)^k * (A/u^2)) := by
  let s : State V E := (v, some e)
  let t : State V E := incomingState G v e
  let x := logIterate G u k
  let y := logMessage G hu hA hW
  rw [occupation_eq_for_incident G hu hA hW he, incidentOccupationIterate]
  change ‖edgeOccupation _ (Real.exp (x s)) (Real.exp (x t)) -
    edgeOccupation _ (Real.exp (y s)) (Real.exp (y t))‖ ≤ _
  rw [edgeOccupation_exp_eq_sigmoid hw, edgeOccupation_exp_eq_sigmoid hw]
  refine (norm_sigmoid_sub_sigmoid_le _ _).trans ?_
  have hb : Real.log (G.weight e) + x s + x t - (Real.log (G.weight e) + y s + y t) =
      (x s-y s)+(x t-y t) := by ring
  have hs := norm_logIterate_sub_logMessage_le G hu hA hW k s
  have ht := norm_logIterate_sub_logMessage_le G hu hA hW k t
  rw [hb]
  have h := norm_add_le (x s-y s) (x t-y t)
  linarith only [hs,ht,h]

end Certificate.OverlapBelief

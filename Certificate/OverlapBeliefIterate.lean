import Certificate.OverlapBeliefContraction

/-! Finite belief-propagation iterates with uniform error in the graph size. -/

open scoped BigOperators

namespace Certificate.OverlapBelief

variable {V E : Type*} [DecidableEq V] [DecidableEq E] (G : WeightedGraph V E)

/-- Belief propagation initialized with the empty-neighborhood message. -/
noncomputable def logIterate (u : ℝ) : ℕ → State V E → ℝ
  | 0 => fun _ => -Real.log u
  | k+1 => update G u (-Real.log u) (logIterate u k)

theorem logIterate_le {u : ℝ} (hu : 0 < u) (k : ℕ) (q : State V E) :
    logIterate G u k q ≤ -Real.log u := by
  cases k with
  | zero => exact le_rfl
  | succ k => exact update_le_upper G hu _ _

/-- The cap used to obtain a global contraction does not affect the iterates. -/
theorem logIterate_succ {u : ℝ} (hu : 0 < u) (k : ℕ) (q : State V E) :
    logIterate G u (k+1) q =
      logUpdate u (incomingEdges G q) G.weight
        (fun e => logIterate G u k (incomingState G q.1 e)) := by
  change logUpdate _ _ _ _ = logUpdate _ _ _ _
  simp only [min_eq_left (logIterate_le G hu k _)]

theorem norm_logIterate_sub_logMessage_le [Fintype V] [Fintype E]
    {u A : ℝ} (hu : 0 < u) (hA : 0 ≤ A) (hW : IncidentWeightBound G A)
    (k : ℕ) (q : State V E) :
    ‖logIterate G u k q - logMessage G hu hA hW q‖ ≤
      (contractionRate u A : ℝ)^k * (A/u^2) := by
  have h := update_contracting G hu hA hW
  have hdist (k : ℕ) :
      ‖logIterate G u k - logMessage G hu hA hW‖ ≤
        (contractionRate u A : ℝ)^k * (A/u^2) := by
    induction k with
    | zero =>
      simp only [pow_zero, one_mul]
      apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
      intro v
      change ‖-Real.log u - logMessage G hu hA hW v‖ ≤ A/u^2
      have hfix := congrFun (logMessage_fixed G hu hA hW) v
      have hmin := (update_ge_lower G hu hW (logMessage G hu hA hW) v).trans_eq hfix
      have hmax := hfix.symm.trans_le (update_le_upper G hu (logMessage G hu hA hW) v)
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hmax)]
      calc
        _ ≤ Real.log (u+A/u) - Real.log u := by linarith only [hmin]
        _ = Real.log ((u+A/u)/u) := (Real.log_div (by positivity) hu.ne').symm
        _ ≤ (u+A/u)/u-1 := Real.log_le_sub_one_of_pos (by positivity)
        _ = _ := by field_simp [hu.ne']; ring
    | succ k hk =>
      have hc := (lipschitzWith_iff_dist_le_mul.mp h.2) (logIterate G u k) (logMessage G hu hA hW)
      rw [dist_eq_norm, dist_eq_norm, logMessage_fixed G hu hA hW] at hc
      exact hc.trans ((mul_le_mul_of_nonneg_left hk (by positivity)).trans_eq (by rw [pow_succ]; ring))
  exact (norm_le_pi_norm (logIterate G u k - logMessage G hu hA hW) q).trans (hdist k)

end Certificate.OverlapBelief

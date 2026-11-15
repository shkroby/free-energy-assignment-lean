import Certificate.OverlapBeliefOccupations
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Continuity of the cavity messages and the envelope derivative. -/

open Filter Finset Set
open scoped Topology

namespace Certificate.OverlapBelief

section Graph

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
variable (G : WeightedGraph V E)

omit [Fintype V] [Fintype E] in
theorem continuous_update_logFugacity (x : State V E → ℝ) :
    Continuous (fun t : ℝ => update G (Real.exp t) (-Real.log (Real.exp t)) x) := by
  apply continuous_pi
  intro q
  let g (t : ℝ) := Real.exp t + ∑ e ∈ incomingEdges G q, G.weight e *
    Real.exp (min (x (incomingState G q.1 e)) (-t))
  have h : Continuous g := Real.continuous_exp.add (continuous_finsetSum _ fun e _ =>
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.min continuous_neg)))
  have hp (t : ℝ) : 0 < g t := add_pos_of_pos_of_nonneg (Real.exp_pos t)
    (Finset.sum_nonneg fun e _ => mul_nonneg (G.weight_nonneg e) (Real.exp_nonneg _))
  have hg : Continuous (fun t => -Real.log (g t)) := (h.log (fun t => (hp t).ne')).neg
  simpa only [update, logUpdate, Real.log_exp, g] using hg

/-- The unique message varies continuously with log fugacity. -/
theorem continuous_logMessage {A : ℝ} (hA : 0 ≤ A) (hW : IncidentWeightBound G A) :
    Continuous (fun t : ℝ => logMessage G (Real.exp_pos t) hA hW) := by
  rw [continuous_iff_continuousAt]
  intro t
  let x := logMessage G (Real.exp_pos t) hA hW
  let U (s : ℝ) := update G (Real.exp s) (-Real.log (Real.exp s))
  let r (s : ℝ) := A / (Real.exp s ^ 2 + A)
  have ht : U t x = x := logMessage_fixed G (Real.exp_pos t) hA hW
  have hpos (s : ℝ) : 0 < Real.exp s ^ 2 + A :=
    add_pos_of_pos_of_nonneg (sq_pos_of_pos (Real.exp_pos s)) hA
  have hr : Continuous r := continuous_const.div ((Real.continuous_exp.pow 2).add continuous_const)
    (fun s => (hpos s).ne')
  have hrt : 0 < 1-r t := sub_pos.mpr ((div_lt_one (hpos t)).mpr (lt_add_of_pos_left _ (sq_pos_of_pos (Real.exp_pos t))))
  have hU : ContinuousAt (fun s => U s x) t := (continuous_update_logFugacity G x).continuousAt
  have hUt : Tendsto (fun s => dist x (U s x)) (𝓝 t) (𝓝 0) := by
    have hc : Tendsto (fun _ : ℝ => x) (𝓝 t) (𝓝 x) := tendsto_const_nhds
    have h := hc.dist hU.tendsto
    rwa [ht, dist_self] at h
  have hbound : Tendsto (fun s => dist x (U s x) / (1-r s)) (𝓝 t) (𝓝 0) := by
    have hden : Tendsto (fun s => 1-r s) (𝓝 t) (𝓝 (1-r t)) :=
      tendsto_const_nhds.sub hr.continuousAt.tendsto
    have h := hUt.div hden hrt.ne'
    change Tendsto (fun s => dist x (U s x) / (1-r s)) (𝓝 t) (𝓝 (0 / (1-r t))) at h
    rwa [zero_div] at h
  apply tendsto_iff_dist_tendsto_zero.mpr
  refine squeeze_zero (fun _ => dist_nonneg) (fun s => ?_) hbound
  have hf := (update_contracting G (Real.exp_pos s) hA hW).dist_fixedPoint_le x
  rw [coe_contractionRate (Real.exp_pos s) hA] at hf
  change dist (logMessage G (Real.exp_pos s) hA hW) x ≤ _
  rw [dist_comm]
  exact hf

theorem continuous_message {A : ℝ} (hA : 0 ≤ A) (hW : IncidentWeightBound G A) (q : State V E) :
    Continuous (fun t : ℝ => message G (Real.exp_pos t) hA hW q) :=
  Real.continuous_exp.comp ((continuous_apply q).comp (continuous_logMessage G hA hW))

theorem continuous_rootMonomer {A : ℝ} (hA : 0 ≤ A) (hW : IncidentWeightBound G A) (v : V) :
    Continuous (fun t : ℝ => Real.exp t * message G (Real.exp_pos t) hA hW (v, none)) :=
  Real.continuous_exp.mul (continuous_message G hA hW (v, none))

end Graph

/-- An affine objective with a continuous optimal slope has the envelope
derivative. The two optimizer inequalities supply the squeeze. -/
theorem hasDerivAt_of_affine_envelope {φ q : ℝ → ℝ} {t : ℝ}
    (hq : ContinuousAt q t)
    (hLo : ∀ s : ℝ, φ t + (s-t) * q t ≤ φ s)
    (hHi : ∀ s : ℝ, φ s ≤ φ t + (s-t) * q s) :
    HasDerivAt φ (q t) t := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  have hq' : Tendsto q (𝓝[≠] t) (𝓝 (q t)) := hq.tendsto.mono_left nhdsWithin_le_nhds
  have hMin : Tendsto (fun s => min (q t) (q s)) (𝓝[≠] t) (𝓝 (q t)) := by
    simpa only [min_self] using (tendsto_const_nhds (x := q t)).min hq'
  have hMax : Tendsto (fun s => max (q t) (q s)) (𝓝[≠] t) (𝓝 (q t)) := by
    simpa only [max_self] using (tendsto_const_nhds (x := q t)).max hq'
  have h (s : ℝ) (hs : s ≠ t) : min (q t) (q s) ≤ slope φ t s ∧
      slope φ t s ≤ max (q t) (q s) := by
    rw [slope_def_field]
    rcases lt_or_gt_of_ne hs with hst | hts
    · have hneg : s-t < 0 := sub_neg.mpr hst
      exact ⟨(min_le_right _ _).trans ((le_div_iff_of_neg hneg).mpr (by linarith only [hHi s])),
        ((div_le_iff_of_neg hneg).mpr (by linarith only [hLo s])).trans (le_max_left _ _)⟩
    · have hpos : 0 < s-t := sub_pos.mpr hts
      exact ⟨(min_le_left _ _).trans ((le_div_iff₀ hpos).mpr (by linarith only [hLo s])),
        ((div_le_iff₀ hpos).mpr (by linarith only [hHi s])).trans (le_max_right _ _)⟩
  have hNear : ∀ᶠ s in 𝓝[≠] t, min (q t) (q s) ≤ slope φ t s ∧
      slope φ t s ≤ max (q t) (q s) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact h s hs
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hMin hMax
    (hNear.mono fun _ h => h.1) (hNear.mono fun _ h => h.2)

end Certificate.OverlapBelief

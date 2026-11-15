import Certificate.OverlapBeliefEnvelope
import Certificate.OverlapSimplexBethe

/-! Belief propagation maximizes the finite Bethe functional. Its corrected
value is the log-fugacity integral of its vertex monomer deficits. -/

open Finset Filter MeasureTheory Set
open scoped BigOperators Topology

namespace Certificate.OverlapBelief

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
variable (G : WeightedGraph V E)
variable {u A : ℝ} (hu : 0 < u) (hA : 0 ≤ A) (hW : IncidentWeightBound G A)
variable (hw : ∀ e ∈ G.edges, 0 < G.weight e)

theorem vertexSlack_eq_rootMonomer (v : V) :
    Overlap.vertexSlack G (occupation G hu hA hW) v = u * message G hu hA hW (v, none) := by
  change 1 - (∑ e ∈ Tree.incident G.ends G.vertices G.edges v, occupation G hu hA hW e) = _
  rw [← incidentEdges_eq_incident, occupation_slack]

include hw in
theorem occupation_feasible : Overlap.Feasible G (occupation G hu hA hW) := by
  refine ⟨fun e he => (occupation_mem_Ioo G hu hA hW he (hw e he)).1.le, fun v _ => ?_⟩
  rw [vertexSlack_eq_rootMonomer]
  exact (rootMonomer_mem G hu hA hW v).1.le

theorem occupation_vertexSlack_pos (v : V) : 0 < Overlap.vertexSlack G (occupation G hu hA hW) v := by
  rw [vertexSlack_eq_rootMonomer]
  exact (rootMonomer_mem G hu hA hW v).1

private theorem log_occupation_factor {e : E} (he : e ∈ G.edges) (h : 0 < G.weight e) :
    Real.log (occupation G hu hA hW e * (1 - occupation G hu hA hW e)) =
      Real.log (G.weight e) + ∑ v ∈ G.ends e, Real.log (message G hu hA hW (v, none)) := by
  let p := endpoints G ⟨e, he⟩
  have h1 : 0 < message G hu hA hW (p.1,none) := Real.exp_pos _
  have h2 : 0 < message G hu hA hW (p.2,none) := Real.exp_pos _
  obtain ⟨hne, hp⟩ := endpoints_spec G ⟨e, he⟩
  change p.1 ≠ p.2 at hne
  change G.ends e = {p.1,p.2} at hp
  have hmul := occupation_mul_compl G hu hA hW he h
  change _ = G.weight e * message G hu hA hW (p.1,none) * message G hu hA hW (p.2,none) at hmul
  rw [hmul, Real.log_mul (mul_pos h h1).ne' h2.ne', Real.log_mul h.ne' h1.ne',
    hp, Finset.sum_insert (by simpa using hne), Finset.sum_singleton]
  ring

include hw in
theorem occupation_stationary : Overlap.BetheStationary G u (occupation G hu hA hW) := by
  intro e he
  have h (v : V) :
      Overlap.vertexBetheSlope G u (occupation G hu hA hW) v =
        -Real.log (message G hu hA hW (v,none)) - 1 := by
    unfold Overlap.vertexBetheSlope
    rw [vertexSlack_eq_rootMonomer, Real.log_mul hu.ne'
      (show message G hu hA hW (v, none) ≠ 0 from (Real.exp_pos _).ne')]
    ring
  simp_rw [h]
  rw [Overlap.betheAtomSlope, log_occupation_factor G hu hA hW he (hw e he), Finset.sum_sub_distrib]
  simp only [Finset.sum_neg_distrib, Finset.sum_const, G.ends_card e he, nsmul_eq_mul]
  ring

include hw in
theorem finiteBethe_le_occupation {p : E → ℝ} (hp : Overlap.Feasible G p) :
    Overlap.finiteBethe G u p ≤ Overlap.finiteBethe G u (occupation G hu hA hW) :=
  Overlap.finiteBethe_le_of_stationary (occupation_feasible G hu hA hW hw) hp
    (fun e he => occupation_mem_Ioo G hu hA hW he (hw e he))
    (fun v _ => occupation_vertexSlack_pos G hu hA hW v)
    (occupation_stationary G hu hA hW hw)

include hw in
/-- The exact fixed-point evaluation of the Bethe functional. -/
theorem finiteBethe_occupation_eq :
    Overlap.finiteBethe G u (occupation G hu hA hW) =
      -(∑ v ∈ G.vertices, Real.log (message G hu hA hW (v,none))) +
        ∑ e ∈ G.edges, Real.log (1 - occupation G hu hA hW e) := by
  let γ := occupation G hu hA hW
  let l (v : V) := Real.log (message G hu hA hW (v,none))
  let q (v : V) := Overlap.vertexSlack G γ v
  have hv (v : V) : q v * Real.log u - q v * Real.log (q v) = -q v * l v := by
    have hlog : Real.log (q v) = Real.log u + l v := by
      dsimp only [q, γ, l]
      rw [vertexSlack_eq_rootMonomer, Real.log_mul hu.ne'
      (show message G hu hA hW (v, none) ≠ 0 from (Real.exp_pos _).ne')]
    rw [hlog]
    ring
  have he (e : E) (hE : e ∈ G.edges) :
      γ e * Real.log (G.weight e) + Overlap.betheAtom (γ e) =
        -(∑ v ∈ G.ends e, γ e * l v) + Real.log (1-γ e) := by
    have hi := occupation_mem_Ioo G hu hA hW hE (hw e hE)
    have hlog := log_occupation_factor G hu hA hW hE (hw e hE)
    change Real.log (γ e * (1-γ e)) = Real.log (G.weight e) + ∑ v ∈ G.ends e, l v at hlog
    rw [Real.log_mul hi.1.ne' (sub_pos.mpr hi.2).ne'] at hlog
    rw [Overlap.betheAtom, ← Finset.mul_sum]
    linear_combination -(γ e) * hlog
  have hE : (∑ e ∈ G.edges, (γ e * Real.log (G.weight e) + Overlap.betheAtom (γ e))) =
      ∑ e ∈ G.edges, (-(∑ v ∈ G.ends e, γ e * l v) + Real.log (1-γ e)) :=
    Finset.sum_congr rfl he
  have hV : (∑ v ∈ G.vertices, (q v * Real.log u - q v * Real.log (q v))) =
      ∑ v ∈ G.vertices, -q v * l v := Finset.sum_congr rfl (fun v _ => hv v)
  change (∑ e ∈ G.edges, (γ e * Real.log (G.weight e) + Overlap.betheAtom (γ e))) +
    (∑ v ∈ G.vertices, (q v * Real.log u - q v * Real.log (q v))) = _
  rw [hE, hV, Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Overlap.sum_incident_vertices]
  have hAcc : -(∑ v ∈ G.vertices, ∑ e ∈ Overlap.incidentEdges G v, γ e * l v) +
      (∑ v ∈ G.vertices, -q v * l v) = -(∑ v ∈ G.vertices, l v) := by
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← Finset.sum_mul]
    unfold q Overlap.vertexSlack
    ring
  change -(∑ v ∈ G.vertices, ∑ e ∈ Overlap.incidentEdges G v, γ e * l v) +
    (∑ e ∈ G.edges, Real.log (1-γ e)) + (∑ v ∈ G.vertices, -q v * l v) =
    -(∑ v ∈ G.vertices, l v) + ∑ e ∈ G.edges, Real.log (1-γ e)
  linarith only [hAcc]

omit [DecidableEq E] [Fintype V] [Fintype E] in
private theorem finiteBethe_exp_shift (p : E → ℝ) (s t : ℝ) :
    Overlap.finiteBethe G (Real.exp s) p = Overlap.finiteBethe G (Real.exp t) p +
      (s-t) * ∑ v ∈ G.vertices, Overlap.vertexSlack G p v := by
  unfold Overlap.finiteBethe
  simp only [Real.log_exp, Finset.mul_sum]
  rw [add_assoc, add_right_inj, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun v _ => by ring

/-- Bethe pressure at the maximizing edge occupation. -/
noncomputable def betheLog (t : ℝ) : ℝ :=
  Overlap.finiteBethe G (Real.exp t) (occupation G (Real.exp_pos t) hA hW)

/-- Bethe pressure normalized by the all-monomer term. -/
noncomputable def betheCorrected (t : ℝ) : ℝ :=
  betheLog G hA hW t - (G.vertices.card : ℝ) * t

/-- Sum of Bethe monomer deficits on the retained vertices. -/
noncomputable def betheDeficit (t : ℝ) : ℝ :=
  ∑ v ∈ G.vertices, (1 - Real.exp t * message G (Real.exp_pos t) hA hW (v,none))

include hw in
theorem hasDerivAt_betheLog (t : ℝ) :
    HasDerivAt (betheLog G hA hW) ((G.vertices.card : ℝ) - betheDeficit G hA hW t) t := by
  let q (s : ℝ) := ∑ v ∈ G.vertices, Real.exp s * message G (Real.exp_pos s) hA hW (v,none)
  have hq : Continuous q := continuous_finsetSum _ (fun v _ => continuous_rootMonomer G hA hW v)
  have hslack (s : ℝ) : (∑ v ∈ G.vertices, Overlap.vertexSlack G
      (occupation G (Real.exp_pos s) hA hW) v) = q s := by
    exact Finset.sum_congr rfl fun v _ => vertexSlack_eq_rootMonomer G (Real.exp_pos s) hA hW v
  have hLower (s r : ℝ) : betheLog G hA hW r + (s-r) * q r ≤ betheLog G hA hW s := by
    let γ := occupation G (Real.exp_pos r) hA hW
    change Overlap.finiteBethe G (Real.exp r) γ + (s-r)*q r ≤ _
    rw [← hslack r, ← finiteBethe_exp_shift G γ s r]
    exact finiteBethe_le_occupation G (Real.exp_pos s) hA hW hw
      (occupation_feasible G (Real.exp_pos r) hA hW hw)
  have hUp (s : ℝ) : betheLog G hA hW s ≤ betheLog G hA hW t + (s-t) * q s := by
    have h := hLower t s
    linarith only [h]
  have h := hasDerivAt_of_affine_envelope hq.continuousAt (fun s => hLower s t) hUp
  simpa [q, betheDeficit, Finset.sum_sub_distrib] using h

include hw in
theorem hasDerivAt_betheCorrected (t : ℝ) :
    HasDerivAt (betheCorrected G hA hW) (-betheDeficit G hA hW t) t := by
  change HasDerivAt (fun s : ℝ => betheLog G hA hW s - (G.vertices.card : ℝ)*s) _ t
  have h := (hasDerivAt_betheLog G hA hW hw t).fun_sub
    ((hasDerivAt_id t).const_mul (G.vertices.card : ℝ))
  convert h using 1 <;> first | rfl | (simp only [mul_one]; ring)

theorem betheDeficit_bounds (t : ℝ) : 0 ≤ betheDeficit G hA hW t ∧
    betheDeficit G hA hW t ≤ (G.vertices.card : ℝ) * (A / (Real.exp t)^2) := by
  rw [betheDeficit]
  refine ⟨Finset.sum_nonneg fun v _ => sub_nonneg.mpr (rootMonomer_mem G (Real.exp_pos t) hA hW v).2, ?_⟩
  calc
    _ ≤ ∑ _v ∈ G.vertices, A / (Real.exp t)^2 :=
      Finset.sum_le_sum fun v _ => rootMonomer_deficit_le G (Real.exp_pos t) hA hW v
    _ = _ := by simp [nsmul_eq_mul]

theorem continuous_betheDeficit : Continuous (betheDeficit G hA hW) := by
  exact continuous_finsetSum _ fun v _ => continuous_const.sub (continuous_rootMonomer G hA hW v)

include hw in
theorem betheCorrected_nonneg (t : ℝ) : 0 ≤ betheCorrected G hA hW t := by
  have hf : Overlap.Feasible G (fun _ => 0) := by simp [Overlap.Feasible, Overlap.vertexSlack]
  have h := finiteBethe_le_occupation G (Real.exp_pos t) hA hW hw hf
  have hz : Overlap.finiteBethe G (Real.exp t) (fun _ => 0) = (G.vertices.card : ℝ) * t := by
    simp [Overlap.finiteBethe, Overlap.vertexSlack, Overlap.betheAtom, nsmul_eq_mul]
  rw [hz] at h
  exact sub_nonneg.mpr h

include hw in
theorem betheCorrected_le (t : ℝ) :
    betheCorrected G hA hW t ≤ (G.vertices.card : ℝ) * (A/(Real.exp t)^2) := by
  let u := Real.exp t
  let m (v : V) := message G (Real.exp_pos t) hA hW (v,none)
  let γ := occupation G (Real.exp_pos t) hA hW
  have hu : 0 < u := Real.exp_pos t
  have hm (v : V) : 0 < m v := Real.exp_pos _
  have hNormalize : -(∑ v ∈ G.vertices, Real.log (m v)) - (G.vertices.card : ℝ)*t =
      ∑ v ∈ G.vertices, -Real.log (u * m v) := by
    simp_rw [Real.log_mul hu.ne' (hm _).ne', Finset.sum_neg_distrib, Finset.sum_add_distrib]
    dsimp only [u]
    simp only [Real.log_exp, Finset.sum_const, nsmul_eq_mul]
    ring
  have hq (v : V) : -Real.log (u * m v) ≤ A/u^2 := by
    have hLo := (message_mem G (Real.exp_pos t) hA hW (v,none)).1
    change (u + A/u)⁻¹ ≤ m v at hLo
    have hD : 0 < u + A/u := add_pos_of_pos_of_nonneg hu (div_nonneg hA hu.le)
    calc
      _ = Real.log ((u*m v)⁻¹) := (Real.log_inv _).symm
      _ ≤ (u*m v)⁻¹ - 1 := Real.log_le_sub_one_of_pos (inv_pos.mpr (mul_pos hu (hm v)))
      _ ≤ (u * (u+A/u)⁻¹)⁻¹ - 1 := by
        exact sub_le_sub_right (inv_anti₀ (mul_pos hu (inv_pos.mpr hD))
          (mul_le_mul_of_nonneg_left hLo hu.le)) _
      _ = _ := by
        rw [mul_inv_rev, inv_inv]
        field_simp [hu.ne']
        ring
  have hE : (∑ e ∈ G.edges, Real.log (1-γ e)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro e he
    have h := occupation_mem_Ioo G (Real.exp_pos t) hA hW he (hw e he)
    exact Real.log_nonpos (sub_nonneg.mpr h.2.le) (sub_le_self _ h.1.le)
  have hV : (∑ v ∈ G.vertices, -Real.log (u*m v)) ≤ (G.vertices.card : ℝ) * (A/u^2) := by
    simpa only [Finset.sum_const, nsmul_eq_mul] using
      (Finset.sum_le_sum (s := G.vertices) (fun v _ => hq v))
  rw [betheCorrected, betheLog, finiteBethe_occupation_eq G (Real.exp_pos t) hA hW hw]
  change -(∑ v ∈ G.vertices, Real.log (m v)) + (∑ e ∈ G.edges, Real.log (1-γ e)) -
    (G.vertices.card : ℝ)*t ≤ (G.vertices.card : ℝ) * (A/u^2)
  linarith only [hNormalize,hE,hV]

include hw in
theorem tendsto_betheCorrected : Tendsto (betheCorrected G hA hW) atTop (𝓝 0) := by
  have ht : Tendsto (fun t : ℝ => -2 * t) atTop atBot := by
    simpa using tendsto_id.const_mul_atTop_of_neg (show (-2 : ℝ) < 0 by norm_num)
  have he : Tendsto (fun t : ℝ => ((G.vertices.card : ℝ) * A) * Real.exp (-2*t)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_apply] using
      (Real.tendsto_exp_atBot.comp ht).const_mul ((G.vertices.card : ℝ) * A)
  have hEq (t : ℝ) : (G.vertices.card : ℝ) * (A/(Real.exp t)^2) =
      ((G.vertices.card : ℝ)*A) * Real.exp (-2*t) := by
    rw [sq, ← Real.exp_add, div_eq_mul_inv, ← Real.exp_neg, mul_assoc]
    congr 3
    ring
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds he
    (betheCorrected_nonneg G hA hW hw) (fun t => (betheCorrected_le G hA hW hw t).trans_eq (hEq t))

include hw in
theorem betheCorrected_eq_integral (t : ℝ) :
    betheCorrected G hA hW t = ∫ s in Ioi t, betheDeficit G hA hW s := by
  have hder (s : ℝ) : HasDerivAt (fun r => -betheCorrected G hA hW r) (betheDeficit G hA hW s) s := by
    simpa using (hasDerivAt_betheCorrected G hA hW hw s).fun_neg
  have htop : Tendsto (fun s => -betheCorrected G hA hW s) atTop (𝓝 0) := by
    simpa using (tendsto_betheCorrected G hA hW hw).neg
  simpa using (integral_Ioi_of_hasDerivAt_of_nonneg' (fun s _ => hder s)
    (fun s _ => (betheDeficit_bounds G hA hW s).1) htop).symm

end Certificate.OverlapBelief

import Certificate.CanonicalTree
import Certificate.SoftLogLipschitz

/-! Joint measurability and pathwise log-fugacity regularity of the canonical messages. -/

open MeasureTheory Filter Set
open scoped Topology

namespace Certificate.CanonicalTree

private theorem measurable_depth_logFugacity (β d : ℝ) (n : ℕ) (v : Vertex) :
    Measurable (fun p : ℝ × Environment => depth β d (Real.exp p.1) n v p.2) := by
  induction n generalizing v with
  | zero =>
    exact measurable_const.prodMk (Real.measurable_exp.comp measurable_fst).inv
  | succ n ih =>
    unfold depth
    simp only [TreeBoundary.bounds]
    have hz : Measurable (fun p : ℝ × Environment => Real.exp p.1) :=
      Real.measurable_exp.comp measurable_fst
    have hL : Measurable (fun p : ℝ × Environment =>
        TreeBoundary.update (Real.exp p.1) (weight β d p.2 v)
          (fun i => (depth β d (Real.exp p.1) n (child v i) p.2).2)) := by
      unfold TreeBoundary.update
      exact (hz.add (Measurable.tsum fun i =>
        ((measurable_weight β d v i).comp measurable_snd).mul (ih (child v i)).snd)).inv
    have hU : Measurable (fun p : ℝ × Environment =>
        TreeBoundary.update (Real.exp p.1) (weight β d p.2 v)
          (fun i => (depth β d (Real.exp p.1) n (child v i) p.2).1)) := by
      unfold TreeBoundary.update
      exact (hz.add (Measurable.tsum fun i =>
        ((measurable_weight β d v i).comp measurable_snd).mul (ih (child v i)).fst)).inv
    exact hL.prodMk hU

theorem measurable_lower_logFugacity (β d : ℝ) (v : Vertex) :
    Measurable (fun p : ℝ × Environment => lower β d (Real.exp p.1) v p.2) :=
  Measurable.iSup fun n => (measurable_depth_logFugacity β d n v).fst

theorem measurable_upper_logFugacity (β d : ℝ) (v : Vertex) :
    Measurable (fun p : ℝ × Environment => upper β d (Real.exp p.1) v p.2) :=
  Measurable.iInf fun n => (measurable_depth_logFugacity β d n v).snd

/-- One almost-sure event gives Lipschitz continuity simultaneously at all
positive fugacities and at every vertex. -/
theorem ae_extremal_logLipschitz {β d : ℝ} (hβ : 0 < β) (hd : 0 < d) :
    ∀ᵐ ω ∂law, ∀ v,
      (∀ t, 0 < lower β d (Real.exp t) v ω ∧ 0 < upper β d (Real.exp t) v ω) ∧
      LipschitzWith 1 (fun t => Real.log (lower β d (Real.exp t) v ω)) ∧
      LipschitzWith 1 (fun t => Real.log (upper β d (Real.exp t) v ω)) := by
  filter_upwards [ae_summable_weight hβ hd] with ω hw
  let hw₀ := weight_nonneg β d ω
  obtain ⟨L, U, htend, hpos, hL, hU⟩ :=
    TreeBoundary.exists_logLipschitz_boundary child (weight β d ω) hw hw₀
  have eqL (t : ℝ) (v : Vertex) : lower β d (Real.exp t) v ω = L t v := by
    refine tendsto_nhds_unique ?_ (htend t v).1
    refine tendsto_atTop_ciSup (monotone_nat_of_le_succ fun n =>
      (TreeBoundary.bounds_step (Real.exp t) child (weight β d ω)
        (Real.exp_pos t) hw hw₀ n v).1) ?_
    exact ⟨(Real.exp t)⁻¹, fun x ⟨n, hn⟩ => hn ▸
      ((TreeBoundary.bounds_mem (Real.exp t) child (weight β d ω)
        (Real.exp_pos t) hw hw₀ n v).2.1.trans
      (TreeBoundary.bounds_mem (Real.exp t) child (weight β d ω)
        (Real.exp_pos t) hw hw₀ n v).2.2)⟩
  have eqU (t : ℝ) (v : Vertex) : upper β d (Real.exp t) v ω = U t v := by
    refine tendsto_nhds_unique ?_ (htend t v).2
    refine tendsto_atTop_ciInf (antitone_nat_of_succ_le fun n =>
      (TreeBoundary.bounds_step (Real.exp t) child (weight β d ω)
        (Real.exp_pos t) hw hw₀ n v).2) ?_
    exact ⟨0, fun x ⟨n, hn⟩ => hn ▸
      ((TreeBoundary.bounds_mem (Real.exp t) child (weight β d ω)
        (Real.exp_pos t) hw hw₀ n v).1.trans
      (TreeBoundary.bounds_mem (Real.exp t) child (weight β d ω)
        (Real.exp_pos t) hw hw₀ n v).2.1)⟩
  intro v
  simp only [eqL, eqU]
  exact ⟨fun t => hpos t v, hL v, hU v⟩

end Certificate.CanonicalTree

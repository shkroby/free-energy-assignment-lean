import Certificate.FiniteRootBounds
import Certificate.CanonicalCutoffLimit
import Certificate.SoftPressure

/-! Passing from finite-depth expected brackets to the limiting cavity message. -/

open Filter MeasureTheory Set
open scoped Topology

namespace Certificate

/-- Fixed-depth convergence of lower and upper brackets determines the limit
of any sequence between them, once the limiting brackets meet. -/
theorem tendsto_of_two_depth_limits {a : ℕ → ℝ} {L U : ℕ → ℕ → ℝ}
    {l u : ℕ → ℝ} {x : ℝ}
    (hL : ∀ k, Tendsto (L k) atTop (𝓝 (l k)))
    (hU : ∀ k, Tendsto (U k) atTop (𝓝 (u k)))
    (hl : Tendsto l atTop (𝓝 x)) (hu : Tendsto u atTop (𝓝 x))
    (hb : ∀ k, ∀ᶠ n in atTop, L k n ≤ a n ∧ a n ≤ U k n) :
    Tendsto a atTop (𝓝 x) := by
  apply tendsto_order.2
  constructor
  · intro y hy
    obtain ⟨k, hk⟩ := ((tendsto_order.1 hl).1 y hy).exists
    filter_upwards [(tendsto_order.1 (hL k)).1 y hk, hb k] with n hn hb
    exact hn.trans_le hb.1
  · intro y hy
    obtain ⟨k, hk⟩ := ((tendsto_order.1 hu).2 y hy).exists
    filter_upwards [(tendsto_order.1 (hU k)).2 y hk, hb k] with n hn hb
    exact hb.2.trans_lt hn

namespace CanonicalTree

/-- Both expected cutoff brackets converge to the mean cutoff root message. -/
theorem tendsto_expected_cutoff_depth_brackets {β d z : ℝ}
    (hβ : 0 < β) (hd : 0 < d) (hz : 0 < z) (R : ℝ) :
    let l := ∫ ω, lowerFor (cutoffKernel β R) d z [] ω ∂law
    Tendsto (fun k => ∫ ω, (depthFor (cutoffKernel β R) d z k [] ω).1 ∂law) atTop (𝓝 l) ∧
    Tendsto (fun k => ∫ ω, (depthFor (cutoffKernel β R) d z k [] ω).2 ∂law) atTop (𝓝 l) := by
  let : IsProbabilityMeasure law := isProbabilityMeasure_law
  let K := cutoffKernel β R
  have hKS := ae_summable_cutoffKernel hβ hd R
  have hm := measurable_cutoffKernel β R
  have h₀ := cutoffKernel_nonneg β R
  have hw := ae_summable_weightFor hKS
  have hlim := ae_boundary_limitsFor hz h₀ hKS
  have hmem : ∀ k, ∀ᵐ ω ∂law,
      0 ≤ (depthFor K d z k [] ω).1 ∧
      (depthFor K d z k [] ω).1 ≤ (depthFor K d z k [] ω).2 ∧
      (depthFor K d z k [] ω).2 ≤ z⁻¹ := by
    intro k
    filter_upwards [hw] with ω hw
    exact TreeBoundary.bounds_mem z child (weightFor K d ω) hz hw (fun _ _ => h₀ _) k []
  constructor
  · refine tendsto_integral_of_dominated_convergence (fun _ => z⁻¹)
      (fun k => (measurable_depthFor hm d z k []).fst.aestronglyMeasurable) (integrable_const _) ?_ ?_
    · intro k
      filter_upwards [hmem k] with ω h
      rw [Real.norm_of_nonneg h.1]
      exact h.2.1.trans h.2.2
    · exact hlim.mono fun _ h => (h []).1
  · refine tendsto_integral_of_dominated_convergence (fun _ => z⁻¹)
      (fun k => (measurable_depthFor hm d z k []).snd.aestronglyMeasurable) (integrable_const _) ?_ ?_
    · intro k
      filter_upwards [hmem k] with ω h
      rw [Real.norm_of_nonneg (h.1.trans h.2.1)]
      exact h.2.2
    · filter_upwards [hlim, ae_cutoff_lower_eq_upper hβ hd hz R] with ω h heq
      rw [heq]
      exact (h []).2.1

/-- Convergence of both finite-graph cutoff bracket expectations at each
fixed depth suffices for convergence of the expected root deletion ratio. -/
theorem tendsto_expected_cutoff_ratio_of_depth_brackets
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {ν : ∀ n, Measure (Ω n)}
    {a : ∀ n, Ω n → ℝ} {L U : ℕ → ∀ n, Ω n → ℝ}
    {β d z : ℝ} (hβ : 0 < β) (hd : 0 < d) (hz : 0 < z) (R : ℝ)
    (ha : ∀ n, Integrable (a n) (ν n))
    (hLi : ∀ k n, Integrable (L k n) (ν n))
    (hUi : ∀ k n, Integrable (U k n) (ν n))
    (hb : ∀ k, ∀ᶠ n in atTop, ∀ᵐ ω ∂ν n, L k n ω ≤ a n ω ∧ a n ω ≤ U k n ω)
    (hL : ∀ k, Tendsto (fun n => ∫ ω, L k n ω ∂ν n) atTop
      (𝓝 (∫ ω, (depthFor (cutoffKernel β R) d z k [] ω).1 ∂law)))
    (hU : ∀ k, Tendsto (fun n => ∫ ω, U k n ω ∂ν n) atTop
      (𝓝 (∫ ω, (depthFor (cutoffKernel β R) d z k [] ω).2 ∂law))) :
    Tendsto (fun n => ∫ ω, a n ω ∂ν n) atTop (𝓝 (∫ ω, lowerFor (cutoffKernel β R) d z [] ω ∂law)) := by
  obtain ⟨hl, hu⟩ := tendsto_expected_cutoff_depth_brackets hβ hd hz R
  refine tendsto_of_two_depth_limits hL hU hl hu (fun k => ?_)
  filter_upwards [hb k] with n hn
  exact ⟨integral_mono_ae (hLi k n) (ha n) (hn.mono fun _ h => h.1),
    integral_mono_ae (ha n) (hUi k n) (hn.mono fun _ h => h.2)⟩

noncomputable def graphRootBounds {Ω V E : Type*} [DecidableEq V] [DecidableEq E]
    (G : Ω → WeightedGraph V E) (root : Ω → V) (z : ℝ) (k : ℕ) (ω : Ω) : ℝ × ℝ :=
  Tree.finiteRootBounds (G ω).ends (G ω).edges (G ω).weight z k (G ω).vertices (root ω)

noncomputable def graphRootRatio {Ω V E : Type*} [DecidableEq V]
    (G : Ω → WeightedGraph V E) (root : Ω → V) (z : ℝ) (ω : Ω) : ℝ :=
  Tree.deletionRatio (G ω).ends (G ω).vertices (G ω).edges (G ω).weight z (root ω)

/-- With a possibly size-dependent root law, bounded test convergence of
each finite-depth graph bracket suffices for the mean monomer probability. -/
theorem tendsto_expected_graphRootRatio_of_cutoff_brackets
    {Ω V E : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    [∀ n, DecidableEq (V n)] [∀ n, DecidableEq (E n)]
    {ν : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (ν n)]
    (G : ∀ n, Ω n → WeightedGraph (V n) (E n)) (root : ∀ n, Ω n → V n)
    {β d z : ℝ} (hβ : 0 < β) (hd : 0 < d) (hz : 0 < z) (R : ℝ)
    (hroot : ∀ n, ∀ᵐ ω ∂ν n, root n ω ∈ (G n ω).vertices)
    (hr : ∀ n, Measurable (graphRootRatio (G n) (root n) z))
    (hm : ∀ k n, Measurable (graphRootBounds (G n) (root n) z k))
    (hL : ∀ k, Tendsto (fun n => ∫ ω, (graphRootBounds (G n) (root n) z k ω).1 ∂ν n)
      atTop (𝓝 (∫ ω, (depthFor (cutoffKernel β R) d z k [] ω).1 ∂law)))
    (hU : ∀ k, Tendsto (fun n => ∫ ω, (graphRootBounds (G n) (root n) z k ω).2 ∂ν n)
      atTop (𝓝 (∫ ω, (depthFor (cutoffKernel β R) d z k [] ω).2 ∂law))) :
    Tendsto (fun n => ∫ ω, graphRootRatio (G n) (root n) z ω ∂ν n)
      atTop (𝓝 (∫ ω, lowerFor (cutoffKernel β R) d z [] ω ∂law)) := by
  have hb (k n : ℕ) (ω : Ω n) := Tree.finiteRootBounds_mem (G n ω).ends (G n ω).edges
    (G n ω).weight (G n ω).weight_nonneg hz k (G n ω).vertices (root n ω)
  refine tendsto_expected_cutoff_ratio_of_depth_brackets hβ hd hz R ?_ ?_ ?_ ?_ hL hU
  · intro n
    refine (integrable_const z⁻¹).mono' (hr n).aestronglyMeasurable ?_
    filter_upwards [hroot n] with ω hv
    have h := Tree.deletionRatio_pos_le (G n ω).ends (G n ω).edges (G n ω).weight
      (G n ω).weight_nonneg hz (G n ω).ends_card hv
    exact (Real.norm_of_nonneg h.1.le).trans_le h.2
  · intro k n
    refine (integrable_const z⁻¹).mono' (hm k n).fst.aestronglyMeasurable ?_
    exact Eventually.of_forall fun ω =>
      (Real.norm_of_nonneg (hb k n ω).1).trans_le ((hb k n ω).2.1.trans (hb k n ω).2.2)
  · intro k n
    refine (integrable_const z⁻¹).mono' (hm k n).snd.aestronglyMeasurable ?_
    exact Eventually.of_forall fun ω =>
      (Real.norm_of_nonneg ((hb k n ω).1.trans (hb k n ω).2.1)).trans_le (hb k n ω).2.2
  · exact fun k => Eventually.of_forall fun n => (hroot n).mono fun ω hv =>
      Tree.deletionRatio_between_finiteRootBounds (G n ω).ends (G n ω).edges
        (G n ω).weight (G n ω).weight_nonneg hz (G n ω).ends_card k hv

end CanonicalTree
end Certificate

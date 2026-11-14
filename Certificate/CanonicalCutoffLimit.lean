import Certificate.CanonicalTreeKernel
import Certificate.CanonicalSoftUniqueness
import Certificate.TreeCutoff
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Almost-sure and expected limits of the positive-fugacity cutoff messages. -/

open Filter MeasureTheory Set
open scoped Topology

namespace Certificate.CanonicalTree

private theorem ae_cutoff_depth_brackets {β d z : ℝ} (hβ : 0 < β) (hd : 0 < d)
    (hz : 0 < z) (R : ℕ) :
    ∀ᵐ ω ∂law, ∀ k,
      (depthFor (cutoffKernel β R) d z k [] ω).1 ≤ lowerFor (cutoffKernel β R) d z [] ω ∧
      lowerFor (cutoffKernel β R) d z [] ω ≤ (depthFor (cutoffKernel β R) d z k [] ω).2 := by
  let K := cutoffKernel β R
  have hKS := ae_summable_cutoffKernel hβ hd R
  have h₀ := cutoffKernel_nonneg β R
  filter_upwards [ae_summable_weightFor hKS, ae_boundary_limitsFor hz h₀ hKS,
    ae_cutoff_lower_eq_upper hβ hd hz R] with ω hw hlim heq
  intro k
  have hl : (depthFor K d z k [] ω).1 ≤ lowerFor K d z [] ω := by
    apply ge_of_tendsto (hlim []).1
    filter_upwards [eventually_ge_atTop k] with n hn
    exact (monotone_nat_of_le_succ fun i =>
      (TreeBoundary.bounds_step z child (weightFor K d ω) hz hw
        (fun v j => h₀ _) i []).1) hn
  refine ⟨hl, ?_⟩
  change lowerFor K d z [] ω ≤ _
  change lowerFor K d z [] ω = upperFor K d z [] ω at heq
  rw [heq]
  apply le_of_tendsto (hlim []).2.1
  filter_upwards [eventually_ge_atTop k] with n hn
  have hanti : Antitone (fun n : ℕ => (depthFor K d z n [] ω).2) :=
    antitone_nat_of_succ_le (fun i => (TreeBoundary.bounds_step z child (weightFor K d ω)
      hz hw (fun v j => h₀ _) i []).2)
  exact hanti hn

/-- The cutoff solution at the root converges almost surely on the common
canonical tree. Only the fixed-depth weight convergence is needed, so no
monotonicity of the solution in the length cutoff is assumed. -/
theorem ae_tendsto_cutoff_root {β d z : ℝ} (hβ : 0 < β) (hd : 0 < d) (hz : 0 < z) :
    ∀ᵐ ω ∂law,
      Tendsto (fun R : ℕ => lowerFor (cutoffKernel β R) d z [] ω)
        atTop (𝓝 (lower β d z [] ω)) := by
  have hb : ∀ᵐ ω ∂law, ∀ (R k : ℕ),
      (depthFor (cutoffKernel β R) d z k [] ω).1 ≤ lowerFor (cutoffKernel β R) d z [] ω ∧
      lowerFor (cutoffKernel β R) d z [] ω ≤ (depthFor (cutoffKernel β R) d z k [] ω).2 :=
    ae_all_iff.mpr (ae_cutoff_depth_brackets hβ hd hz)
  filter_upwards [hb, ae_summable_weight hβ hd, ae_root_depth_same_limit hβ hd hz] with ω hb hw hl
  let W (R : ℕ) := weightFor (cutoffKernel β R) d ω
  have hW (R : ℕ) (v : Vertex) (i : ℕ) : 0 ≤ W R v i ∧ W R v i ≤ weight β d ω v i := by
    change 0 ≤ cutoffKernel β R (arrivalLength d (ω v) i) ∧
      cutoffKernel β R (arrivalLength d (ω v) i) ≤ Real.exp (-β * arrivalLength d (ω v) i)
    unfold cutoffKernel
    split
    · exact ⟨Real.exp_nonneg _, le_rfl⟩
    · exact ⟨le_rfl, Real.exp_nonneg _⟩
  have hlim (v : Vertex) (i : ℕ) : Tendsto (fun R => W R v i) atTop (𝓝 (weight β d ω v i)) := by
    apply tendsto_const_nhds.congr'
    obtain ⟨R, hR⟩ := exists_nat_ge (arrivalLength d (ω v) i)
    filter_upwards [eventually_ge_atTop R] with S hS
    change Real.exp (-β * arrivalLength d (ω v) i) =
      cutoffKernel β S (arrivalLength d (ω v) i)
    exact (if_pos (hR.trans (Nat.cast_le.mpr hS))).symm
  exact TreeBoundary.tendsto_of_between_weight_cutoff_bounds (child := child) []
    (fun R => lowerFor (cutoffKernel β R) d z [] ω) hz hw hW hlim hl.1 hl.2 hb

/-- The same cutoff passage holds for expected root messages. -/
theorem tendsto_expectation_cutoff_root {β d z : ℝ} (hβ : 0 < β) (hd : 0 < d) (hz : 0 < z) :
    Tendsto (fun R : ℕ => ∫ ω, lowerFor (cutoffKernel β R) d z [] ω ∂law) atTop
      (𝓝 (∫ ω, lower β d z [] ω ∂law)) := by
  let : IsProbabilityMeasure law := isProbabilityMeasure_law
  apply tendsto_integral_of_dominated_convergence (fun _ : Environment => z⁻¹)
  · intro R
    exact (measurable_lowerFor (measurable_cutoffKernel β R) d z []).aestronglyMeasurable
  · exact integrable_const _
  · intro R
    filter_upwards [ae_boundary_limitsFor hz (cutoffKernel_nonneg β R)
      (ae_summable_cutoffKernel hβ hd R)] with ω h
    rw [Real.norm_of_nonneg (h []).2.2.1.le]
    exact (h []).2.2.2.1.trans (h []).2.2.2.2.1
  · exact ae_tendsto_cutoff_root hβ hd hz

end Certificate.CanonicalTree

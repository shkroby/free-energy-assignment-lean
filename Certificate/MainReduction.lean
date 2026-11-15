import Certificate.CanonicalCutoffPressure
import Certificate.CanonicalHardBethe
import Certificate.HardBetheIntegrability
import Certificate.HardInvariantCoupling
import Certificate.LocalAssignmentBracketLimits

/-!
# Reduction of the manuscript's main theorem

Convergence of local vacancy at each fixed length cutoff is the remaining
input to the full free-energy theorem.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace Certificate

/-- The manuscript's existence-and-uniqueness assertion for its hard law. -/
theorem cavityUniquenessClaim : CavityUniquenessClaim := by
  intro d β hd hβ
  exact existsUnique_hard_cavity_law hβ hd

/-- The cutoff local vacancy limit implies every assertion in the
manuscript's main free-energy theorem. -/
theorem freeEnergyClaim_of_cutoff_local
    (hLocal : ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] {β d κ : ℝ},
      0 < β → 0 < d → 0 < κ → SmallCostTail μ κ d →
      ∀ (t : ℝ) (R : ℕ), ∀ᵐ s ∂volume.restrict (Ioi t),
        Tendsto (fun n : ℕ ↦ ∫ C, (cutoffAssignmentGraph β d κ R n C).deficit s / n ∂iidCosts μ)
          atTop (𝓝 (2 * (1 - CanonicalTree.expectedCutoffVacancy β d R s)))) :
    FreeEnergyClaim := by
  intro μ hμprob κ d β hκ hd hβ hμ
  let : IsProbabilityMeasure μ := hμprob
  obtain ⟨H, hH, hUnique⟩ := existsUnique_hard_cavity_law hβ hd
  let Hprob : ProbabilityMeasure ℝ := ⟨H, hH.1⟩
  have hlimit := CanonicalTree.tendsto_bethePressure_softCavityProbability_of_hard_unique
    hβ hd Hprob hH hUnique
  have hp := CanonicalTree.hard_pressure_formula_of_canonical_cutoff_bethe_limits
    hβ hd hκ hμ (hLocal μ hβ hd hκ hμ) H hlimit
  exact ⟨H, hH, hUnique, hard_cavity_log_integrable hd hβ hH,
    fun x _ ↦ hard_edge_integrand_integrable hd hβ hH x, hard_edgeLogCorrection_integrable hd hβ hH,
    hp.1, hp.2⟩

/-- It suffices to verify convergence of the expected finite-depth
brackets in the cutoff local limit. -/
theorem freeEnergyClaim_of_cutoff_bracket_limits
    (hLocal : ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] {β d κ : ℝ},
      0 < β → 0 < d → 0 < κ → SmallCostTail μ κ d →
      ∀ (R k : ℕ) (t : ℝ),
        Tendsto (fun n => ∫ C, (CanonicalTree.cutoffMeanRootBounds β d κ R (Real.exp t) n k C).1 ∂iidCosts μ)
          atTop (𝓝 (∫ ω, (CanonicalTree.depthFor (CanonicalTree.cutoffKernel β R)
            d (Real.exp t) k [] ω).1 ∂CanonicalTree.law)) ∧
        Tendsto (fun n => ∫ C, (CanonicalTree.cutoffMeanRootBounds β d κ R (Real.exp t) n k C).2 ∂iidCosts μ)
          atTop (𝓝 (∫ ω, (CanonicalTree.depthFor (CanonicalTree.cutoffKernel β R)
            d (Real.exp t) k [] ω).2 ∂CanonicalTree.law))) :
    FreeEnergyClaim := by
  apply freeEnergyClaim_of_cutoff_local
  intro μ _ β d κ hβ hd hκ hμ t R
  apply Eventually.of_forall
  intro s
  exact CanonicalTree.tendsto_expected_cutoff_deficit_of_bracket_limits hβ hd R s
    (fun k ↦ (hLocal μ hβ hd hκ hμ R k s).1) (fun k ↦ (hLocal μ hβ hd hκ hμ R k s).2)

end Certificate

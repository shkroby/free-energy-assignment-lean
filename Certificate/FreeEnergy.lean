import Certificate.FiniteLocalBracketLimit
import Certificate.IndependentShapeBracketMixture
import Certificate.LocalRootSymmetry
import Certificate.LocalZeroCutoffBrackets
import Certificate.MainReduction

/-! The local limit on the cutoff graph closes the free-energy certificate. -/

open Filter MeasureTheory Set
open scoped Topology

namespace Certificate

namespace CanonicalTree

set_option maxHeartbeats 1000000 in
/-- At each depth and integer cutoff, the expected lower and upper vacancy
brackets on the iid assignment graph converge to those on the Poisson tree. -/
theorem tendsto_expected_cutoffMeanRootBounds
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {β d κ : ℝ}
    (hd : 0 < d) (hκ : 0 < κ) (hμ : SmallCostTail μ κ d) (R k : ℕ) (t : ℝ) :
    Tendsto (fun n => ∫ C, (cutoffMeanRootBounds β d κ R (Real.exp t) n k C).1 ∂iidCosts μ)
        atTop (𝓝 (∫ ω, (depthFor (cutoffKernel β R) d (Real.exp t) k [] ω).1 ∂law)) ∧
      Tendsto (fun n => ∫ C, (cutoffMeanRootBounds β d κ R (Real.exp t) n k C).2 ∂iidCosts μ)
        atTop (𝓝 (∫ ω, (depthFor (cutoffKernel β R) d (Real.exp t) k [] ω).2 ∂law)) := by
  cases R with
  | zero =>
    simpa only [Nat.cast_zero] using tendsto_zero_cutoffMeanRootBounds (β := β) hd hκ hμ k t
  | succ R =>
    let z := Real.exp t
    have hz : 0 < z := Real.exp_pos t
    have hR : 0 < ((R + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos R)
    let roots (n : ℕ) : Fin (n+1) := 0
    have hTest (P : ℝ × ℝ → ℝ) (hP : Continuous P) (hB : ∀ x : ℝ × ℝ, 0 ≤ x.1 →
        x.1 ≤ x.2 → x.2 ≤ z⁻¹ → P x ∈ Icc 0 z⁻¹) :
        Tendsto (fun n => ∫ C, P (cutoffRootBounds β d κ (R + 1 : ℕ) z (n+1) k
          (Sum.inl (roots n)) C) ∂iidCosts μ) atTop
            (𝓝 (∫ ω, P (depthFor (cutoffKernel β (R + 1 : ℕ)) d z k [] ω) ∂law)) := by
      rw [integral_depthFor_eq_cutoffShapeMixture hd hR hz k P hP hB]
      exact tendsto_expected_cutoffRowBracket_mixture hd hκ hR hz hμ k roots P hP hB
    exact tendsto_expected_cutoffMeanRootBounds_of_root μ β d κ _ hz k
      (fun n => Sum.inl (roots n))
      (hTest Prod.fst continuous_fst fun _ h₀ h₁ h₂ => ⟨h₀, h₁.trans h₂⟩)
      (hTest Prod.snd continuous_snd fun _ h₀ h₁ h₂ => ⟨h₀.trans h₁, h₂⟩)

end CanonicalTree

/-- The full bipartite random assignment free-energy theorem. The hard
cavity law is unique, the Bethe terms are integrable, and the pressure
converges almost surely. A finite positive-order cost moment gives L¹ convergence. -/
theorem freeEnergyClaim : FreeEnergyClaim := by
  apply freeEnergyClaim_of_cutoff_bracket_limits
  intro μ _ β d κ _ hd hκ hμ R k t
  exact CanonicalTree.tendsto_expected_cutoffMeanRootBounds hd hκ hμ R k t

end Certificate

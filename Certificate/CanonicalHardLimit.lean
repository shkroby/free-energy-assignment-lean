import Certificate.CanonicalHardExistence
import Certificate.HardLogMoment

/-!
# Uniqueness and convergence from invariant couplings

The endpoint comparison proves uniqueness whenever the coupling recursion
admits a fixed point for each pair of hard marginal laws.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace Certificate

/-- An invariant coupling for each pair of hard laws is enough for the
manuscript's existence-and-uniqueness conclusion. -/
theorem existsUnique_hard_cavity_law_of_invariant_couplings {β d : ℝ}
    (hβ : 0 < β) (hd : 0 < d)
    (hInv : ∀ μ ν : Measure ℝ, IsCavityLaw β d μ → IsCavityLaw β d ν →
      ∃ (ρ : Measure (ℝ × ℝ)) (_ : IsProbabilityMeasure ρ),
        ρ.map Prod.fst = μ ∧ ρ.map Prod.snd = ν ∧
        (markedArrivalSequenceLaw ρ).map (pairedHardRoot β d) = ρ) :
    ∃! H : Measure ℝ, IsCavityLaw β d H := by
  obtain ⟨H, hH⟩ := CanonicalTree.exists_hard_cavity_law hβ hd
  refine ⟨H, hH, fun μ hμ ↦ ?_⟩
  obtain ⟨ρ, hρ, hfst, hsnd, hinv⟩ := hInv μ H hμ hH
  have h := hard_cavity_law_marginals_eq_of_fixed_coupling hd hβ ρ
    (hfst ▸ hμ) (hsnd ▸ hH) hinv
  rwa [hfst, hsnd] at h

namespace CanonicalTree

/-- Once the hard law has been identified uniquely, the entire soft
family converges to it as fugacity decreases to zero. -/
theorem tendsto_softCavityProbability_of_hard_unique {β d : ℝ}
    (hβ : 0 < β) (hd : 0 < d) (H : ProbabilityMeasure ℝ)
    (hUnique : ∀ μ : Measure ℝ, IsCavityLaw β d μ → μ = (H : Measure ℝ)) :
    Tendsto (softCavityProbability β d) (𝓝[>] (0 : ℝ)) (𝓝 H) := by
  apply tendsto_of_subseq_tendsto
  intro z hz
  obtain ⟨hzLim, hzPos⟩ := tendsto_nhdsWithin_iff.mp hz
  have hSmall : ∀ᶠ n in atTop, 0 < z n ∧ z n ≤ 1 := by
    filter_upwards [hzPos, hzLim.eventually (Iio_mem_nhds (zero_lt_one : (0 : ℝ) < 1))]
      with n hn hlt
    exact ⟨hn, hlt.le⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp hSmall
  let z' (n : ℕ) := z (n + N)
  obtain ⟨G, φ, _, hφ, hG⟩ := exists_subseq_softCavityProbability_hard hβ hd z'
    (fun n ↦ (hN _ (Nat.le_add_left N n)).1) (fun n ↦ (hN _ (Nat.le_add_left N n)).2)
    (hzLim.comp (tendsto_add_atTop_nat N))
  have hEq : G = H := Subtype.ext (hUnique G hG)
  exact ⟨fun n ↦ φ n + N, hEq ▸ hφ⟩

end CanonicalTree
end Certificate

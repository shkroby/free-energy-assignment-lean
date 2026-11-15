import Certificate.CanonicalHardLimit
import Certificate.HardBetheIntegrability
import Certificate.SoftLogMoment
import Certificate.WeakBetheMoments

/-!
# The Bethe limit for the canonical soft cavity laws

The common soft logarithmic bounds verify the hypotheses of the
weak-convergence argument along every subsequence with a hard limit.
Uniqueness promotes this to the full right limit in the fugacity.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace Certificate.CanonicalTree

/-- The Bethe formula passes to any hard weak limit of the canonical
positive-fugacity cavity laws. -/
theorem tendsto_bethePressure_softCavityProbability_along_sequence {β d : ℝ}
    (hβ : 0 < β) (hd : 0 < d) (z : ℕ → ℝ) (hz₀ : ∀ n, 0 < z n) (hz₁ : ∀ n, z n ≤ 1)
    (H : ProbabilityMeasure ℝ) (hH : IsCavityLaw β d (H : Measure ℝ))
    (hweak : Tendsto (fun n => softCavityProbability β d (z n)) atTop (𝓝 H)) :
    Tendsto (fun n => bethePressure β d (softCavityProbability β d (z n) : Measure ℝ))
      atTop (𝓝 (bethePressure β d (H : Measure ℝ))) := by
  let μ (n : ℕ) := softCavityProbability β d (z n)
  have hspec (n : ℕ) := softCavityProbability_spec hβ hd (hz₀ n)
  have hsupport (n : ℕ) : ∀ᵐ x ∂(μ n : Measure ℝ), x ∈ Icc 0 (z n)⁻¹ :=
    (hspec n).1.mono fun _ hx => ⟨hx.1.le, hx.2⟩
  have hLaw (n : ℕ) : (markedSpacings (μ n : Measure ℝ)).map
      (arrivalSoftOutput β d (z n)) = (μ n : Measure ℝ) := (hspec n).2
  obtain ⟨K, hK, hTail⟩ := exists_uniform_soft_log_tail hβ hd
  have hupper (n : ℕ) (s : ℝ) (hs : 0 ≤ s) :
      (μ n : Measure ℝ) (Ioi (Real.exp (β*s))) ≤
        ENNReal.ofReal (K * Real.exp (-((s/2)^d/2))) :=
    hTail (z n) (hz₀ n) (hz₁ n) (μ n : Measure ℝ) (hsupport n) (hLaw n) s hs
  obtain ⟨B, hB, hMoment⟩ := exists_uniform_soft_cavity_log_eLpNorm_two_le
    hd hβ hK.le z μ hz₀ hz₁ (fun n => (hspec n).1) hLaw hupper
  have hHardMoment := hard_cavity_log_memLp_two hd hβ hH
  let B' := max B (eLpNorm Real.log 2 (H : Measure ℝ)).toReal
  have hB' : 0 ≤ B' := hB.trans (le_max_left _ _)
  let c := 1 / (2 * (2 : ℝ)^d)
  have hc : 0 < c := by dsimp [c]; positivity
  apply tendsto_bethePressure_of_uniform_logBounds hβ hd hc hK.le hB'
    (fun n => soft_cavity_law_positive (hz₀ n) (μ n : Measure ℝ) (hLaw n))
    hH.2.1 hweak
  · intro q hq
    rcases mem_insert_iff.mp hq with hEq | ⟨n, rfl⟩
    · subst q
      calc
        _ = ENNReal.ofReal (eLpNorm Real.log 2 (H : Measure ℝ)).toReal :=
          (ENNReal.ofReal_toReal hHardMoment.eLpNorm_ne_top).symm
        _ ≤ _ := ENNReal.ofReal_le_ofReal (le_max_right _ _)
    · exact (hMoment n).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  · intro n s hs
    have he : (s/2)^d/2 = c*s^d := by
      unfold c
      rw [Real.div_rpow hs (by norm_num)]
      ring
    rw [neg_mul, ← he]
    exact hupper n s hs

/-- If every hard cavity law equals a given hard law, the canonical
soft Bethe pressures converge to its Bethe pressure as fugacity
decreases to zero. -/
theorem tendsto_bethePressure_softCavityProbability_of_hard_unique {β d : ℝ}
    (hβ : 0 < β) (hd : 0 < d) (H : ProbabilityMeasure ℝ)
    (hH : IsCavityLaw β d (H : Measure ℝ))
    (hUnique : ∀ ν : Measure ℝ, IsCavityLaw β d ν → ν = (H : Measure ℝ)) :
    Tendsto (fun z => bethePressure β d (softCavityProbability β d z : Measure ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 (bethePressure β d (H : Measure ℝ))) := by
  have hLaw := tendsto_softCavityProbability_of_hard_unique hβ hd H hUnique
  apply tendsto_of_subseq_tendsto
  intro z hz
  obtain ⟨hzLim, hzPos⟩ := tendsto_nhdsWithin_iff.mp hz
  have hSmall : ∀ᶠ n in atTop, 0 < z n ∧ z n ≤ 1 := by
    filter_upwards [hzPos, hzLim.eventually (Iio_mem_nhds (zero_lt_one : (0 : ℝ) < 1))]
      with n hn hlt
    exact ⟨hn, hlt.le⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp hSmall
  let z' (n : ℕ) := z (n + N)
  have hWeak : Tendsto (fun n => softCavityProbability β d (z' n)) atTop (𝓝 H) :=
    hLaw.comp (hz.comp (tendsto_add_atTop_nat N))
  exact ⟨fun n => n + N, tendsto_bethePressure_softCavityProbability_along_sequence hβ hd z'
    (fun n => (hN _ (Nat.le_add_left N n)).1) (fun n => (hN _ (Nat.le_add_left N n)).2)
    H hH hWeak⟩

end Certificate.CanonicalTree

import Certificate.SoftLogUpperTail
import Certificate.SoftLogLowerTail
import Certificate.CanonicalSoftUniqueness
import Certificate.CavityExistence

/-! Existence of a zero-fugacity law on the manuscript's canonical arrivals. -/

open Filter MeasureTheory Set
open scoped Topology ENNReal

namespace Certificate.CanonicalTree

/-- The law of the positive-fugacity canonical root message. -/
noncomputable def softCavityProbability (β d z : ℝ) : ProbabilityMeasure ℝ := by
  let : IsProbabilityMeasure law := isProbabilityMeasure_law
  exact ⟨law.map (lower β d z []),
    Measure.isProbabilityMeasure_map (measurable_lower β d z []).aemeasurable⟩

theorem softCavityProbability_spec {β d z : ℝ} (hβ : 0 < β) (hd : 0 < d) (hz : 0 < z) :
    (∀ᵐ h ∂(softCavityProbability β d z : Measure ℝ), h ∈ Ioc 0 z⁻¹) ∧
      (markedSpacings (softCavityProbability β d z : Measure ℝ)).map
        (arrivalSoftOutput β d z) = (softCavityProbability β d z : Measure ℝ) := by
  let : IsProbabilityMeasure law := isProbabilityMeasure_law
  change (∀ᵐ h ∂law.map (lower β d z []), h ∈ Ioc 0 z⁻¹) ∧ _
  constructor
  · apply (ae_map_iff (measurable_lower β d z []).aemeasurable measurableSet_Ioc).mpr
    exact (ae_boundary_limits hβ hd hz).mono fun _ h ↦
      ⟨(h []).2.2.1, (h []).2.2.2.1.trans (h []).2.2.2.2.1⟩
  · change (markedSpacings (law.map (lower β d z []))).map
      (arrivalSoftOutput β d z) = law.map (lower β d z [])
    have h := (crossed_arrival_laws hβ hd hz).2
    rw [← Measure.map_congr (ae_lower_eq_upper hβ hd hz)] at h
    exact h

/-- Every positive soft fugacity sequence tending to zero admits a
subsequence whose limit solves the hard distributional equation. -/
theorem exists_subseq_softCavityProbability_hard {β d : ℝ}
    (hβ : 0 < β) (hd : 0 < d) (z : ℕ → ℝ) (hz₀ : ∀ n, 0 < z n)
    (hz₁ : ∀ n, z n ≤ 1) (hz : Tendsto z atTop (𝓝 0)) :
    ∃ (H : ProbabilityMeasure ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto ((fun n ↦ softCavityProbability β d (z n)) ∘ φ) atTop (𝓝 H) ∧
      IsCavityLaw β d (H : Measure ℝ) := by
  let μ (n : ℕ) := softCavityProbability β d (z n)
  have hμ (n : ℕ) := softCavityProbability_spec hβ hd (hz₀ n)
  have hsupport (n : ℕ) : ∀ᵐ h ∂(μ n : Measure ℝ), h ∈ Icc 0 (z n)⁻¹ :=
    (hμ n).1.mono fun _ h ↦ ⟨h.1.le, h.2⟩
  have hLaw (n : ℕ) : (markedSpacings (μ n : Measure ℝ)).map
      (arrivalSoftOutput β d (z n)) = (μ n : Measure ℝ) := (hμ n).2
  obtain ⟨K, hK, htail⟩ := exists_uniform_soft_log_tail hβ hd
  have hcompact := isCompact_closure_of_soft_cavity_log_laws hd hβ hK.le z μ hz₀ hz₁
    (fun n ↦ (hμ n).1) hLaw
    (fun n t ht ↦ htail (z n) (hz₀ n) (hz₁ n) (μ n : Measure ℝ) (hsupport n) (hLaw n) t ht)
  obtain ⟨K', hK', htail'⟩ := exists_uniform_soft_cavity_log_upperTail hβ hd
  have hc : 0 < (2 * (4 : ℝ) ^ d)⁻¹ := by positivity
  exact exists_subseq_cavityLaw_of_compact_soft_logs hβ hd hc hK'.le z μ hz
    (fun n ↦ soft_cavity_law_positive (hz₀ n) (μ n : Measure ℝ) (hLaw n))
    hLaw hcompact
    (fun n x hx ↦ htail' (z n) (hz₀ n) (hz₁ n) (μ n : Measure ℝ) (hsupport n) (hLaw n) x hx.le)

/-- The zero-fugacity recursive distributional equation has a strictly
positive, finite solution on the canonical exponential-arrival model. -/
theorem exists_hard_cavity_law {β d : ℝ} (hβ : 0 < β) (hd : 0 < d) :
    ∃ H : Measure ℝ, IsCavityLaw β d H := by
  let z (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hz₀ (n : ℕ) : 0 < z n := by dsimp [z]; positivity
  have hz₁ (n : ℕ) : z n ≤ 1 := by
    dsimp [z]
    rw [div_le_iff₀ (by positivity)]
    simp
  obtain ⟨H, _, _, _, hH⟩ := exists_subseq_softCavityProbability_hard hβ hd z hz₀ hz₁
    tendsto_one_div_add_atTop_nhds_zero_nat
  exact ⟨H, hH⟩

end Certificate.CanonicalTree

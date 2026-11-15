import Certificate.FreeEnergy
import Certificate.OverlapDegreeTail
import Certificate.OverlapGibbsTilt
import Certificate.OverlapOccupation

/-! Parameter selection for the quenched overlap theorem. -/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace Certificate.Overlap

/-- The actual retained edge set used for the positive-fugacity tilt. -/
noncomputable def overlapKeptEdges (d κ : ℝ) (R D n : ℕ) (C : CostArray) :
    Finset (Fin n × Fin n) :=
  trimDegrees D (retainedEdges d κ (R : ℝ) n C)

/-- The retained occupations approximate the hard square statistic, and
the finite-graph log tilt has the quadratic penalty plus the good-row error.
The parameters follow the order of the manuscript's cutoff argument. -/
def RetainedOverlapTestInput (μ : Measure ℝ) (β d κ Q : ℝ) : Prop :=
  ∀ δ > 0, ∃ η > 0,
    ∀ᶠ z : ℝ in 𝓝[>] (0 : ℝ), ∀ᶠ R : ℕ in atTop, ∀ᶠ D : ℕ in atTop,
      ∃ γ : (n : ℕ) → CostArray → (Fin n × Fin n) → ℝ,
        (∀ n e, Measurable (fun C => γ n C e)) ∧
        (∀ n C e, γ n C e ∈ Icc 0 1) ∧
        (∀ᵐ C ∂iidCosts μ, ∀ᶠ n : ℕ in atTop,
          |(∑ e, (γ n C e)^2) / (n : ℝ) - Q| < δ) ∧
        ∀ a > 0, ∀ᵐ C ∂iidCosts μ, ∀ᶠ n : ℕ in atTop,
          ∀ (f : Fin n × Fin n → ℝ), (∀ e, |f e| ≤ 1) → ∀ t : ℝ, |t| ≤ 1 →
            let kept := overlapKeptEdges d κ R D n C
            let u := Real.log z
            Real.log (((gibbsTiltedAssignmentGraph β d κ t n C f).retain kept
              (Finset.subset_univ _)).Z u) ≤
            Real.log (((assignmentGraph β d κ n C).retain kept (Finset.subset_univ _)).Z u) +
              t * (∑ e, f e * γ n C e) +
                (n : ℝ) * (16*t^2/η + 2*|t| * (δ/16) + a)

private theorem ae_softAssignmentPressure_tendsto_bethe {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {β d κ z : ℝ} (hβ : 0 < β) (hd : 0 < d) (hκ : 0 < κ)
    (hμ : SmallCostTail μ κ d) (hz : 0 < z) :
    ∀ᵐ C ∂iidCosts μ, Tendsto (fun n => softAssignmentPressure β d κ (Real.log z) n C) atTop
      (𝓝 (bethePressure β d (CanonicalTree.softCavityProbability β d z : Measure ℝ))) := by
  have h := CanonicalTree.ae_monomerPressure_tendsto_bethe_of_cutoff_local hβ hd hκ hμ hz
    (fun R => Eventually.of_forall fun s =>
      CanonicalTree.tendsto_expected_cutoff_deficit_of_bracket_limits hβ hd R s
        (fun k => (CanonicalTree.tendsto_expected_cutoffMeanRootBounds hd hκ hμ R k s).1)
        (fun k => (CanonicalTree.tendsto_expected_cutoffMeanRootBounds hd hκ hμ R k s).2))
  simpa only [softAssignmentPressure_eq_monomerPressure, Real.exp_log hz,
    CanonicalTree.softCavityProbability, ProbabilityMeasure.coe_mk] using h

/-- For sufficiently small positive fugacity, the soft-to-hard pressure
gap is eventually below any prescribed tolerance almost surely. -/
theorem eventually_ae_softAssignmentPressure_sub_pressure_lt
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {β d κ ε : ℝ}
    (hβ : 0 < β) (hd : 0 < d) (hκ : 0 < κ) (hμ : SmallCostTail μ κ d) (hε : 0 < ε) :
    ∀ᶠ z : ℝ in 𝓝[>] (0 : ℝ), ∀ᵐ C ∂iidCosts μ, ∀ᶠ n : ℕ in atTop,
      softAssignmentPressure β d κ (Real.log z) n C - pressure β d κ n C < ε := by
  obtain ⟨H,hH,hUnique,_,_,_,hHard,_⟩ :=
    freeEnergyClaim μ (inferInstance : IsProbabilityMeasure μ) κ d β hκ hd hβ hμ
  let Hp : ProbabilityMeasure ℝ := ⟨H,hH.1⟩
  have hsmall := CanonicalTree.tendsto_bethePressure_softCavityProbability_of_hard_unique
    hβ hd Hp hH hUnique
  let b := bethePressure β d H
  have hb : b < b + ε/2 := by linarith
  filter_upwards [hsmall.eventually (Iio_mem_nhds hb),
    (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))] with z hzLimit hz
  let bz := bethePressure β d (CanonicalTree.softCavityProbability β d z : Measure ℝ)
  have hzLimit' : bz < b + ε/2 := hzLimit
  filter_upwards [hHard, ae_softAssignmentPressure_tendsto_bethe hβ hd hκ hμ hz] with C hP hSoft
  have hb₀ : b - ε/4 < b := by linarith
  have hbz₀ : bz < bz + ε/4 := by linarith
  filter_upwards [hP.eventually (Ioi_mem_nhds hb₀),
    hSoft.eventually (Iio_mem_nhds hbz₀)] with n hn₀ hn₁
  change b - ε/4 < pressure β d κ n C at hn₀
  change softAssignmentPressure β d κ (Real.log z) n C < bz + ε/4 at hn₁
  linarith

/-- Choosing fugacity, length cutoff and degree cap in order converts the
retained local tests and tilt into the hard uniform edge-statistic estimate. -/
theorem uniformEdgeStatisticBound_of_retainedOverlapTests
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {β d κ Q : ℝ}
    (hβ : 0 < β) (hd : 0 < d) (hκ : 0 < κ) (hμ : SmallCostTail μ κ d)
    (hRetained : RetainedOverlapTestInput μ β d κ Q) :
    UniformEdgeStatisticBound μ β d κ Q := by
  intro δ hδ
  obtain ⟨η,hη,hTest⟩ := hRetained δ hδ
  obtain ⟨s,hs,hs₁,hquad⟩ := exists_overlap_chernoff_step hη hδ
  let a := s*δ/12
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨z,⟨hTest,hGap⟩,hz⟩ := ((hTest.and
    (eventually_ae_softAssignmentPressure_sub_pressure_lt hβ hd hκ hμ ha)).and
      (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))).exists
  let u := Real.log z
  let E := Real.exp (1 - 2*u)
  have hE : 0 < E := Real.exp_pos _
  obtain ⟨R₀,_,hOmit⟩ :=
    ae_eventually_trimmedAssignment_omittedWeight_div_lt hβ hd hκ hμ (div_pos ha hE)
  obtain ⟨R,hR,hR₀⟩ := (hTest.and (eventually_ge_atTop R₀)).exists
  obtain ⟨D₀,hD₀⟩ := hOmit (R : ℝ) (Nat.cast_le.mpr hR₀)
  obtain ⟨D,hD,hD₀'⟩ := (hR.and (eventually_ge_atTop D₀)).exists
  obtain ⟨γ,hmeas,hmem,hBias,hTilt⟩ := hD
  refine ⟨s*δ/2, by positivity, γ, hmeas, hmem, ?_⟩
  filter_upwards [hBias, hGap, hTilt a ha, hD₀] with C hBC hGC hTC hOC
  filter_upwards [hBC, hGC, hTC, hOC, eventually_gt_atTop (0 : ℕ)]
    with n hB hG hT hO hn
  let kept := overlapKeptEdges d κ R D n C
  let W := (∑ e ∈ Finset.univ \ kept, (assignmentGraph β d κ n C).weight e) / (n : ℝ)
  let gap := softAssignmentPressure β d κ u n C - pressure β d κ n C
  let error := 16*s^2/η + 2*s*(δ/16) + a
  have hO' : W * E < a := (lt_div_iff₀ hE).mp (hO D hD₀')
  have hRest : gap + W*E + a ≤ s*δ/4 := by
    change gap < a at hG
    dsimp only [a] at *
    linarith only [hO', hG]
  apply edgeStatisticBoundAt_of_retained_tilt (u := u) hn hs hs₁ C kept (γ n C) error hB
  · intro f hf t ht
    have h := hT f hf t (ht.le.trans hs₁)
    dsimp only at h
    have ht₂ : t^2 = s^2 := by rw [← ht, sq_abs]
    simpa only [ht, ht₂, error] using h
  · change gap + W*E + error ≤ s*δ - s*δ/2
    have h := overlap_cgf_margin_of_error_budgets hs.le hquad
      (show δ/16 ≤ δ/16 from le_rfl) hRest
    dsimp only [error]
    linarith only [h]

/-- Quenched pair concentration and almost-sure product convergence for
the actual cavity target, from the retained occupation tests and tilt. -/
theorem quenchedOverlap_of_retainedOverlapTests
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {β d κ : ℝ} {H : Measure ℝ}
    (hβ : 0 < β) (hd : 0 < d) (hκ : 0 < κ) (hμ : SmallCostTail μ κ d)
    (hH : IsCavityLaw β d H) (hRetained : RetainedOverlapTestInput μ β d κ (cavityOverlap β d H)) :
    let Q := cavityOverlap β d H
    Q ∈ Ioo 0 1 ∧
      (∀ ε > 0, ∃ c > 0, ∀ᵐ C ∂iidCosts μ, ∀ᶠ n : ℕ in atTop,
        gibbsAssignmentPair β d κ n C {p | ε < |assignmentOverlap p.1 p.2 - Q|} ≤
          ENNReal.ofReal (4 * Real.exp (-c * (n : ℝ)))) ∧
      (∀ᵐ C ∂iidCosts μ, gibbsPairSequence β d κ C
        {ω | Tendsto (fun n => assignmentOverlap (ω n).1 (ω n).2) atTop (𝓝 Q)} = 1) :=
  quenchedOverlap_of_uniformEdgeStatisticBound (cavityOverlap_mem_Ioo hd hH)
    (uniformEdgeStatisticBound_of_retainedOverlapTests hβ hd hκ hμ hRetained)

end Certificate.Overlap

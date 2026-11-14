import Certificate.CompletionTransfer
import Certificate.SoftExpected
import Certificate.SoftConcentrationLimit

/-! The almost-sure and L¹ pressure limits from convergence of local vacancy. -/

open Filter MeasureTheory Set
open scoped Topology

namespace Certificate

/-- The two finite monomer pressure encodings agree at every positive fugacity. -/
theorem softAssignmentPressure_eq_monomerPressure
    (β d κ t : ℝ) (n : ℕ) (C : CostArray) :
    softAssignmentPressure β d κ t n C =
      Completion.monomerPressure β d κ n C (Real.exp t) := by
  unfold softAssignmentPressure Completion.monomerPressure WeightedGraph.Z
  rw [← Tree.Bipartite.monomerPartition_eq_grouped]
  rfl

/-- A fixed limiting local vacancy profile determines the positive-fugacity
pressure through the interpolation integral. -/
theorem ae_monomerPressure_limit_of_local_deficit_limits
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {β d κ : ℝ}
    (hβ : 0 < β) (hd : 0 < d) (hκ : 0 < κ) (hμ : SmallCostTail μ κ d)
    (m : ℝ → ℝ)
    (hlocal : ∀ t : ℝ, ∀ᵐ s ∂volume.restrict (Ioi t),
      Tendsto (fun n : ℕ ↦ ∫ C, (assignmentGraph β d κ n C).deficit s / n ∂iidCosts μ)
        atTop (𝓝 (2 * (1 - m s))))
    {z : ℝ} (hz : 0 < z) :
    ∀ᵐ C ∂iidCosts μ, Tendsto (fun n ↦ Completion.monomerPressure β d κ n C z)
      atTop (𝓝 (2 * Real.log z + 2 * ∫ s in Ioi (Real.log z), (1 - m s))) := by
  have hE := tendsto_expected_softAssignmentPressure_of_local hβ hd hκ hμ
    (Real.log z) m (hlocal (Real.log z))
  have hA := ae_tendsto_softAssignmentPressure_of_expected hμ.1 hβ.le d κ
    (Real.log z) hκ.le hE
  simpa only [softAssignmentPressure_eq_monomerPressure, Real.exp_log hz] using hA

/-- Local vacancy convergence gives a finite deterministic hard pressure limit.
The random model assumptions suffice for the additional L¹ limit under a
finite positive-order cost moment. -/
theorem hard_pressure_exists_of_local_deficit_limits
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {β d κ : ℝ}
    (hβ : 0 < β) (hd : 0 < d) (hκ : 0 < κ) (hμ : SmallCostTail μ κ d)
    (m : ℝ → ℝ)
    (hlocal : ∀ t : ℝ, ∀ᵐ s ∂volume.restrict (Ioi t),
      Tendsto (fun n : ℕ ↦ ∫ C, (assignmentGraph β d κ n C).deficit s / n ∂iidCosts μ)
        atTop (𝓝 (2 * (1 - m s)))) :
    ∃ p : ℝ, (∀ᵐ C ∂iidCosts μ, Tendsto (fun n ↦ pressure β d κ n C) atTop (𝓝 p)) ∧
      (∀ q : ℝ, 0 < q → Integrable (fun c : ℝ ↦ c ^ q) μ →
        (∀ᶠ n in atTop, Integrable (pressure β d κ n) (iidCosts μ)) ∧
        Tendsto (fun n ↦ ∫ C, |pressure β d κ n C - p| ∂iidCosts μ) atTop (𝓝 0)) := by
  let b : ℝ → ℝ := fun z ↦ 2 * Real.log z + 2 * ∫ s in Ioi (Real.log z), (1 - m s)
  have hsoft (z : ℝ) (hz : 0 < z) : ∀ᵐ C ∂iidCosts μ,
      Tendsto (fun n ↦ Completion.monomerPressure β d κ n C z) atTop (𝓝 (b z)) :=
    ae_monomerPressure_limit_of_local_deficit_limits hβ hd hκ hμ m hlocal hz
  obtain ⟨p, _, hp⟩ := exists_pressure_limit_of_positive_fugacity_limits hβ hd hκ hμ hsoft
  refine ⟨p, hp, fun q hq hMq ↦ ⟨?_, ?_⟩⟩
  · exact eventually_integrable_pressure hβ hd hκ hq hμ hMq
  · exact pressure_L1_of_ae_limit hβ hd hκ hq hμ hMq hp

/-- The checked finite-array arguments give the pressure conclusions of the
main theorem once its local profile and its limiting value are identified. -/
theorem hard_pressure_formula_of_local_deficit_limits
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {β d κ : ℝ}
    (hβ : 0 < β) (hd : 0 < d) (hκ : 0 < κ) (hμ : SmallCostTail μ κ d)
    (m : ℝ → ℝ)
    (hlocal : ∀ t : ℝ, ∀ᵐ s ∂volume.restrict (Ioi t),
      Tendsto (fun n : ℕ ↦ ∫ C, (assignmentGraph β d κ n C).deficit s / n ∂iidCosts μ)
        atTop (𝓝 (2 * (1 - m s))))
    (H : Measure ℝ)
    (hformula : Tendsto (fun z ↦ 2 * Real.log z + 2 * ∫ s in Ioi (Real.log z), (1 - m s))
      (𝓝[>] (0 : ℝ)) (𝓝 (bethePressure β d H))) :
    (∀ᵐ C ∂iidCosts μ, Tendsto (fun n ↦ pressure β d κ n C) atTop
      (𝓝 (bethePressure β d H))) ∧
      ((∃ q : ℝ, 0 < q ∧ Integrable (fun c : ℝ ↦ c ^ q) μ) →
        (∀ᶠ n in atTop, Integrable (pressure β d κ n) (iidCosts μ)) ∧
        Tendsto (fun n ↦ ∫ C, |pressure β d κ n C - bethePressure β d H| ∂iidCosts μ)
          atTop (𝓝 0)) := by
  have hp := ae_pressure_limit_of_positive_fugacity_limit hβ hd hκ hμ
    (fun _ hz ↦ ae_monomerPressure_limit_of_local_deficit_limits hβ hd hκ hμ m hlocal hz)
    hformula
  refine ⟨hp, ?_⟩
  rintro ⟨q, hq, hMq⟩
  exact ⟨eventually_integrable_pressure hβ hd hκ hq hμ hMq,
    pressure_L1_of_ae_limit hβ hd hκ hq hμ hMq hp⟩

end Certificate

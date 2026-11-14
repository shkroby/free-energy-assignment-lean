import Certificate.SoftConcentrationMGF
import Certificate.SubgaussianLimit
import Certificate.SoftExpected

/-! Almost-sure concentration of the actual square monomer pressure. -/

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal

namespace Certificate

/-- At fixed positive fugacity the centered monomer pressure tends to zero
almost surely on the single infinite iid cost array. -/
theorem ae_tendsto_centered_softAssignmentPressure
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : μ (Iio 0) = 0)
    {β : ℝ} (hβ : 0 ≤ β) (d κ t : ℝ) (hκ : 0 ≤ κ) :
    ∀ᵐ C ∂iidCosts μ,
      Tendsto (fun n => softAssignmentPressure β d κ t n C -
        ∫ C', softAssignmentPressure β d κ t n C' ∂iidCosts μ) atTop (𝓝 0) := by
  let : IsProbabilityMeasure (iidCosts μ) := by unfold iidCosts; infer_instance
  let X (n : ℕ) (C : CostArray) := softAssignmentPressure β d κ t n C -
    ∫ C', softAssignmentPressure β d κ t n C' ∂iidCosts μ
  let v (n : ℕ) : ℝ≥0 := (n : ℝ≥0) * (monomerRowOscillation n t) ^ 2
  have hm (n : ℕ) : HasSubgaussianMGF (X n) (v n) (iidCosts μ) := by
    by_cases hn : 0 < n
    · exact hasSubgaussianMGF_centered_softAssignmentPressure hμ hβ d κ t hκ hn
    · have hn₀ : n = 0 := by omega
      subst n
      have hx : X 0 = 0 := by funext C; simp [X, softAssignmentPressure]
      have hv : v 0 = 0 := by simp [v]
      rw [hx, hv]
      exact HasSubgaussianMGF.zero
  have hle : ∀ᶠ n : ℕ in atTop, 0 < v n ∧ (v n : ℝ) ≤ 1 / (n : ℝ) ^ (1 / 2 : ℝ) := by
    filter_upwards [eventually_logSquared_div_size_le (Real.exp_pos (-2 * t)),
      eventually_gt_atTop (0 : ℕ)] with n h hn
    have hn₀ : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hl : 0 < Real.log (1 + (n : ℝ) * Real.exp (-2 * t)) :=
      Real.log_pos (lt_add_of_pos_right _ (mul_pos hn₀ (Real.exp_pos _)))
    have hv : (v n : ℝ) = Real.log (1 + (n : ℝ) * Real.exp (-2 * t)) ^ 2 / n := by
      change (n : ℝ) * (Real.log (1 + (n : ℝ) * Real.exp (-2 * t)) / n) ^ 2 = _
      field_simp [hn₀.ne']
    refine ⟨?_, hv.trans_le h⟩
    have hp : 0 < (v n : ℝ) := hv ▸ (div_pos (pow_pos hl _) hn₀)
    exact_mod_cast hp
  exact ae_tendsto_zero_of_subgaussian_stretched_decay (iidCosts μ) hm zero_lt_one hle

/-- A deterministic limit of the expected pressures lifts to the same
almost-sure limit of the random pressures. -/
theorem ae_tendsto_softAssignmentPressure_of_expected
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : μ (Iio 0) = 0)
    {β : ℝ} (hβ : 0 ≤ β) (d κ t : ℝ) (hκ : 0 ≤ κ) {b : ℝ}
    (h : Tendsto (fun n => ∫ C, softAssignmentPressure β d κ t n C ∂iidCosts μ)
      atTop (𝓝 b)) :
    ∀ᵐ C ∂iidCosts μ,
      Tendsto (fun n => softAssignmentPressure β d κ t n C) atTop (𝓝 b) := by
  filter_upwards [ae_tendsto_centered_softAssignmentPressure hμ hβ d κ t hκ] with C hC
  simpa only [sub_add_cancel, zero_add] using hC.add h

/-- The monomer pressure on the actual infinite iid array converges almost
surely to the integrated local profile once local convergence is supplied. -/
theorem ae_tendsto_softAssignmentPressure_of_local
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {β d κ : ℝ} (hβ : 0 < β) (hd : 0 < d) (hκ : 0 < κ) (hμ : SmallCostTail μ κ d)
    (t : ℝ) (m : ℝ → ℝ)
    (hlocal : ∀ᵐ s ∂volume.restrict (Ioi t),
      Tendsto (fun n : ℕ => ∫ C, (assignmentGraph β d κ n C).deficit s / n ∂iidCosts μ)
        atTop (𝓝 (2 * (1 - m s)))) :
    ∀ᵐ C ∂iidCosts μ, Tendsto (fun n => softAssignmentPressure β d κ t n C) atTop
      (𝓝 (2 * t + 2 * ∫ s in Ioi t, (1 - m s))) :=
  ae_tendsto_softAssignmentPressure_of_expected hμ.1 hβ.le d κ t hκ.le
    (tendsto_expected_softAssignmentPressure_of_local hβ hd hκ hμ t m hlocal)

end Certificate

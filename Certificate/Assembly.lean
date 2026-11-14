import Certificate.CompletionModel

/-!
# Combining the finite and limiting estimates

This theorem applies the monomer-removal argument to the actual square
assignment partition function. It isolates the probability estimates
and the limiting soft-pressure calculation needed by the main theorem.
-/

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace Certificate

theorem ae_pressure_limit_of_softPressure_and_completion
    {μ : Measure ℝ} (β d κ : ℝ) {K α limit : ℝ} (hK : 0 ≤ K) (hα : 0 ≤ α)
    {bad : ℕ → Set CostArray} (hbad : (∑' n, iidCosts μ (bad n)) ≠ ∞)
    (hcomp : ∀ (n : ℕ) (C : CostArray), 0 < n → C ∉ bad n →
      ∀ k : ℕ, 0 < k → k ≤ n →
        Completion.deficitPartition β d κ n k C ≤ assignmentPartition β d κ n C *
          Real.exp (K * k * Real.log (Real.exp 1 * n / k) ^ α))
    {b : ℝ → ℝ}
    (hsoft : ∀ z > 0, ∀ᵐ C ∂iidCosts μ,
      Tendsto (fun n ↦ Completion.monomerPressure β d κ n C z) atTop (𝓝 (b z)))
    (hlim : Tendsto b (𝓝[>] (0 : ℝ)) (𝓝 limit)) :
    ∀ᵐ C ∂iidCosts μ, Tendsto (fun n ↦ pressure β d κ n C) atTop (𝓝 limit) := by
  let err : ℕ → ℝ := fun j ↦ 1 / ((j : ℝ) + 1)
  have herr : Tendsto err atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hpos (j : ℕ) : 0 < err j := by dsimp [err]; positivity
  choose cap hcap _ hgap using
    (fun j ↦ Completion.concrete_monomer_pressure_gap β d κ hK hα (hpos j))
  let z : ℕ → ℝ := fun j ↦ min (cap j) (err j)
  have hz (j : ℕ) : 0 < z j := lt_min (hcap j) (hpos j)
  have hzlim : Tendsto z atTop (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within z ?_
      (.of_forall hz)
    refine tendsto_order.mpr ⟨fun x hx ↦ .of_forall (fun j ↦ hx.trans (hz j)), ?_⟩
    intro x hx
    filter_upwards [(tendsto_order.mp herr).2 x hx] with j hj
    exact (min_le_right _ _).trans_lt hj
  apply ae_tendsto_of_monomer_approximation (iidCosts μ)
    (b := fun j n C ↦ Completion.monomerPressure β d κ n C (z j))
    (B := fun j ↦ b (z j)) (err := err) (fun j ↦ hsoft (z j) (hz j)) (hlim.comp hzlim) herr hbad
  intro j n C hn hC
  have hg := hgap j n C hn (hcomp n C hn hC) (z j) (hz j) (min_le_left _ _)
  exact ⟨by linarith [hg.2], by linarith [hg.1]⟩

end Certificate

import Certificate.Assembly
import Certificate.CompletionExpansionFinal
import Certificate.PressureL1
import Mathlib.Analysis.PSeries

/-!
# The hard pressure from its soft limits

The random completion estimate now discharges the exceptional-event and
coefficient hypotheses of the monomer removal argument for the iid array.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace Certificate

/-- The null set of arrays having a negative coordinate is absorbed into the
completion event without changing its probability upper bound. -/
theorem ae_pressure_limit_of_positive_fugacity_limit
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {β d κ : ℝ}
    (hβ : 0 < β) (hd : 0 < d) (hκ : 0 < κ) (hμ : SmallCostTail μ κ d)
    {b : ℝ → ℝ} {p : ℝ}
    (hsoft : ∀ z > 0, ∀ᵐ C ∂iidCosts μ,
      Tendsto (fun n ↦ Completion.monomerPressure β d κ n C z) atTop (𝓝 (b z)))
    (hzero : Tendsto b (𝓝[>] (0 : ℝ)) (𝓝 p)) :
    ∀ᵐ C ∂iidCosts μ, Tendsto (fun n ↦ pressure β d κ n C) atTop (𝓝 p) := by
  let : IsProbabilityMeasure (iidCosts μ) := by unfold iidCosts; infer_instance
  obtain ⟨K, _, bad, hK, _, _, hprob, hcomp, _⟩ :=
    Completion.weightedCompletion_certificate hβ hd hκ (B := 2) (by norm_num) hμ
  have hsum : (∑' n, iidCosts μ (bad n)) ≠ ∞ := by
    exact Completion.tsum_ne_top_of_eventually_le_npow
      (by norm_num : (1 : ℝ) < 2) (by norm_num : (0 : ℝ) ≤ 4)
      (fun n ↦ iidCosts μ (bad n)) (fun _ ↦ measure_ne_top _ _) hprob
  apply ae_pressure_limit_of_softPressure_and_completion β d κ
    (α := max 2 (1 + 1 / d)) hK (le_trans (by norm_num) (le_max_left _ _))
    hsum _ hsoft hzero
  intro n C _ hC k hk hkn
  exact hcomp n k C hk hkn hC

private theorem pressure_le_monomerPressure (β d κ : ℝ) (n : ℕ) (C : CostArray)
    {z : ℝ} (hz : 0 ≤ z) :
    pressure β d κ n C ≤ Completion.monomerPressure β d κ n C z := by
  let Z : ℕ → ℝ := fun k ↦ Completion.deficitPartition β d κ n k C
  have hZ : ∀ k, 0 ≤ Z k := fun k ↦ Completion.deficitPartition_nonneg β d κ n k C
  have h₀ : Z 0 = assignmentPartition β d κ n C := Completion.deficitPartition_zero β d κ n C
  have h := hard_le_monomerPartition n Z z hz hZ
  rw [h₀] at h
  apply div_le_div_of_nonneg_right (Real.log_le_log (assignmentPartition_pos ..) h) (Nat.cast_nonneg n)

private theorem monomerPressure_mono (β d κ : ℝ) (n : ℕ) (C : CostArray)
    {z w : ℝ} (hz : 0 ≤ z) (hzw : z ≤ w) :
    Completion.monomerPressure β d κ n C z ≤ Completion.monomerPressure β d κ n C w := by
  let Z : ℕ → ℝ := fun k ↦ Completion.deficitPartition β d κ n k C
  have hZ : ∀ k, 0 ≤ Z k := fun k ↦ Completion.deficitPartition_nonneg β d κ n k C
  have h₀ : Z 0 = assignmentPartition β d κ n C := Completion.deficitPartition_zero β d κ n C
  have hpos : 0 < monomerPartition n Z z := by
    apply lt_of_lt_of_le _ (hard_le_monomerPartition n Z z hz hZ)
    rw [h₀]
    exact assignmentPartition_pos ..
  apply div_le_div_of_nonneg_right (Real.log_le_log hpos ?_) (Nat.cast_nonneg n)
  unfold monomerPartition
  exact Finset.sum_le_sum fun k _ ↦ mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ hz hzw _) (hZ k)

/-- The almost-sure hard pressure has a finite limit whenever the soft
pressures have deterministic almost-sure limits at positive fugacities. -/
theorem exists_pressure_limit_of_positive_fugacity_limits
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {β d κ : ℝ}
    (hβ : 0 < β) (hd : 0 < d) (hκ : 0 < κ) (hμ : SmallCostTail μ κ d)
    {b : ℝ → ℝ} (hsoft : ∀ z > 0, ∀ᵐ C ∂iidCosts μ,
      Tendsto (fun n ↦ Completion.monomerPressure β d κ n C z) atTop (𝓝 (b z))) :
    ∃ p : ℝ, Tendsto b (𝓝[>] (0 : ℝ)) (𝓝 p) ∧
      ∀ᵐ C ∂iidCosts μ, Tendsto (fun n ↦ pressure β d κ n C) atTop (𝓝 p) := by
  let : IsProbabilityMeasure (iidCosts μ) := by unfold iidCosts; infer_instance
  obtain ⟨K, L, bad, hK, _, _, hprob, hcomp, hneg⟩ :=
    Completion.weightedCompletion_certificate hβ hd hκ (B := 2) (by norm_num) hμ
  have hsum : (∑' n, iidCosts μ (bad n)) ≠ ∞ := by
    exact Completion.tsum_ne_top_of_eventually_le_npow
      (by norm_num : (1 : ℝ) < 2) (by norm_num : (0 : ℝ) ≤ 4)
      (fun n ↦ iidCosts μ (bad n)) (fun _ ↦ measure_ne_top _ _) hprob
  have hgood := ae_eventually_notMem hsum
  have hmono : MonotoneOn b (Ioi 0) := by
    intro z hz w hw hzw
    obtain ⟨C, hzC, hwC⟩ := ((hsoft z hz).and (hsoft w hw)).exists
    exact le_of_tendsto_of_tendsto' hzC hwC
      (fun n ↦ monomerPressure_mono β d κ n C hz.le hzw)
  have hlo : ∀ z > 0, -L ≤ b z := by
    intro z hz
    obtain ⟨C, hzC, hCg⟩ := ((hsoft z hz).and hgood).exists
    apply ge_of_tendsto hzC
    filter_upwards [hCg, eventually_gt_atTop (0 : ℕ)] with n hn hn₀
    have hnegC := hneg n C hn₀ hn
    have hz' := pressure_le_monomerPressure β d κ n C hz.le
    have hp : -L ≤ pressure β d κ n C := by
      have hp' : -pressure β d κ n C ≤ L := (le_max_left _ _).trans hnegC
      linarith
    exact hp.trans hz'
  have hB : BddBelow (b '' Ioi 0) := ⟨-L, by
    rintro _ ⟨z, hz, rfl⟩
    exact hlo z hz⟩
  have hN : (b '' Ioi (0 : ℝ)).Nonempty := ⟨b 1, ⟨1, mem_Ioi.mpr zero_lt_one, rfl⟩⟩
  let p := sInf (b '' Ioi (0 : ℝ))
  have ht : Tendsto b (𝓝[>] (0 : ℝ)) (𝓝 p) := by
    apply tendsto_order.mpr
    constructor
    · intro a ha
      filter_upwards [self_mem_nhdsWithin] with z (hz : 0 < z)
      exact ha.trans_le (csInf_le hB (mem_image_of_mem b hz))
    · intro a ha
      obtain ⟨_, ⟨z, hz, rfl⟩, hza⟩ := exists_lt_of_csInf_lt hN ha
      filter_upwards [Ioo_mem_nhdsGT hz] with w hw
      exact (hmono hw.1 hz hw.2.le).trans_lt hza
  refine ⟨p, ht, ?_⟩
  apply ae_pressure_limit_of_softPressure_and_completion β d κ
    (α := max 2 (1 + 1 / d)) hK (le_trans (by norm_num) (le_max_left _ _))
    hsum _ hsoft ht
  intro n C _ hC k hk hkn
  exact hcomp n k C hk hkn hC

/-- The checked completion event also discharges the exceptional-event
hypotheses for L¹ convergence once the almost-sure limiting pressure is known. -/
theorem pressure_L1_of_ae_limit
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {β d κ q p : ℝ}
    (hβ : 0 < β) (hd : 0 < d) (hκ : 0 < κ) (hq : 0 < q)
    (hμ : SmallCostTail μ κ d) (hM : Integrable (fun c : ℝ ↦ c ^ q) μ)
    (h : ∀ᵐ C ∂iidCosts μ, Tendsto (fun n ↦ pressure β d κ n C) atTop (𝓝 p)) :
    Tendsto (fun n ↦ ∫ C, |pressure β d κ n C - p| ∂iidCosts μ) atTop (𝓝 0) := by
  let B := 2 * (1 / d + 1 / q + 1)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  obtain ⟨_, L, bad, _, hL, hmeas, hprob, _, hneg⟩ :=
    Completion.weightedCompletion_certificate hβ hd hκ hB hμ
  apply pressure_L1_of_ae_of_completion_events hβ hd hκ hq hμ hM h hL
    (show (0 : ℝ) ≤ 4 by norm_num) bad
  filter_upwards [hprob, eventually_gt_atTop (0 : ℕ)] with n hn hn₀
  exact ⟨hmeas n, hn, fun C hC ↦ hneg n C hn₀ hC⟩

end Certificate

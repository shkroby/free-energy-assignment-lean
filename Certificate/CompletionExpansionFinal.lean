import Certificate.CompletionExpansionIteration
import Certificate.CompletionExpansionSum
import Certificate.CompletionExpansionWeights

/-!
# Weighted completion on the random array

Combine the common expansion event, the deterministic augmentation procedure,
and the concentrated sum of the row weights.
-/

open Finset Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace Certificate.Completion

private theorem expansionLog_eq_log {n j : ℕ} (hj : 0 < j) (hjn : j ≤ n) :
    expansionLog n j = Real.log (Real.exp 1 * (n : ℝ) / j) := by
  have hj' : 0 < (j : ℝ) := by exact_mod_cast hj
  have hn' : 0 < (n : ℝ) := hj'.trans_le (by exact_mod_cast hjn)
  rw [mul_div_assoc, Real.log_mul (Real.exp_pos _).ne' (div_pos hn' hj').ne', Real.log_exp]
  rfl

/-- A constant valid both for the count and the total scaled length of all
inserted edges. -/
noncomputable def completionBudgetConstant (A d : ℝ) : ℝ :=
  max 24 (8 * A * (1 + 2 * (1 + 1 / d)) ^ (1 + 1 / d : ℝ))

theorem completionBudgetConstant_ge_one (A d : ℝ) : 1 ≤ completionBudgetConstant A d :=
  (by norm_num : (1 : ℝ) ≤ 24).trans (le_max_left _ _)

/-- On the common expansion event, every matching has a perfect completion
with the two logarithmic budgets of the manuscript. -/
theorem exists_completion_with_log_budgets {n k : ℕ} {C : CostArray}
    {m : Fin n → Option (Fin n)} {A d κ : ℝ}
    (hA : 0 < A) (hd : 0 < d) (hκ : 0 < κ)
    (hC : C ∉ commonExpansionFailure n (expansionCutoff A d κ n))
    (hcost : ∀ p, 0 ≤ C p) (hk : 0 < k) (hkn : k ≤ n)
    (hm : m ∈ matchingsAtDeficit n k) :
    ∃ p : Equiv.Perm (Fin n),
      ((changedRows p m).card : ℝ) ≤
        completionBudgetConstant A d * k * Real.log (Real.exp 1 * n / k) ∧
      insertedLength (scaledCost d κ n C) p m ≤
        completionBudgetConstant A d * k * Real.log (Real.exp 1 * n / k) ^ (1 + 1 / d : ℝ) := by
  obtain ⟨p, hpcount, hplen⟩ := exists_completion_summed_bounds hA hκ hC hcost hm
  let L := expansionLog n k
  have hL : 0 < L := zero_lt_one.trans_le (expansionLog_ge_one hk hkn)
  let b : ℝ := 1 + 1 / d
  have hb : 0 < b := by dsimp [b]; positivity
  have hx₀ : ∑ j ∈ Finset.range k, expansionLog n (j + 1) ≤ 6 * k * L := by
    have hz := sum_expansionLog_rpow_le hk hkn (show (0 : ℝ) < 1 by norm_num)
    norm_num [Real.rpow_one] at hz
    exact hz
  have hx₁ : ∑ j ∈ Finset.range k, 4 * expansionLog n (j + 1) ≤ 24 * k * L := by
    rw [← Finset.mul_sum]
    linarith
  have hy : ∑ j ∈ Finset.range k, 4 * A * expansionLog n (j + 1) ^ b ≤
      (8 * A * (1 + 2 * b) ^ b) * k * L ^ b := by
    calc
      _ = (4 * A) * ∑ j ∈ Finset.range k, expansionLog n (j + 1) ^ b :=
        (Finset.mul_sum ..).symm
      _ ≤ (4 * A) * ((2 * (1 + 2 * b) ^ b) * k * L ^ b) :=
        mul_le_mul_of_nonneg_left (sum_expansionLog_rpow_le hk hkn hb) (by positivity)
      _ = _ := by ring
  refine ⟨p, ?_, ?_⟩
  · rw [← expansionLog_eq_log hk hkn]
    apply (hpcount.trans hx₁).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg k)) hL.le
  · rw [← expansionLog_eq_log hk hkn]
    apply (hplen.trans hy).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Nat.cast_nonneg k))
      (Real.rpow_nonneg hL.le _)

/-- Failure of at least one of the two events used for weighted completion. -/
noncomputable def weightedCompletionFailure (A K₁ β d κ : ℝ) (n : ℕ) : Set CostArray :=
  commonExpansionFailure n (expansionCutoff A d κ n) ∪
    {C | K₁ * n < totalRowWeight β d κ n C}

/-- On the common good event, weighted completion holds for the actual
coefficient at every positive deficit. -/
theorem weightedCompletion_of_not_mem_failure
    {A K₁ β d κ : ℝ} {n k : ℕ} {C : CostArray}
    (hA : 0 < A) (hK₁ : 0 ≤ K₁) (hβ : 0 ≤ β) (hd : 0 < d) (hκ : 0 < κ)
    (hC : C ∉ weightedCompletionFailure A K₁ β d κ n)
    (hcost : ∀ p, 0 ≤ C p) (hk : 0 < k) (hkn : k ≤ n) :
    deficitPartition β d κ n k C ≤ assignmentPartition β d κ n C *
      Real.exp ((β * completionBudgetConstant A d + completionBudgetConstant A d * (2 + K₁)) * k *
        Real.log (Real.exp 1 * n / k) ^ (max 2 (1 + 1 / d) : ℝ)) := by
  classical
  have hExpansion : C ∉ commonExpansionFailure n (expansionCutoff A d κ n) :=
    fun hc => hC (Or.inl hc)
  have hweights : totalRowWeight β d κ n C ≤ K₁ * n :=
    le_of_not_gt (fun hg => hC (Or.inr hg))
  let budget (m : Fin n → Option (Fin n)) (hm : m ∈ matchingsAtDeficit n k) :=
    exists_completion_with_log_budgets hA hd hκ hExpansion hcost hk hkn hm
  let complete (m : Fin n → Option (Fin n)) : Equiv.Perm (Fin n) :=
    if hm : m ∈ matchingsAtDeficit n k then Classical.choose (budget m hm) else Equiv.refl _
  apply weightedCompletion_bound_of_real_budget β d κ hβ n k C complete
    (completionBudgetConstant A d) K₁ (completionBudgetConstant_ge_one _ _) hK₁ hk hkn
  · intro m hm
    unfold complete
    rw [dif_pos hm]
    exact (Classical.choose_spec (budget m hm)).1
  · intro m hm
    unfold complete
    rw [dif_pos hm]
    exact (Classical.choose_spec (budget m hm)).2
  · exact hweights

/-- The simultaneous weighted completion estimate, with an explicit common
exceptional event for the concrete iid assignment model. -/
theorem weightedCompletion_probability {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {β d κ B : ℝ} (hβ : 0 < β) (hd : 0 < d) (hκ : 0 < κ) (hB : 0 ≤ B)
    (hμ : SmallCostTail μ κ d) :
    ∃ (K : ℝ) (bad : ℕ → Set CostArray), 0 ≤ K ∧
      (∀ᶠ n : ℕ in atTop, iidCosts μ (bad n) ≤
        ENNReal.ofReal (3 * (n : ℝ) ^ (-B)) + ENNReal.ofReal (Real.exp (-(n : ℝ)))) ∧
      (∀ (n k : ℕ) (C : CostArray), 0 < k → k ≤ n → C ∉ bad n → (∀ p, 0 ≤ C p) →
        deficitPartition β d κ n k C ≤ assignmentPartition β d κ n C *
          Real.exp (K * k * Real.log (Real.exp 1 * n / k) ^ (max 2 (1 + 1 / d) : ℝ))) := by
  obtain ⟨A, hA, hexp⟩ := eventually_measure_expansionCutoffFailure_le hd hκ hB hμ
  obtain ⟨K₁, hK₁, hweight⟩ := measure_totalRowWeight_gt_le hβ hd hκ hμ
  let K₀ := completionBudgetConstant A d
  have hK₀ : 0 ≤ K₀ := zero_le_one.trans (completionBudgetConstant_ge_one _ _)
  refine ⟨β * K₀ + K₀ * (2 + K₁), weightedCompletionFailure A K₁ β d κ, by positivity, ?_, ?_⟩
  · filter_upwards [hexp, eventually_gt_atTop (0 : ℕ)] with n hn hn'
    apply (measure_union_le _ _).trans
    exact add_le_add hn (hweight n hn')
  · intro n k C hk hkn hC hcost
    exact weightedCompletion_of_not_mem_failure hA hK₁ hβ.le hd hκ hC hcost hk hkn

theorem measurableSet_weightedCompletionFailure (A K₁ β d κ : ℝ) (n : ℕ) :
    MeasurableSet (weightedCompletionFailure A K₁ β d κ n) :=
  (measurableSet_commonExpansionFailure n _).union
    (measurableSet_lt measurable_const (measurable_totalRowWeight β d κ n))

/-- Complete the empty matching to get a bounded negative part of the pressure
everywhere on the common good event. -/
theorem negativePressure_le_of_not_mem_failure
    {A K₁ β d κ : ℝ} {n : ℕ} {C : CostArray}
    (hA : 0 < A) (hβ : 0 ≤ β) (hd : 0 < d) (hκ : 0 < κ)
    (hC : C ∉ weightedCompletionFailure A K₁ β d κ n)
    (hcost : ∀ p, 0 ≤ C p) (hn : 0 < n) :
    negativePressure β d κ n C ≤ β * completionBudgetConstant A d := by
  let empty : Fin n → Option (Fin n) := fun _ => none
  have hs : AugmentingPath.matchedRows empty = ∅ := by ext i; simp [empty]
  have hm : empty ∈ matchingsAtDeficit n n := by
    apply mem_matchingsAtDeficit.mpr
    constructor
    · intro i j c h _
      simp [empty] at h
    · simp [hs]
  have hExpansion : C ∉ commonExpansionFailure n (expansionCutoff A d κ n) :=
    fun hc => hC (Or.inl hc)
  obtain ⟨p, _, hlen⟩ := exists_completion_with_log_budgets
    hA hd hκ hExpansion hcost hn le_rfl hm
  have hchanged : changedRows p empty = Finset.univ := by ext i; simp [empty]
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have he : Real.log (Real.exp 1 * (n : ℝ) / n) = 1 := by
    rw [mul_div_cancel_right₀ _ hn'.ne', Real.log_exp]
  let K₀ := completionBudgetConstant A d
  have hzero : 0 ≤ K₀ := zero_le_one.trans (completionBudgetConstant_ge_one _ _)
  have ht : ∑ i, scaledCost d κ n C i (p i) ≤ K₀ * (n : ℝ) := by
    simpa only [insertedLength, hchanged, he, Real.one_rpow, mul_one] using hlen
  have hpart : Real.exp (-β * (K₀ * n)) ≤ assignmentPartition β d κ n C := by
    calc
      _ ≤ perfectWeight β (scaledCost d κ n C) p := by
        rw [perfectWeight_exp]
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left ht (neg_nonpos.mpr hβ))
      _ ≤ _ := by
        rw [assignmentPartition_eq_sum_perfectWeight]
        exact Finset.single_le_sum
          (f := perfectWeight β (scaledCost d κ n C))
          (fun σ _ => (perfectWeight_pos β (scaledCost d κ n C) σ).le)
          (Finset.mem_univ p)
  have hlog := Real.log_le_log (Real.exp_pos _) hpart
  rw [Real.log_exp] at hlog
  unfold negativePressure
  refine max_le ?_ (mul_nonneg hβ hzero)
  unfold pressure
  rw [← neg_div, div_le_iff₀ hn']
  linarith

/-- The complete finite-size weighted completion certificate for the iid cost law.
The bad event is measurable and contains all arrays with at least one negative entry.
Thus both finite-size conclusions are pointwise outside that event. -/
theorem weightedCompletion_certificate {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {β d κ B : ℝ} (hβ : 0 < β) (hd : 0 < d) (hκ : 0 < κ) (hB : 0 ≤ B)
    (hμ : SmallCostTail μ κ d) :
    ∃ (K L : ℝ) (bad : ℕ → Set CostArray), 0 ≤ K ∧ 0 ≤ L ∧
      (∀ n, MeasurableSet (bad n)) ∧
      (∀ᶠ n : ℕ in atTop, iidCosts μ (bad n) ≤ ENNReal.ofReal (4 * (n : ℝ) ^ (-B))) ∧
      (∀ (n k : ℕ) (C : CostArray), 0 < k → k ≤ n → C ∉ bad n →
        deficitPartition β d κ n k C ≤ assignmentPartition β d κ n C *
          Real.exp (K * k * Real.log (Real.exp 1 * n / k) ^ (max 2 (1 + 1 / d) : ℝ))) ∧
      (∀ (n : ℕ) (C : CostArray), 0 < n → C ∉ bad n → negativePressure β d κ n C ≤ L) := by
  obtain ⟨A, hA, hexp⟩ := eventually_measure_expansionCutoffFailure_le hd hκ hB hμ
  obtain ⟨K₁, hK₁, hweight⟩ := measure_totalRowWeight_gt_le hβ hd hκ hμ
  let K₀ := completionBudgetConstant A d
  have hK₀ : 0 ≤ K₀ := zero_le_one.trans (completionBudgetConstant_ge_one _ _)
  let negCost : Set CostArray := {C | ¬ ∀ p, 0 ≤ C p}
  have hnegM : MeasurableSet negCost := by
    have hN : negCost = (⋂ p : ℕ × ℕ, {C : CostArray | 0 ≤ C p})ᶜ := by ext C; simp [negCost]
    rw [hN]
    exact (MeasurableSet.iInter (fun p =>
      measurableSet_le measurable_const (measurable_pi_apply p))).compl
  have hzero : iidCosts μ negCost = 0 := ae_iff.mp (ae_cost_nonneg μ hμ.1)
  let bad (n : ℕ) := weightedCompletionFailure A K₁ β d κ n ∪ negCost
  have hcost (n : ℕ) (C : CostArray) (hC : C ∉ bad n) : ∀ p, 0 ≤ C p :=
    not_not.mp (fun h => hC (Or.inr h))
  have hgood (n : ℕ) (C : CostArray) (hC : C ∉ bad n) :
      C ∉ weightedCompletionFailure A K₁ β d κ n :=
    fun h => hC (Or.inl h)
  refine ⟨β * K₀ + K₀ * (2 + K₁), β * K₀, bad, by positivity, by positivity,
    fun n => (measurableSet_weightedCompletionFailure A K₁ β d κ n).union hnegM, ?_, ?_, ?_⟩
  · filter_upwards [hexp, eventually_gt_atTop (0 : ℕ), eventually_exp_neg_size_le_rpow B]
      with n hn hn' he
    calc
      _ ≤ iidCosts μ (weightedCompletionFailure A K₁ β d κ n) + iidCosts μ negCost :=
        measure_union_le _ _
      _ = iidCosts μ (weightedCompletionFailure A K₁ β d κ n) := by rw [hzero, add_zero]
      _ ≤ ENNReal.ofReal (3 * (n : ℝ) ^ (-B)) + ENNReal.ofReal (Real.exp (-(n : ℝ))) :=
        (measure_union_le _ _).trans (add_le_add hn (hweight n hn'))
      _ ≤ ENNReal.ofReal (3 * (n : ℝ) ^ (-B)) + ENNReal.ofReal ((n : ℝ) ^ (-B)) :=
        add_le_add le_rfl (ENNReal.ofReal_le_ofReal he)
      _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
  · intro n k C hk hkn hC
    exact weightedCompletion_of_not_mem_failure hA hK₁ hβ.le hd hκ
      (hgood n C hC) (hcost n C hC) hk hkn
  · intro n C hn hC
    exact negativePressure_le_of_not_mem_failure hA hβ.le hd hκ
      (hgood n C hC) (hcost n C hC) hn

end Certificate.Completion

import Certificate.CompletionProbability
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# The manuscript cutoff and the simultaneous expansion event

The cutoff is expressed in the original cost units so that it can be evaluated
directly under the cost distribution's CDF.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

namespace Certificate.Completion

/-- Original cost cutoff (A [\log(en/j)]^{1/d} / (\kappa n)^{1/d}). -/
noncomputable def expansionCutoff (A d κ : ℝ) (n j : ℕ) : ℝ :=
  A * (expansionLog n j / (κ * n)) ^ (1 / d : ℝ)

theorem expansionCutoff_eq_scaled (A : ℝ) {d κ : ℝ} (hκ : 0 < κ)
    {n j : ℕ} (hj : 0 < j) (hjn : j ≤ n) :
    expansionCutoff A d κ n j = A * expansionLog n j ^ (1 / d : ℝ) / lengthScale d κ n := by
  unfold expansionCutoff lengthScale
  rw [Real.div_rpow (zero_le_one.trans (expansionLog_ge_one hj hjn)) (by positivity),
    mul_div_assoc]

private theorem tendsto_log_size_div_size :
    Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using
      (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 by norm_num)).tendsto_div_nhds_zero
  exact h.comp (tendsto_natCast_atTop_atTop (R := ℝ))

private theorem tendsto_expansionLog_one_div_size :
    Tendsto (fun n : ℕ => expansionLog n 1 / (n : ℝ)) atTop (𝓝 0) := by
  have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_div_atTop 1
  simpa [expansionLog, add_div] using hinv.add tendsto_log_size_div_size

private theorem tendsto_expansionCutoff_one (A : ℝ) {d κ : ℝ} (hd : 0 < d) :
    Tendsto (fun n : ℕ => expansionCutoff A d κ n 1) atTop (𝓝 0) := by
  have hlin : Tendsto (fun n : ℕ => expansionLog n 1 / (κ * n)) atTop (𝓝 0) := by
    simpa [div_div, mul_comm] using tendsto_expansionLog_one_div_size.div_const κ
  simpa [expansionCutoff] using (hlin.rpow_const_nhds_zero (one_div_pos.mpr hd)).const_mul A

/-- The CDF asymptotic supplies the manuscript's lower bound on each retention
probability, uniformly over all positive deficits. -/
theorem eventually_expansionCutoff_cdf_lower {μ : Measure ℝ} {A d κ : ℝ}
    (hA : 0 < A) (hd : 0 < d) (hκ : 0 < κ) (h : SmallCostTail μ κ d) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, 0 < j → j ≤ n →
      A ^ d / 2 / (n : ℝ) * expansionLog n j ≤ cdf μ (expansionCutoff A d κ n j) := by
  have hcdf := (tendsto_order.mp h.2).1 (1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hcdf with ⟨s, hs, hsub⟩
  rcases Metric.mem_nhds_iff.mp hs with ⟨δ, hδ, hball⟩
  have hsmall := (tendsto_order.mp (tendsto_expansionCutoff_one A (κ := κ) hd)).2 δ hδ
  filter_upwards [hsmall] with n hn j hj hjn
  have hn₀ : 0 < n := hj.trans_le hjn
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn₀
  have hκn : 0 < κ * (n : ℝ) := mul_pos hκ hn'
  have hL : 0 < expansionLog n j := zero_lt_one.trans_le (expansionLog_ge_one hj hjn)
  have hbase : 0 < expansionLog n j / (κ * n) := div_pos hL hκn
  let t := expansionCutoff A d κ n j
  have ht : 0 < t := mul_pos hA (Real.rpow_pos_of_pos hbase _)
  have ht₁ : t ≤ expansionCutoff A d κ n 1 := by
    apply mul_le_mul_of_nonneg_left _ hA.le
    apply Real.rpow_le_rpow hbase.le _ (one_div_pos.mpr hd).le
    exact div_le_div_of_nonneg_right (expansionLog_antitone hn₀ Nat.one_pos hj) hκn.le
  have htδ : t < δ := ht₁.trans_lt hn
  have hmem : t ∈ s ∩ Ioi (0 : ℝ) := by
    refine ⟨hball ?_, ht⟩
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht] using htδ
  have hratio : (1 / 2 : ℝ) < cdf μ t / (κ * t ^ d) := hsub hmem
  have hineq := (lt_div_iff₀ (mul_pos hκ (Real.rpow_pos_of_pos ht d))).mp hratio
  have hpow : t ^ d = A ^ d * (expansionLog n j / (κ * n)) := by
    unfold t expansionCutoff
    rw [Real.mul_rpow hA.le (Real.rpow_nonneg hbase.le _), ← Real.rpow_mul hbase.le,
      one_div_mul_cancel hd.ne', Real.rpow_one]
  rw [hpow] at hineq
  refine le_of_eq_of_le ?_ hineq.le
  field_simp

/-- At the exact logarithmic cost cutoff of the manuscript, the joint failure
probability has a power-law term and an exponentially small term. -/
theorem eventually_measure_expansionCutoffFailure_le_exp {μ : Measure ℝ}
    [IsProbabilityMeasure μ] {d κ B : ℝ} (hd : 0 < d) (hκ : 0 < κ) (hB : 0 ≤ B)
    (h : SmallCostTail μ κ d) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ n : ℕ in atTop,
      iidCosts μ (commonExpansionFailure n (expansionCutoff A d κ n)) ≤
        (2 * (n : ℝ≥0∞) ^ 2) * ENNReal.ofReal (Real.exp (-(B + 2) * Real.log (n : ℝ))) +
          (n : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(n : ℝ))) := by
  let c := max (4 / 3 * (B + 13)) (6400 * (Real.log 4 + 1))
  have hc₁ : 4 / 3 * (B + 13) ≤ c := le_max_left _ _
  have hc₂ : 6400 * (Real.log 4 + 1) ≤ c := le_max_right _ _
  have hc : 0 < c := by linarith
  let A := (2 * c) ^ (1 / d : ℝ)
  have hA : 0 < A := Real.rpow_pos_of_pos (by positivity) _
  have hA' : A ^ d / 2 = c := by
    unfold A
    rw [← Real.rpow_mul (by positivity : 0 ≤ 2 * c), one_div_mul_cancel hd.ne', Real.rpow_one]
    ring
  refine ⟨A, hA, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (80 : ℕ),
    eventually_expansionCutoff_cdf_lower hA hd hκ h] with n hn hretention
  refine measure_commonExpansionFailure_le μ n (expansionCutoff A d κ n) c B hn hc.le hB
    (by linarith) (by linarith) ?_
  intro j hj hjn
  simpa only [hA'] using hretention j hj hjn

/-- The common expansion event at the manuscript's cutoff has failure probability
at most `3 n^(-B)` for all sufficiently large `n`. -/
theorem eventually_measure_expansionCutoffFailure_le {μ : Measure ℝ}
    [IsProbabilityMeasure μ] {d κ B : ℝ} (hd : 0 < d) (hκ : 0 < κ) (hB : 0 ≤ B)
    (h : SmallCostTail μ κ d) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ n : ℕ in atTop,
      iidCosts μ (commonExpansionFailure n (expansionCutoff A d κ n)) ≤
        ENNReal.ofReal (3 * (n : ℝ) ^ (-B)) := by
  obtain ⟨A, hA, hfailure⟩ := eventually_measure_expansionCutoffFailure_le_exp hd hκ hB h
  have hlog := (tendsto_order.mp (tendsto_log_size_div_size.const_mul (B + 1))).2 1
    (by simp : (B + 1) * (0 : ℝ) < 1)
  refine ⟨A, hA, ?_⟩
  filter_upwards [hfailure, hlog, eventually_gt_atTop (0 : ℕ)] with n hf hl hn
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hlam : (B + 1) * Real.log (n : ℝ) < (n : ℝ) := by
    change (B + 1) * (Real.log (n : ℝ) / n) < 1 at hl
    rw [← mul_div_assoc] at hl
    exact (div_lt_one hn').mp hl
  have hpow : (n : ℝ) ^ (2 : ℕ) = Real.exp (2 * Real.log (n : ℝ)) := by
    simpa only [Nat.cast_ofNat, Real.exp_log hn'] using (Real.exp_nat_mul (Real.log n) 2).symm
  have hs : 2 * (n : ℝ) ^ (2 : ℕ) * Real.exp (-(B + 2) * Real.log (n : ℝ)) =
      2 * (n : ℝ) ^ (-B) := by
    rw [hpow, mul_assoc, ← Real.exp_add, Real.rpow_def_of_pos hn']
    congr 2
    ring
  have hc : (n : ℝ) * Real.exp (-(n : ℝ)) ≤ (n : ℝ) ^ (-B) := by
    calc
      _ = Real.exp (Real.log (n : ℝ) - n) := by
        rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hn']
      _ ≤ _ := by
        rw [Real.rpow_def_of_pos hn']
        exact Real.exp_le_exp.mpr (by linarith)
  apply hf.trans
  have hsen : (2 * (n : ℝ≥0∞) ^ 2) * ENNReal.ofReal (Real.exp (-(B + 2) * Real.log (n : ℝ))) =
      ENNReal.ofReal (2 * (n : ℝ) ^ (2 : ℕ) * Real.exp (-(B + 2) * Real.log (n : ℝ))) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ)),
      ENNReal.ofReal_pow hn'.le, ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]
  have hcen : (n : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(n : ℝ))) =
      ENNReal.ofReal ((n : ℝ) * Real.exp (-(n : ℝ))) := by
    rw [ENNReal.ofReal_mul hn'.le, ENNReal.ofReal_natCast]
  rw [hsen, hcen, ← ENNReal.ofReal_add (by positivity) (by positivity), hs]
  exact ENNReal.ofReal_le_ofReal (by linarith)

theorem eventually_exp_neg_size_le_rpow (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, Real.exp (-(n : ℝ)) ≤ (n : ℝ) ^ (-B) := by
  have hlog := (tendsto_order.mp (tendsto_log_size_div_size.const_mul B)).2 1
    (by simp : B * (0 : ℝ) < 1)
  filter_upwards [hlog, eventually_gt_atTop (0 : ℕ)] with n h hn
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  change B * (Real.log (n : ℝ) / n) < 1 at h
  rw [← mul_div_assoc] at h
  have hl := (div_lt_one hn').mp h
  rw [Real.rpow_def_of_pos hn']
  exact Real.exp_le_exp.mpr (by linarith)

theorem tsum_ne_top_of_eventually_le_npow {B K : ℝ} (hB : 1 < B) (hK : 0 ≤ K)
    (a : ℕ → ℝ≥0∞) (hfin : ∀ n, a n ≠ ∞)
    (hb : ∀ᶠ n : ℕ in atTop, a n ≤ ENNReal.ofReal (K * (n : ℝ) ^ (-B))) :
    (∑' n, a n) ≠ ∞ := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hb
  have hseries : Summable (fun n : ℕ => K * (n : ℝ) ^ (-B)) :=
    (Real.summable_nat_rpow.mpr (by linarith : -B < -1)).mul_left K
  have htail' : Summable (fun k : ℕ => K * ((k + N : ℕ) : ℝ) ^ (-B)) :=
    (summable_nat_add_iff N).mpr hseries
  have htail : Summable (fun k : ℕ => (a (k + N)).toReal) := by
    apply Summable.of_nonneg_of_le (fun _ => ENNReal.toReal_nonneg) _ htail'
    intro k
    have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hN (k + N) (Nat.le_add_left N k))
    rwa [ENNReal.toReal_ofReal (by positivity)] at hb
  have hfull : Summable (fun k : ℕ => (a k).toReal) := (summable_nat_add_iff N).mp htail
  simpa only [ENNReal.ofReal_toReal (hfin _)] using hfull.tsum_ofReal_ne_top

/-- In particular, along one infinite array the cheap-edge expansion and cut
conditions both hold for all sufficiently large matrix sizes almost surely. -/
theorem ae_eventually_not_mem_expansionCutoffFailure {μ : Measure ℝ}
    [IsProbabilityMeasure μ] {d κ : ℝ} (hd : 0 < d) (hκ : 0 < κ)
    (h : SmallCostTail μ κ d) :
    ∃ A : ℝ, 0 < A ∧ ∀ᵐ C ∂iidCosts μ, ∀ᶠ n : ℕ in atTop,
      C ∉ commonExpansionFailure n (expansionCutoff A d κ n) := by
  obtain ⟨A, hA, hbound⟩ := eventually_measure_expansionCutoffFailure_le hd hκ
    (show (0 : ℝ) ≤ 2 by norm_num) h
  let bad (n : ℕ) := commonExpansionFailure n (expansionCutoff A d κ n)
  let : IsProbabilityMeasure (iidCosts μ) := by unfold iidCosts; infer_instance
  have hfin (n : ℕ) : iidCosts μ (bad n) ≠ ∞ := measure_ne_top _ _
  have hsum : (∑' n, iidCosts μ (bad n)) ≠ ∞ :=
    tsum_ne_top_of_eventually_le_npow (by norm_num) (by norm_num)
      (fun n => iidCosts μ (bad n)) hfin hbound
  exact ⟨A, hA, ae_eventually_notMem hsum⟩

end Certificate.Completion

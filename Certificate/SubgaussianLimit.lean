import Certificate.Arrivals
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-! Borel–Cantelli for the bounded-differences variance proxy of the soft pressure. -/

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology ENNReal NNReal

namespace Certificate

theorem eventually_logSquared_div_size_le {a : ℝ} (ha : 0 < a) :
    ∀ᶠ n : ℕ in atTop,
      Real.log (1 + (n : ℝ) * a) ^ 2 / (n : ℝ) ≤ 1 / (n : ℝ) ^ (1 / 2 : ℝ) := by
  have ht := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 4 by norm_num)).tendsto_div_nhds_zero
  have hcast : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have ht' : Tendsto (fun n : ℕ ↦
      (Real.log (1 + a) + Real.log (n : ℝ)) / (n : ℝ) ^ (1 / 4 : ℝ)) atTop (𝓝 0) := by
    have hden := (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 4 by norm_num)).comp hcast
    have hconst := hden.const_div_atTop (Real.log (1 + a))
    simpa only [add_div, zero_add, Function.comp_def] using hconst.add (ht.comp hcast)
  filter_upwards [(tendsto_order.mp ht').2 (1 : ℝ) zero_lt_one,
    eventually_ge_atTop (1 : ℕ)] with n hlimit hn
  have hn₁ : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hn₀ : 0 < (n : ℝ) := zero_lt_one.trans_le hn₁
  have hp := Real.rpow_pos_of_pos hn₀ (1 / 4 : ℝ)
  have hlog₀ : 0 ≤ Real.log (1 + (n : ℝ) * a) :=
    Real.log_nonneg (le_add_of_nonneg_right (mul_nonneg hn₀.le ha.le))
  have hlog : Real.log (1 + (n : ℝ) * a) ≤ Real.log (1 + a) + Real.log (n : ℝ) := by
    rw [← Real.log_mul (by positivity) hn₀.ne']
    apply Real.log_le_log (by positivity)
    nlinarith [hn₁]
  have hsmall := hlog.trans ((div_lt_one hp).mp hlimit).le
  have hsq := pow_le_pow_left₀ hlog₀ hsmall 2
  have hs : ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 2 = (n : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_ofNat, ← Real.rpow_mul hn₀.le]
    norm_num
  have hhalf : (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) = (n : ℝ) := by
    rw [← Real.rpow_add hn₀, show (1 : ℝ) / 2 + 1 / 2 = 1 by norm_num, Real.rpow_one]
  rw [hs] at hsq
  apply (div_le_div_iff₀ hn₀ (Real.rpow_pos_of_pos hn₀ _)).mpr
  simpa only [one_mul, hhalf] using mul_le_mul_of_nonneg_right hsq
    (Real.rpow_nonneg hn₀.le (1 / 2 : ℝ))

/-- A sequence with sub-Gaussian variance proxies eventually bounded by
a fixed multiple of the inverse square root of the size converges almost surely to zero. -/
theorem ae_tendsto_zero_of_subgaussian_stretched_decay {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ} {v : ℕ → ℝ≥0}
    (h : ∀ n, HasSubgaussianMGF (X n) (v n) μ)
    {K : ℝ} (hK : 0 < K)
    (hv : ∀ᶠ n : ℕ in atTop, 0 < v n ∧ (v n : ℝ) ≤ K / (n : ℝ) ^ (1 / 2 : ℝ)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X n ω) atTop (𝓝 0) := by
  have hsum (ε : ℝ) (hε : 0 < ε) :
      (∑' n, μ {ω | ε ≤ |X n ω|}) ≠ ∞ := by
    let c := ε ^ 2 / (2 * K)
    have hc : 0 < c := by positivity
    let Q : ℕ → ℝ := fun n ↦ 2 * Real.exp (-(c * (n : ℝ) ^ (1 / 2 : ℝ)))
    have hQ : Summable Q :=
      (summable_nat_stretchedExp hc (show (0 : ℝ) < 1 / 2 by norm_num)).mul_left 2
    have hQfin : (∑' n, ENNReal.ofReal (Q n)) < ∞ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ by positivity) hQ]
      exact ENNReal.ofReal_lt_top
    have htail : ∀ᶠ n : ℕ in atTop, μ {ω | ε ≤ |X n ω|} ≤ ENNReal.ofReal (Q n) := by
      filter_upwards [hv, eventually_gt_atTop (0 : ℕ)] with n hn hn'
      have hn₀ : 0 < (n : ℝ) := Nat.cast_pos.mpr hn'
      have hs : 0 < (n : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hn₀ _
      have hv₀ : 0 < (v n : ℝ) := by exact_mod_cast hn.1
      have hup : Real.exp (-ε ^ 2 / (2 * (v n : ℝ))) ≤
          Real.exp (-(c * (n : ℝ) ^ (1 / 2 : ℝ))) := by
        apply Real.exp_le_exp.mpr
        rw [neg_div]
        apply neg_le_neg_iff.mpr
        calc
          c * (n : ℝ) ^ (1 / 2 : ℝ) = ε ^ 2 / (2 * (K / (n : ℝ) ^ (1 / 2 : ℝ))) := by
            unfold c
            field_simp
          _ ≤ _ := div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
            (mul_le_mul_of_nonneg_left hn.2 (by norm_num))
      have hplus : μ {ω | ε ≤ X n ω} ≤ ENNReal.ofReal (Real.exp (-ε ^ 2 / (2 * (v n : ℝ)))) := by
        rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
        exact ENNReal.ofReal_le_ofReal ((h n).measure_ge_le hε.le)
      have hminus : μ {ω | ε ≤ -(X n ω)} ≤ ENNReal.ofReal (Real.exp (-ε ^ 2 / (2 * (v n : ℝ)))) := by
        rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
        exact ENNReal.ofReal_le_ofReal ((h n).neg.measure_ge_le hε.le)
      have hSet : {ω | ε ≤ |X n ω|} = {ω | ε ≤ X n ω} ∪ {ω | ε ≤ -(X n ω)} := by
        ext ω
        simp [abs_eq_max_neg]
      rw [hSet]
      calc
        _ ≤ μ {ω | ε ≤ X n ω} + μ {ω | ε ≤ -(X n ω)} := measure_union_le _ _
        _ ≤ ENNReal.ofReal (Real.exp (-(c * (n : ℝ) ^ (1 / 2 : ℝ)))) +
            ENNReal.ofReal (Real.exp (-(c * (n : ℝ) ^ (1 / 2 : ℝ)))) :=
          add_le_add (hplus.trans (ENNReal.ofReal_le_ofReal hup))
            (hminus.trans (ENNReal.ofReal_le_ofReal hup))
        _ = _ := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← two_mul]
    obtain ⟨N, hN⟩ := eventually_atTop.mp htail
    let M (n : ℕ) : ℝ≥0∞ := if n < N then 1 else 0
    have hMfin : (∑' n : ℕ, (M n : ℝ≥0∞)) < ∞ := by
      rw [tsum_eq_sum (s := Finset.range N)]
      · simp [M]
      · intro n hn
        simpa [M, Finset.mem_range] using hn
    have hle : (∑' n, μ {ω | ε ≤ |X n ω|}) ≤
        ∑' n, (M n + ENNReal.ofReal (Q n)) := by
      apply ENNReal.tsum_le_tsum
      intro n
      by_cases hn : n < N
      · exact prob_le_one.trans (by simp [M, hn])
      · simpa [M, hn] using hN n (le_of_not_gt hn)
    rw [ENNReal.tsum_add] at hle
    exact (lt_of_le_of_lt hle (ENNReal.add_lt_top.mpr ⟨hMfin, hQfin⟩)).ne
  have he (j : ℕ) :
      ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, |X n ω| < 1 / ((j : ℝ) + 1) := by
    have hh := ae_eventually_notMem (hsum _ (by positivity : 0 < 1 / ((j : ℝ) + 1)))
    simpa only [mem_ofPred_eq, not_le] using hh
  filter_upwards [ae_all_iff.mpr he] with ω hω
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hε
  filter_upwards [hω j] with n hn
  simpa only [Real.dist_eq, sub_zero] using hn.trans hj

end Certificate

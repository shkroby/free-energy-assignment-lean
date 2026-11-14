import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
# Removing monomers

Deterministic estimates from the manuscript's section “From partial to perfect matchings”.
The completion estimate enters as a bound on positive coefficients; the graph and the proof
of the estimate are independent of the comparison and limit arguments below.
-/

open scoped BigOperators Topology ENNReal
open Filter Set MeasureTheory

namespace Certificate

/-- The finite monomer partition function, grouped by the deficit (k). -/
noncomputable def monomerPartition (n : ℕ) (Z : ℕ → ℝ) (z : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), z ^ (2 * k) * Z k

theorem hard_le_monomerPartition (n : ℕ) (Z : ℕ → ℝ) (z : ℝ)
    (hz : 0 ≤ z) (hZ : ∀ k, 0 ≤ Z k) :
    Z 0 ≤ monomerPartition n Z z := by
  classical
  have h := Finset.single_le_sum
    (s := Finset.range (n + 1))
    (f := fun k : ℕ ↦ z ^ (2 * k) * Z k)
    (fun k _ ↦ mul_nonneg (pow_nonneg hz _) (hZ k))
    (a := 0) (by simp)
  simpa [monomerPartition] using h

/-- A coefficient bound near deficit zero and a penalty suppressing larger deficits
give a finite-size pressure comparison. -/
theorem monomer_pressure_gap {n : ℕ} {Z : ℕ → ℝ} {z ε : ℝ}
    (hn : 0 < n) (hZ₀ : 0 < Z 0) (hZ : ∀ k, 0 ≤ Z k) (hz : 0 < z)
    (hcoeff : ∀ k ≤ n, z ^ (2 * k) * Z k ≤ Z 0 * Real.exp ((n : ℝ) * ε)) :
    0 ≤ Real.log (monomerPartition n Z z) / n - Real.log (Z 0) / n ∧
    Real.log (monomerPartition n Z z) / n - Real.log (Z 0) / n ≤
      Real.log ((n : ℝ) + 1) / n + ε := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hlo := hard_le_monomerPartition n Z z hz.le hZ
  have hsoft := hZ₀.trans_le hlo
  have hup : monomerPartition n Z z ≤
      (((n : ℝ) + 1) * Z 0) * Real.exp ((n : ℝ) * ε) := by
    calc
      monomerPartition n Z z ≤
          ∑ _k ∈ Finset.range (n + 1), Z 0 * Real.exp ((n : ℝ) * ε) :=
        Finset.sum_le_sum (fun k hk ↦ hcoeff k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)))
      _ = _ := by simp [nsmul_eq_mul, Nat.cast_add, mul_assoc]
  have hlog := Real.log_le_log hsoft hup
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero _),
    Real.log_mul (by positivity) hZ₀.ne', Real.log_exp] at hlog
  constructor
  · exact sub_nonneg.mpr (div_le_div_of_nonneg_right (Real.log_le_log hZ₀ hlo) hn'.le)
  · rw [← sub_div, div_le_iff₀ hn']
    have he : (Real.log ((n : ℝ) + 1) / n + ε) * n =
        Real.log ((n : ℝ) + 1) + (n : ℝ) * ε := by
      rw [add_mul, div_mul_cancel₀ _ hn'.ne', mul_comm ε]
    rw [he]
    linarith

/-- The completion profile (K u log(e/u)^\alpha), for positive deficit fraction (u). -/
noncomputable def deficitProfile (K α u : ℝ) : ℝ :=
  K * (u * (Real.log (Real.exp 1 / u)) ^ α)

theorem tendsto_deficitProfile (K α : ℝ) :
    Tendsto (deficitProfile K α) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h := (isLittleO_abs_log_rpow_rpow_nhdsGT_zero α
    (show (-1 : ℝ) < 0 by norm_num)).tendsto_div_nhds_zero
  have hscale : Tendsto (fun u : ℝ ↦ u / Real.exp 1) (𝓝[>] (0 : ℝ)) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hc : ContinuousAt (fun u : ℝ ↦ u / Real.exp 1) 0 :=
        (continuous_id.div_const (Real.exp 1)).continuousAt
      have h₀ : Tendsto (fun u : ℝ ↦ u / Real.exp 1) (𝓝 (0 : ℝ)) (𝓝 0) := by
        simpa only [zero_div] using hc.tendsto
      exact h₀.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with u (hu : 0 < u)
      exact div_pos hu (Real.exp_pos 1)
  have hm := (h.comp hscale).const_mul (K * Real.exp 1)
  simp only [mul_zero] at hm
  refine hm.congr' ?_
  have hnear : ∀ᶠ u in 𝓝[>] (0 : ℝ), u < Real.exp 1 :=
    (eventually_lt_nhds (Real.exp_pos 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hnear] with u (hu : 0 < u) hu'
  change K * Real.exp 1 * (|Real.log (u / Real.exp 1)| ^ α / (u / Real.exp 1) ^ (-1 : ℝ)) = _
  rw [Real.rpow_neg_one, div_inv_eq_mul, abs_of_nonpos (Real.log_nonpos (by positivity)
    ((div_le_one (Real.exp_pos 1)).mpr hu'.le)), ← Real.log_inv, inv_div, deficitProfile]
  field_simp

/-- A sufficiently small fugacity makes all weighted coefficients at most
(Z_0 e^{n\varepsilon}), using the manuscript's real (not rounded) exponent. -/
theorem small_fugacity_bound {K α ε : ℝ}
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hε : 0 < ε) :
    ∃ z₀ : ℝ, 0 < z₀ ∧ z₀ ≤ 1 ∧ ∀ ⦃z u : ℝ⦄,
    0 < z → z ≤ z₀ → 0 < u → u ≤ 1 →
    deficitProfile K α u + 2 * u * Real.log z ≤ ε := by
  have hsmall := (tendsto_order.mp (tendsto_deficitProfile K α)).2 ε hε
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hsmall with ⟨s, hs, hsub⟩
  rcases Metric.mem_nhds_iff.mp hs with ⟨δ, hδ, hball⟩
  let t := min δ 1
  have ht : 0 < t := lt_min hδ zero_lt_one
  have ht' : t ≤ 1 := min_le_right _ _
  let L : ℝ := K * (Real.log (Real.exp 1 / t)) ^ α
  have hlog_pos : ∀ {a : ℝ}, 0 < a → a ≤ 1 → 0 ≤ Real.log (Real.exp 1 / a) := by
    intro a ha ha'
    apply Real.log_nonneg
    rw [le_div_iff₀ ha, one_mul]
    have he : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp_iff.mpr zero_le_one
    exact ha'.trans he
  have hL : 0 ≤ L := mul_nonneg hK (Real.rpow_nonneg (hlog_pos ht ht') _)
  refine ⟨Real.exp (-L / 2), Real.exp_pos _, Real.exp_le_one_iff.mpr (by linarith), ?_⟩
  intro z u hz hz' hu hu'
  have hlz : Real.log z ≤ -L / 2 := by
    simpa only [Real.log_exp] using Real.log_le_log hz hz'
  by_cases htu : u < t
  · have hmem : u ∈ s ∩ Ioi (0 : ℝ) := by
      refine ⟨hball ?_, hu⟩
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hu] using
        htu.trans_le (min_le_left δ 1)
    have hp : deficitProfile K α u < ε := hsub hmem
    have hmul : 2 * u * Real.log z ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity)
      (hlz.trans (by linarith))
    linarith
  · have htu' : t ≤ u := le_of_not_gt htu
    have hlog : Real.log (Real.exp 1 / u) ≤ Real.log (Real.exp 1 / t) := by
      apply Real.log_le_log (by positivity)
      exact div_le_div_of_nonneg_left (Real.exp_pos 1).le ht htu'
    have hpow := Real.rpow_le_rpow (hlog_pos hu hu') hlog hα
    have hprof : deficitProfile K α u ≤ u * L := by
      unfold deficitProfile L
      calc
        K * (u * Real.log (Real.exp 1 / u) ^ α) =
            u * (K * Real.log (Real.exp 1 / u) ^ α) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hK) hu.le
    have hpen := mul_le_mul_of_nonneg_left hlz (show 0 ≤ 2 * u by positivity)
    linarith only [hprof, hpen, hε]

/-- Deterministic convergence transfer. The approximation family can be countable, and each
comparison is required only eventually in graph size, as after Borel–Cantelli. -/
theorem tendsto_of_monomer_approximation {p : ℕ → ℝ} {b : ℕ → ℕ → ℝ}
    {B err : ℕ → ℝ} {limit : ℝ}
    (hb : ∀ j, Tendsto (b j) atTop (𝓝 (B j))) (hB : Tendsto B atTop (𝓝 limit))
    (herr : Tendsto err atTop (𝓝 0))
    (hcmp : ∀ j, ∀ᶠ n in atTop, b j n - err j ≤ p n ∧ p n ≤ b j n) :
    Tendsto p atTop (𝓝 limit) := by
  have hl : Tendsto (fun j ↦ B j - err j) atTop (𝓝 limit) := by simpa using hB.sub herr
  refine tendsto_order.mpr ⟨fun a ha ↦ ?_, fun a ha ↦ ?_⟩
  · obtain ⟨j, hj⟩ := ((tendsto_order.mp hl).1 a ha).exists
    have ht : Tendsto (fun n ↦ b j n - err j) atTop (𝓝 (B j - err j)) :=
      (hb j).sub tendsto_const_nhds
    filter_upwards [(tendsto_order.mp ht).1 a hj, hcmp j] with n hn hc
    exact hn.trans_le hc.1
  · obtain ⟨j, hj⟩ := ((tendsto_order.mp hB).2 a ha).exists
    filter_upwards [(tendsto_order.mp (hb j)).2 a hj, hcmp j] with n hn hc
    exact hc.2.trans_lt hn


/-- Finite-size term in the pressure sandwich vanishes. -/
theorem tendsto_log_card_div_size :
    Tendsto (fun n : ℕ ↦ Real.log ((n : ℝ) + 1) / n) atTop (𝓝 0) := by
  have hx : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  simpa [Function.comp_def, ← sub_eq_add_neg] using
    (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp hx

/-- Given the completion coefficient bound, the manuscript's pressure sandwich is
uniform for all graph sizes with that bound. -/
theorem monomer_pressure_gap_of_completion {K α ε : ℝ}
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hε : 0 < ε) :
    ∃ z₀ : ℝ, 0 < z₀ ∧ z₀ ≤ 1 ∧ ∀ ⦃z : ℝ⦄, 0 < z → z ≤ z₀ →
    ∀ ⦃n : ℕ⦄, 0 < n → ∀ ⦃Z : ℕ → ℝ⦄, 0 < Z 0 → (∀ k, 0 ≤ Z k) →
    (∀ k : ℕ, 0 < k → k ≤ n →
      Z k ≤ Z 0 * Real.exp ((n : ℝ) * deficitProfile K α ((k : ℝ) / n))) →
    0 ≤ Real.log (monomerPartition n Z z) / n - Real.log (Z 0) / n ∧
    Real.log (monomerPartition n Z z) / n - Real.log (Z 0) / n ≤
      Real.log ((n : ℝ) + 1) / n + ε := by
  obtain ⟨z₀, hz₀, hz₁, hpen⟩ := small_fugacity_bound hK hα hε
  refine ⟨z₀, hz₀, hz₁, ?_⟩
  intro z hz hzz₀ n hn Z hZ₀ hZ hcomp
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  apply monomer_pressure_gap hn hZ₀ hZ hz
  intro k hkn
  by_cases hk : k = 0
  · subst k
    simp only [mul_zero, pow_zero, one_mul]
    exact le_mul_of_one_le_right hZ₀.le (Real.one_le_exp_iff.mpr (by positivity))
  · have hk' : 0 < (k : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hk)
    have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn
    have hp := hpen hz hzz₀ (div_pos hk' hn') ((div_le_one hn').mpr hkn')
    have hlog :=
      mul_le_mul_of_nonneg_left hp hn'.le
    have hfactor : z ^ (2 * k) = Real.exp ((2 * (k : ℝ)) * Real.log z) := by
      calc
        z ^ (2 * k) = Real.exp (Real.log z) ^ (2 * k) := by rw [Real.exp_log hz]
        _ = _ := by rw [← Real.exp_nat_mul, Nat.cast_mul, Nat.cast_ofNat]
    have hcancel : (n : ℝ) * (2 * ((k : ℝ) / n) * Real.log z) =
        (2 * (k : ℝ)) * Real.log z := by
      field_simp
    rw [mul_add, hcancel] at hlog
    calc
      z ^ (2 * k) * Z k ≤
          z ^ (2 * k) * (Z 0 * Real.exp ((n : ℝ) * deficitProfile K α ((k : ℝ) / n))) :=
        mul_le_mul_of_nonneg_left (hcomp k (Nat.pos_of_ne_zero hk) hkn) (by positivity)
      _ = Z 0 * Real.exp ((n : ℝ) * deficitProfile K α ((k : ℝ) / n) +
          (2 * (k : ℝ)) * Real.log z) := by rw [hfactor, Real.exp_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hlog) hZ₀.le

/-- The abstract almost-sure step in Proposition “Removing monomers”.
Combines the summable exceptional probabilities, countably many soft-pressure limits,
and the pressure gap with its vanishing finite-size term. -/
theorem ae_tendsto_of_monomer_approximation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {p : ℕ → Ω → ℝ} {b : ℕ → ℕ → Ω → ℝ}
    {B err : ℕ → ℝ} {limit : ℝ} {bad : ℕ → Set Ω}
    (hb : ∀ j, ∀ᵐ ω ∂μ, Tendsto (fun n ↦ b j n ω) atTop (𝓝 (B j)))
    (hB : Tendsto B atTop (𝓝 limit)) (herr : Tendsto err atTop (𝓝 0))
    (hbad : (∑' n, μ (bad n)) ≠ ∞)
    (hcmp : ∀ j n ω, 0 < n → ω ∉ bad n →
      b j n ω - (Real.log ((n : ℝ) + 1) / n + err j) ≤ p n ω ∧ p n ω ≤ b j n ω) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ p n ω) atTop (𝓝 limit) := by
  filter_upwards [ae_all_iff.mpr hb, ae_eventually_notMem hbad] with ω hω hgood
  have hl : Tendsto (fun j ↦ B j - err j) atTop (𝓝 limit) := by simpa using hB.sub herr
  refine tendsto_order.mpr ⟨fun a ha ↦ ?_, fun a ha ↦ ?_⟩
  · obtain ⟨j, hj⟩ := ((tendsto_order.mp hl).1 a ha).exists
    have ht : Tendsto (fun n ↦ b j n ω - (Real.log ((n : ℝ) + 1) / n + err j))
        atTop (𝓝 (B j - err j)) := by
      simpa using (hω j).sub (tendsto_log_card_div_size.add
        (tendsto_const_nhds (x := err j)))
    filter_upwards [(tendsto_order.mp ht).1 a hj, hgood, eventually_gt_atTop 0] with n hn hg hn'
    exact hn.trans_le (hcmp j n ω hn' hg).1
  · obtain ⟨j, hj⟩ := ((tendsto_order.mp hB).2 a ha).exists
    filter_upwards [(tendsto_order.mp (hω j)).2 a hj, hgood, eventually_gt_atTop 0] with n hn hg hn'
    exact (hcmp j n ω hn' hg).2.trans_lt hn

end Certificate

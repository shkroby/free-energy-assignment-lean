import Certificate.CompletionCyclic
import Certificate.TailMoment
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-!
# The negative part on exceptional arrays

A fixed number of independent cyclic assignments controls the second moment of
the negative pressure, even when the original cost has no finite mean.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace Certificate

/-- The negative part of the hard pressure. -/
noncomputable def negativePressure (β d κ : ℝ) (n : ℕ) (C : CostArray) : ℝ :=
  max (-pressure β d κ n C) 0

theorem measurable_negativePressure (β d κ : ℝ) (n : ℕ) :
    Measurable (negativePressure β d κ n) :=
  (measurable_pressure β d κ n).neg.max measurable_const

theorem ae_cost_nonneg (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Iio 0) = 0) :
    ∀ᵐ C ∂iidCosts μ, ∀ i, 0 ≤ C i := by
  apply ae_all_iff.mpr
  intro i
  have hi : (iidCosts μ).map (fun C : CostArray ↦ C i) = μ :=
    Measure.infinitePi_map_eval (fun _ : ℕ × ℕ ↦ μ) i
  rw [ae_iff]
  simp only [not_le]
  change iidCosts μ ((fun C : CostArray ↦ C i) ⁻¹' Iio 0) = 0
  rw [← Measure.map_apply (measurable_pi_apply i) measurableSet_Iio, hi, hμ]

/-- A polynomial L² bound with the exponent from the manuscript,
`1/d + 1/q`. The leading constant can depend on the selected number of
cyclic assignments. -/
theorem eLpNorm_negativePressure_le_of_moment
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {β d κ q : ℝ}
    (hβ : 0 < β) (_hd : 0 < d) (hκ : 0 < κ) (hq : 0 < q)
    (hμ : μ (Iio 0) = 0) (hMoment : Integrable (fun c : ℝ ↦ c ^ q) μ) :
    ∃ A : ℝ, 0 < A ∧ ∃ ℓ : ℕ, ∀ n : ℕ, ℓ ≤ n + 1 →
      eLpNorm (negativePressure β d κ (n + 1)) 2 (iidCosts μ) ≤
        ENNReal.ofReal (A * ((n : ℝ) + 1) ^ (1 / d + 1 / q)) := by
  let : IsProbabilityMeasure (iidCosts μ) := by
    unfold iidCosts
    infer_instance
  let M := ∫⁻ c, ENNReal.ofReal (c ^ q) ∂μ
  have hM : M < ∞ := ((hasFiniteIntegral_iff_norm _).mp hMoment.2).trans_le' <|
    lintegral_mono fun c ↦ ENNReal.ofReal_le_ofReal (by simpa only [Real.norm_eq_abs] using le_abs_self (c ^ q))
  let B := M.toReal + 1
  have hB : 0 < B := by positivity
  have hMB : M ≤ ENNReal.ofReal B := by
    rw [← ENNReal.ofReal_toReal hM.ne]
    apply ENNReal.ofReal_le_ofReal
    dsimp [B]
    linarith
  obtain ⟨ℓ, hℓ⟩ := exists_nat_gt (2 / q)
  have hℓq : 2 < q * (ℓ : ℝ) := by
    have ht := (div_lt_iff₀ hq).mp hℓ
    linarith only [ht]
  have ha : 0 < q * (ℓ : ℝ) / (q * (ℓ : ℝ) - 2) :=
    div_pos (by linarith) (by linarith)
  let K := (q * (ℓ : ℝ) / (q * (ℓ : ℝ) - 2)) ^ (1 / 2 : ℝ)
  have hK : 0 < K := Real.rpow_pos_of_pos ha _
  refine ⟨β * κ ^ (1 / d : ℝ) * B ^ (1 / q : ℝ) * K, by positivity, ℓ, ?_⟩
  intro n hn
  let N : ℝ := (n : ℝ) + 1
  have hN : 0 < N := by positivity
  let A := (N * B) ^ (1 / q : ℝ)
  have hA : 0 < A := Real.rpow_pos_of_pos (mul_pos hN hB) _
  have hAq : A ^ q = N * B := by
    dsimp [A]
    rw [← Real.rpow_mul (mul_nonneg hN.le hB.le), one_div_mul_cancel hq.ne', Real.rpow_one]
  let D := β * lengthScale d κ (n + 1) * A
  have hscale : 0 < lengthScale d κ (n + 1) := by
    unfold lengthScale
    positivity
  have hD : 0 < D := by positivity
  let f : CostArray → ℝ := fun C ↦ negativePressure β d κ (n + 1) C / D
  have hf : Measurable f := (measurable_negativePressure β d κ _).div_const D
  have hf₀ : 0 ≤ᵐ[iidCosts μ] f := .of_forall fun C ↦
    div_nonneg (le_max_right _ _) hD.le
  have htail (t : ℝ) (ht : 1 < t) :
      iidCosts μ {C | t < f C} ≤ ENNReal.ofReal (t ^ (-(q * (ℓ : ℝ)))) := by
    let S : Finset (Fin (n + 1)) := Finset.univ.map (Fin.castLEEmb hn)
    have hS : S.card = ℓ := by simp [S]
    let u := t * (N * A)
    have ht₀ : 0 < t := zero_lt_one.trans ht
    have hu : 0 < u := by positivity
    have hsub : {C | t < f C} ≤ᵐ[iidCosts μ]
        (⋂ s ∈ S, Completion.cyclicCost n s ⁻¹' Ioi u) := by
      filter_upwards [ae_cost_nonneg μ hμ] with C hC htC
      have hlt : t * D < negativePressure β d κ (n + 1) C := (lt_div_iff₀ hD).mp htC
      apply mem_iInter₂.mpr
      intro s hs
      have hnC : 0 ≤ Completion.cyclicCost n s C :=
        Finset.sum_nonneg fun i _ ↦ hC _
      have hneg := Completion.pressure_negPart_le_cyclicCost β d κ n s C
        (mul_nonneg (mul_nonneg hβ.le hscale.le) hnC)
      have hnEq : ((n + 1 : ℕ) : ℝ) = N := by simp [N]
      rw [hnEq] at hneg
      have hlt' := (lt_div_iff₀ hN).mp (hlt.trans_le hneg)
      change u < Completion.cyclicCost n s C
      apply (mul_lt_mul_iff_right₀ (mul_pos hβ hscale)).mp
      convert hlt' using 1
      unfold u D
      ring
    calc
      _ ≤ iidCosts μ (⋂ s ∈ S, Completion.cyclicCost n s ⁻¹' Ioi u) :=
        measure_mono_ae hsub
      _ ≤ (((n : ℝ≥0∞) + 1) * (M / ENNReal.ofReal ((u / N) ^ q))) ^ S.card :=
        Completion.cyclicCost_min_tail_le_rpow μ n S hu hq
      _ ≤ (ENNReal.ofReal N * (ENNReal.ofReal B / ENNReal.ofReal ((u / N) ^ q))) ^ ℓ := by
        have hNE : (n : ℝ≥0∞) + 1 = ENNReal.ofReal N := by
          dsimp [N]
          rw [ENNReal.ofReal_add (by positivity) zero_le_one]
          simp
        rw [hNE, hS]
        gcongr
      _ = _ := by
        have hu' : u / N = t * A := by
          unfold u
          field_simp
        have hx : (u / N) ^ q = t ^ q * (N * B) := by
          rw [hu', Real.mul_rpow ht₀.le hA.le, hAq]
        have htq : 0 < t ^ q := Real.rpow_pos_of_pos ht₀ _
        rw [hx, ← ENNReal.ofReal_div_of_pos (by positivity),
          ← ENNReal.ofReal_mul hN.le, ← ENNReal.ofReal_pow (by positivity)]
        have hfrac : N * (B / (t ^ q * (N * B))) = t ^ (-q) := by
          rw [Real.rpow_neg ht₀.le]
          field_simp
        rw [hfrac, ← Real.rpow_natCast, ← Real.rpow_mul ht₀.le, neg_mul]
  have hbnd := eLpNorm_two_le_of_power_tail (iidCosts μ) hf hf₀ hℓq htail
  have hscale_f : negativePressure β d κ (n + 1) = D • f := by
    funext C
    dsimp [f, Pi.smul_apply, smul_eq_mul]
    field_simp
  have hDform : D * K = β * κ ^ (1 / d : ℝ) * B ^ (1 / q : ℝ) * K * N ^ (1 / d + 1 / q) := by
    have hnEq : ((n + 1 : ℕ) : ℝ) = N := by simp [N]
    change (β * lengthScale d κ (n + 1) * ((N * B) ^ (1 / q : ℝ))) * K = _
    rw [lengthScale, hnEq, Real.mul_rpow hκ.le hN.le, Real.mul_rpow hN.le hB.le,
      Real.rpow_add hN]
    ring
  rw [hscale_f, eLpNorm_const_smul, Real.enorm_of_nonneg hD.le, ← hDform, ENNReal.ofReal_mul hD.le]
  gcongr

end Certificate

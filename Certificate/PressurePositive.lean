import Certificate.PressureNegative
import Certificate.CostWeightTail
import Mathlib.Probability.Moments.Variance

/-! The positive part of the hard pressure has a uniform second moment. -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal ProbabilityTheory

namespace Certificate

/-- The positive part of the hard pressure. -/
noncomputable def positivePressure (β d κ : ℝ) (n : ℕ) (C : CostArray) : ℝ :=
  max (pressure β d κ n C) 0

theorem measurable_positivePressure (β d κ : ℝ) (n : ℕ) :
    Measurable (positivePressure β d κ n) :=
  (measurable_pressure β d κ n).max measurable_const

/-- Dropping column injectivity bounds the permanent by the product of row sums. -/
theorem permanent_le_prod_row_sum {n : ℕ} (w : Fin n → Fin n → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) :
    permanent w ≤ ∏ i, ∑ j, w i j := by
  classical
  let e : Equiv.Perm (Fin n) ↪ (Fin n → Fin n) :=
    ⟨fun σ ↦ σ, fun _ _ h ↦ Equiv.ext (congrFun h)⟩
  unfold permanent
  rw [Fintype.prod_sum]
  calc
    _ = ∑ f ∈ Finset.univ.map e, ∏ i, w i (f i) := by rw [Finset.sum_map]; rfl
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun f _ _ ↦ Finset.prod_nonneg fun i _ ↦ hw i (f i))

private theorem positivePressure_le_weight_sum {β d κ : ℝ} {n : ℕ} (hn : 0 < n)
    (C : CostArray) :
    positivePressure β d κ n C ≤
      (∑ p : Fin n × Fin n, Real.exp (-(β * lengthScale d κ n * C (p.1.val, p.2.val)))) / n := by
  let w : Fin n → Fin n → ℝ := fun i j ↦ Real.exp (-(β * lengthScale d κ n * C (i.val, j.val)))
  let S : Fin n → ℝ := fun i ↦ ∑ j, w i j
  have hS (i : Fin n) : 0 < S i := Finset.sum_pos (fun _ _ ↦ Real.exp_pos _)
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hupper := Real.log_le_log (assignmentPartition_pos β d κ n C)
    (permanent_le_prod_row_sum w (fun _ _ ↦ Real.exp_nonneg _))
  change Real.log (assignmentPartition β d κ n C) ≤ Real.log (∏ i, S i) at hupper
  have hlog : Real.log (∏ i, S i) = ∑ i, Real.log (S i) :=
    Real.log_prod (fun i _ ↦ (hS i).ne')
  rw [hlog] at hupper
  have hsum : Real.log (assignmentPartition β d κ n C) ≤ ∑ i, S i :=
    hupper.trans (Finset.sum_le_sum fun i _ ↦ (Real.log_le_sub_one_of_pos (hS i)).trans (by linarith))
  have h := div_le_div_of_nonneg_right hsum (Nat.cast_nonneg n)
  unfold positivePressure pressure
  rw [Fintype.sum_prod_type]
  exact max_le h (by positivity)

/-- The uniform one-edge first-moment bound from the small-cost CDF. -/
theorem integral_edgeWeight_le_div_size {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {β d κ : ℝ} (hβ : 0 < β) (hd : 0 < d) (hκ : 0 < κ) (hμ : SmallCostTail μ κ d) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ n : ℕ, 0 < n →
      (∫ c, Real.exp (-β * (lengthScale d κ n * c)) ∂μ) ≤ A / n := by
  obtain ⟨K, hK, htail⟩ := scaled_costWeight_tail_le hκ hd hβ hμ
  let g : ℝ → ℝ := fun t ↦ β * t ^ d * Real.exp (-β * t)
  have hg : IntegrableOn g (Ioi 0) := by
    have hbase : IntegrableOn (fun t : ℝ ↦ t ^ d * Real.exp (-β * t)) (Ioi 0) := by
      by_contra h
      have hh := integral_undef h
      have hp := integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := d) zero_lt_one
        (show -1 < d by linarith) hβ
      simp only [Real.rpow_one] at hp
      rw [hp] at hh
      have hGamma := Real.Gamma_pos_of_pos (show 0 < (d + 1) / 1 by positivity)
      have hpositive : 0 < β ^ (-(d + 1) / 1) * (1 / 1) *
          Real.Gamma ((d + 1) / 1) := by positivity
      exact hpositive.ne' hh
    change Integrable g (volume.restrict (Ioi (0 : ℝ)))
    refine (hbase.const_mul β).congr (.of_forall fun t ↦ ?_)
    dsimp [g]
    ring
  have hg0 : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] g := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
    exact mul_nonneg (mul_nonneg hβ.le (Real.rpow_nonneg hx.le _)) (Real.exp_nonneg _)
  let G := ∫ t in Ioi (0 : ℝ), g t
  have hG : 0 ≤ G := integral_nonneg_of_ae hg0
  refine ⟨K * G, mul_nonneg hK.le hG, ?_⟩
  intro n hn
  have hC : ∀ᵐ c ∂μ, 0 ≤ c := by
    rw [ae_iff]
    simp only [not_le]
    exact hμ.1
  have hscale : 0 ≤ lengthScale d κ n := by unfold lengthScale; positivity
  let w : ℝ → ℝ := fun c ↦ Real.exp (-β * (lengthScale d κ n * c))
  have hwa : ∀ᵐ c ∂μ, w c ∈ Icc 0 1 := by
    filter_upwards [hC] with c hc
    exact ⟨Real.exp_nonneg _, Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hscale hc])⟩
  have hwM : Measurable w := by unfold w; fun_prop
  have hwI := memLp_one_iff_integrable.mp (memLp_of_bounded hwa hwM.aestronglyMeasurable 1)
  have hwt : ∀ᵐ c ∂μ, c ∈ {c | 0 ≤ lengthScale d κ n * c} :=
    hC.mono fun _ hc ↦ mul_nonneg hscale hc
  have hB := htail n hn 0 le_rfl
  rw [Measure.restrict_eq_self_of_ae_mem hwt] at hB
  change (∫⁻ c, ENNReal.ofReal (w c) ∂μ) ≤
    ENNReal.ofReal (K / n) * ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (g t) at hB
  rw [← ofReal_integral_eq_lintegral_ofReal hwI (.of_forall fun _ ↦ Real.exp_nonneg _),
    ← ofReal_integral_eq_lintegral_ofReal hg hg0, ← ENNReal.ofReal_mul (by positivity)] at hB
  have hout : 0 ≤ K / (n : ℝ) * G := by positivity
  have hI := (ENNReal.ofReal_le_ofReal_iff hout).mp hB
  convert hI using 1
  ring

/-- Probability variance bounds for iid entries give a uniformly bounded L²
norm of the positive part. -/
theorem eLpNorm_positivePressure_bdd {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {β d κ : ℝ} (hβ : 0 < β) (hd : 0 < d) (hκ : 0 < κ) (hμ : SmallCostTail μ κ d) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, 0 < n →
      eLpNorm (positivePressure β d κ n) 2 (iidCosts μ) ≤ ENNReal.ofReal B := by
  let : IsProbabilityMeasure (iidCosts μ) := by unfold iidCosts; infer_instance
  obtain ⟨A, hA, hmean⟩ := integral_edgeWeight_le_div_size hβ hd hκ hμ
  refine ⟨(A + A ^ 2) ^ (1 / 2 : ℝ), Real.rpow_nonneg (by positivity) _, ?_⟩
  intro n hn
  let D := Fin n × Fin n
  let idx : D → ℕ × ℕ := fun p ↦ (p.1.val, p.2.val)
  let w : ℝ → ℝ := fun c ↦ Real.exp (-(β * lengthScale d κ n * c))
  let W : D → CostArray → ℝ := fun p C ↦ w (C (idx p))
  let S : CostArray → ℝ := fun C ↦ ∑ p, W p C
  let Y : CostArray → ℝ := fun C ↦ S C / n
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hscale : 0 ≤ lengthScale d κ n := by unfold lengthScale; positivity
  have hmw : Measurable w := by unfold w; fun_prop
  have hmW (p : D) : Measurable (W p) := hmw.comp (measurable_pi_apply (idx p))
  have hW01 (p : D) : ∀ᵐ C ∂iidCosts μ, W p C ∈ Icc 0 1 := by
    filter_upwards [ae_cost_nonneg μ hμ.1] with C hC
    change 0 ≤ w (C (idx p)) ∧ w (C (idx p)) ≤ 1
    exact ⟨Real.exp_nonneg _, Real.exp_le_one_iff.mpr
      (neg_nonpos.mpr (mul_nonneg (mul_nonneg hβ.le hscale) (hC _)))⟩
  have hLp (p : D) : MemLp (W p) 2 (iidCosts μ) :=
    memLp_of_bounded (hW01 p) (hmW p).aestronglyMeasurable 2
  have hS : S = ∑ p : D, W p := by funext C; simp [S, Finset.sum_apply]
  have hLpS : MemLp S 2 (iidCosts μ) := hS.symm ▸ (memLp_finsetSum' _ fun p _ ↦ hLp p)
  have hYEq : Y = (n : ℝ)⁻¹ • S := by funext C; simp [Y, div_eq_mul_inv, mul_comm]
  have hLpY : MemLp Y 2 (iidCosts μ) := hYEq ▸ hLpS.const_smul (n : ℝ)⁻¹
  have hi : Function.Injective idx := fun p q hp ↦
    Prod.ext (Fin.ext (congrArg Prod.fst hp)) (Fin.ext (congrArg Prod.snd hp))
  have hInd : iIndepFun W (iidCosts μ) := by
    exact (iIndepFun_infinitePi (X := fun _ ↦ w) (fun _ ↦ hmw)).precomp hi
  have hmeanW (p : D) : (∫ C, W p C ∂iidCosts μ) ≤ A / n := by
    have hmap := Measure.infinitePi_map_eval (fun _ : ℕ × ℕ ↦ μ) (idx p)
    have hm := integral_map (μ := iidCosts μ) (measurable_pi_apply (idx p)).aemeasurable
      hmw.aestronglyMeasurable
    rw [show (iidCosts μ).map (fun C => C (idx p)) = μ from hmap] at hm
    change (∫ C : CostArray, w (C (idx p)) ∂iidCosts μ) ≤ A / n
    rw [← hm]
    simpa only [w, neg_mul, mul_assoc] using hmean n hn
  have hvarW (p : D) : variance (W p) (iidCosts μ) ≤ A / n := by
    rw [variance_eq_sub (hLp p)]
    have ht : (∫ C, (W p C) ^ 2 ∂iidCosts μ) ≤ ∫ C, W p C ∂iidCosts μ := by
      apply integral_mono_ae (hLp p).integrable_sq ((hLp p).integrable (by norm_num))
      filter_upwards [hW01 p] with C hc
      rw [pow_two]
      exact mul_le_of_le_one_right hc.1 hc.2
    change (∫ C, (W p C) ^ 2 ∂iidCosts μ) - (∫ C, W p C ∂iidCosts μ) ^ 2 ≤ A / n
    linarith [hmeanW p, sq_nonneg (∫ C, W p C ∂iidCosts μ)]
  have hsumBound (f : D → ℝ) (hf : ∀ p, f p ≤ A / n) : ∑ p, f p ≤ n * A := by
    calc
      _ ≤ ∑ _p : D, A / n := Finset.sum_le_sum fun p _ ↦ hf p
      _ = _ := by simp [D, Fintype.card_prod, nsmul_eq_mul]; field_simp
  have hvarS : variance S (iidCosts μ) ≤ n * A := by
    rw [hS, IndepFun.variance_sum (fun p _ ↦ hLp p) (fun p _ q _ hpq ↦ hInd.indepFun hpq)]
    exact hsumBound _ hvarW
  have hmeanS : (∫ C, S C ∂iidCosts μ) ≤ n * A := by
    unfold S
    rw [integral_finsetSum _ (fun p _ ↦ (hLp p).integrable (by norm_num))]
    exact hsumBound _ hmeanW
  have hmeanY : (∫ C, Y C ∂iidCosts μ) ≤ A := by
    change (∫ C, S C / (n : ℝ) ∂iidCosts μ) ≤ A
    rw [integral_div]
    exact (div_le_iff₀ hn0).mpr (by linarith only [hmeanS, mul_comm A (n : ℝ)])
  have hY0 : ∀ C, 0 ≤ Y C := fun C ↦
    div_nonneg (Finset.sum_nonneg fun _ _ ↦ Real.exp_nonneg _) hn0.le
  have hvarY : variance Y (iidCosts μ) ≤ A := by
    rw [hYEq, variance_smul]
    calc
      _ ≤ ((n : ℝ)⁻¹) ^ 2 * ((n : ℝ) * A) :=
        mul_le_mul_of_nonneg_left hvarS (sq_nonneg _)
      _ = A / n := by field_simp
      _ ≤ A := div_le_self hA hn'
  have hYsq : (∫ C, Y C ^ 2 ∂iidCosts μ) ≤ A + A ^ 2 := by
    rw [variance_eq_sub hLpY] at hvarY
    have hm0 : 0 ≤ ∫ C, Y C ∂iidCosts μ := integral_nonneg_of_ae (.of_forall hY0)
    have hp := pow_le_pow_left₀ hm0 hmeanY 2
    change (∫ C, Y C ^ 2 ∂iidCosts μ) - (∫ C, Y C ∂iidCosts μ) ^ 2 ≤ A at hvarY
    linarith
  have hnY : eLpNorm Y 2 (iidCosts μ) ≤ ENNReal.ofReal ((A + A ^ 2) ^ (1 / 2 : ℝ)) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := (2 : ℝ≥0∞)) (by norm_num) (by simp)]
    norm_num only [ENNReal.toReal_ofNat]
    rw [← ENNReal.ofReal_rpow_of_nonneg (by positivity : 0 ≤ A + A ^ 2) (by norm_num)]
    apply ENNReal.rpow_le_rpow _ (by norm_num)
    have hlin : (∫⁻ C, ‖Y C‖ₑ ^ (2 : ℝ) ∂iidCosts μ) =
        ENNReal.ofReal (∫ C, Y C ^ 2 ∂iidCosts μ) := by
      rw [ofReal_integral_eq_lintegral_ofReal hLpY.integrable_sq (.of_forall fun _ ↦ sq_nonneg _)]
      congr with C
      rw [ENNReal.rpow_two, Real.enorm_of_nonneg (hY0 C), ENNReal.ofReal_pow (hY0 C)]
    rw [hlin]
    exact ENNReal.ofReal_le_ofReal hYsq
  apply (eLpNorm_mono (g := Y) ?_).trans hnY
  intro C
  rw [Real.norm_of_nonneg (show 0 ≤ positivePressure β d κ n C from le_max_right _ _),
    Real.norm_of_nonneg (hY0 C)]
  exact positivePressure_le_weight_sum hn C

end Certificate

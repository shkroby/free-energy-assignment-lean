import Certificate.CompletionModel
import Certificate.PressurePositive
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Concentration of the total of the row weights

An exponential Markov estimate controls the sum of the edge weights on the
same cost array as the common expansion event.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal MeasureTheory

namespace Certificate.Completion

private theorem exp_le_chord {x : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) :
    Real.exp x ≤ 1 + (Real.exp 1 - 1) * x := by
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ))
    (sub_nonneg.mpr hx₁) hx₀ (sub_add_cancel 1 x)
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add, Real.exp_zero] at h
  linarith

/-- The complete sum of row weights. -/
noncomputable def totalRowWeight (β d κ : ℝ) (n : ℕ) (C : CostArray) : ℝ :=
  ∑ i, rowSum β (scaledCost d κ n C) i

theorem measurable_totalRowWeight (β d κ : ℝ) (n : ℕ) :
    Measurable (totalRowWeight β d κ n) := by
  unfold totalRowWeight rowSum scaledCost
  fun_prop

/-- The manuscript's extra weight event has exponentially small failure probability. -/
theorem measure_totalRowWeight_gt_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {β d κ : ℝ} (hβ : 0 < β) (hd : 0 < d) (hκ : 0 < κ) (hμ : SmallCostTail μ κ d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, 0 < n →
      iidCosts μ {C | K * n < totalRowWeight β d κ n C} ≤
        ENNReal.ofReal (Real.exp (-(n : ℝ))) := by
  obtain ⟨A, hA, hmean⟩ := integral_edgeWeight_le_div_size hβ hd hκ hμ
  let b := Real.exp 1 - 1
  have hb : 0 ≤ b := sub_nonneg.mpr (Real.one_le_exp zero_le_one)
  let K := b * A + 1
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro n hn
  let : IsProbabilityMeasure (iidCosts μ) := by unfold iidCosts; infer_instance
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  let D := Fin n × Fin n
  let idx : D → ℕ × ℕ := fun p => (p.1.val, p.2.val)
  let w : ℝ → ℝ := fun c => Real.exp (-β * (lengthScale d κ n * c))
  let W (p : D) (C : CostArray) := w (C (idx p))
  let S (C : CostArray) : ℝ := ∑ p : D, W p C
  have hWS : totalRowWeight β d κ n = S := by
    funext C
    change (∑ i : Fin n, ∑ j : Fin n, W (i, j) C) = ∑ p : Fin n × Fin n, W p C
    exact (Fintype.sum_prod_type (fun p : Fin n × Fin n => W p C)).symm
  have hidx : Function.Injective idx := fun _ _ h =>
    Prod.ext (Fin.ext (congrArg Prod.fst h)) (Fin.ext (congrArg Prod.snd h))
  have hwM : Measurable w := by unfold w; fun_prop
  have hWM (p : D) : Measurable (W p) := hwM.comp (measurable_pi_apply (idx p))
  have hSM : Measurable S := Finset.measurable_fun_sum _ fun p _ => hWM p
  have hscale : 0 ≤ lengthScale d κ n := by unfold lengthScale; positivity
  have hW01 : ∀ᵐ C ∂iidCosts μ, ∀ p : D, W p C ∈ Icc 0 1 := by
    filter_upwards [ae_cost_nonneg μ hμ.1] with C hC
    intro p
    change 0 ≤ w (C (idx p)) ∧ w (C (idx p)) ≤ 1
    exact ⟨Real.exp_nonneg _, Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hβ.le) (mul_nonneg hscale (hC _)))⟩
  have hWI (p : D) : Integrable (W p) (iidCosts μ) := by
    apply Integrable.of_bound (hWM p).aestronglyMeasurable 1
    filter_upwards [hW01] with C hC
    rw [Real.norm_eq_abs, abs_of_nonneg (hC p).1]
    exact (hC p).2
  have hEI (p : D) : Integrable (fun C => Real.exp (W p C)) (iidCosts μ) := by
    apply Integrable.of_bound (Real.continuous_exp.measurable.comp (hWM p)).aestronglyMeasurable
      (Real.exp 1)
    filter_upwards [hW01] with C hC
    rw [Real.norm_eq_abs, Function.comp_apply, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (hC p).2
  have hmeanW (p : D) : (∫ C, W p C ∂iidCosts μ) ≤ A / n := by
    have hmap := Measure.infinitePi_map_eval (fun _ : ℕ × ℕ => μ) (idx p)
    have hi := integral_map (μ := iidCosts μ) (measurable_pi_apply (idx p)).aemeasurable
      hwM.aestronglyMeasurable
    rw [show (iidCosts μ).map (fun C => C (idx p)) = μ from hmap] at hi
    change (∫ C : CostArray, w (C (idx p)) ∂iidCosts μ) ≤ A / n
    rw [← hi]
    exact hmean n hn
  have hsingle (p : D) :
      (∫ C, Real.exp (W p C) ∂iidCosts μ) ≤ 1 + b * (A / n) := by
    calc
      _ ≤ ∫ C, 1 + b * W p C ∂iidCosts μ := by
        apply integral_mono_ae (hEI p) ((integrable_const 1).add ((hWI p).const_mul b))
        filter_upwards [hW01] with C hC
        exact exp_le_chord (hC p).1 (hC p).2
      _ = 1 + b * (∫ C, W p C ∂iidCosts μ) := by
        rw [integral_add (integrable_const 1) ((hWI p).const_mul b), integral_const_mul]
        simp
      _ ≤ _ := by linarith [mul_le_mul_of_nonneg_left (hmeanW p) hb]
  have hEind : iIndepFun (fun p C => Real.exp (W p C)) (iidCosts μ) :=
    (iIndepFun_infinitePi (X := fun (_ : ℕ × ℕ) => fun c => Real.exp (w c))
      (fun _ => Real.continuous_exp.measurable.comp hwM)).precomp hidx
  have hMGF : (∫ C, Real.exp (S C) ∂iidCosts μ) ≤ Real.exp (b * A * n) := by
    change (∫ C, Real.exp (∑ p : D, W p C) ∂iidCosts μ) ≤ _
    simp_rw [Real.exp_sum]
    rw [hEind.integral_fun_prod_eq_prod_integral
      (fun p => (Real.continuous_exp.measurable.comp (hWM p)).aestronglyMeasurable)]
    calc
      _ ≤ ∏ _ : D, (1 + b * (A / n)) :=
        Finset.prod_le_prod (fun p _ => integral_nonneg fun _ => Real.exp_nonneg _)
          (fun p _ => hsingle p)
      _ ≤ Real.exp (∑ _ : D, b * (A / n)) :=
        Real.prod_one_add_le_exp_sum _ (fun _ => by positivity)
      _ = _ := by
        congr 1
        simp [D, Fintype.card_prod, Nat.cast_mul, nsmul_eq_mul]
        field_simp
  have hESI : Integrable (fun C => Real.exp (S C)) (iidCosts μ) := by
    apply Integrable.of_bound (Real.continuous_exp.measurable.comp hSM).aestronglyMeasurable
      (Real.exp (Fintype.card D))
    filter_upwards [hW01] with C hC
    rw [Real.norm_eq_abs, Function.comp_apply, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    change (∑ p : D, W p C) ≤ (Fintype.card D : ℝ)
    simpa [nsmul_eq_mul] using
      (Finset.sum_le_sum (s := (Finset.univ : Finset D)) (fun p _ => (hC p).2))
  rw [hWS]
  have hm : Measurable (fun C => ENNReal.ofReal (Real.exp (S C))) :=
    ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp hSM)
  have hk : 0 < Real.exp (K * (n : ℝ)) := Real.exp_pos _
  calc
    _ ≤ iidCosts μ {C | ENNReal.ofReal (Real.exp (K * (n : ℝ))) ≤
        ENNReal.ofReal (Real.exp (S C))} :=
      measure_mono fun C hC => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hC.le)
    _ ≤ (∫⁻ C, ENNReal.ofReal (Real.exp (S C)) ∂iidCosts μ) /
        ENNReal.ofReal (Real.exp (K * (n : ℝ))) :=
      meas_ge_le_lintegral_div hm.aemeasurable (ENNReal.ofReal_ne_zero_iff.mpr hk)
        ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (Real.exp (b * A * n)) / ENNReal.ofReal (Real.exp (K * (n : ℝ))) := by
      rw [← ofReal_integral_eq_lintegral_ofReal hESI (.of_forall fun _ => Real.exp_nonneg _)]
      exact ENNReal.div_le_div_right (ENNReal.ofReal_le_ofReal hMGF) _
    _ = _ := by
      rw [← ENNReal.ofReal_div_of_pos hk, ← Real.exp_sub]
      congr 2
      dsimp [K]
      ring

end Certificate.Completion

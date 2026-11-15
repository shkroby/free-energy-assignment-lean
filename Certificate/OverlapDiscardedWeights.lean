import Certificate.OverlapTrim
import Certificate.AssignmentCutoffPressure
import Certificate.SubgaussianLimit
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Probability.Independence.InfinitePi

/-! Exponential upper bounds for the mass discarded by length and degree cutoffs. -/

open Finset Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

namespace Certificate.Overlap

/-- An exponential moment estimate at parameter one suffices for an eventual
almost-sure upper bound, with any strictly positive slack. -/
theorem ae_eventually_lt_linear_of_mgf {A : Type*} [MeasurableSpace A]
    (P : Measure A) [IsProbabilityMeasure P] {F : ℕ → A → ℝ} {c δ : ℝ}
    (hδ : 0 < δ)
    (hm : ∀ n, Integrable (fun a => Real.exp (F n a)) P)
    (hb : ∀ᶠ n in atTop, mgf (F n) P 1 ≤ Real.exp (c * (n : ℝ))) :
    ∀ᵐ a ∂P, ∀ᶠ n in atTop, F n a < (c + δ) * (n : ℝ) := by
  let E (n : ℕ) := {a | (c + δ) * (n : ℝ) ≤ F n a}
  have htail : ∀ᶠ n in atTop, P (E n) ≤ ENNReal.ofReal (Real.exp (-(δ * (n : ℝ)))) := by
    filter_upwards [hb] with n hbn
    have h := measure_ge_le_exp_mul_mgf (μ := P) (X := F n) (t := 1)
      ((c + δ) * (n : ℝ)) zero_le_one (by simpa using hm n)
    rw [← ENNReal.ofReal_toReal (measure_ne_top P (E n))]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ Real.exp (-(1:ℝ) * ((c + δ) * (n : ℝ))) * mgf (F n) P 1 := h
      _ ≤ Real.exp (-(1:ℝ) * ((c + δ) * (n : ℝ))) * Real.exp (c * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hbn (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  obtain ⟨N,hN⟩ := eventually_atTop.mp htail
  let b (n : ℕ) : ℝ≥0∞ := if n < N then 1 else 0
  have hbfinite : (∑' n, b n) < ∞ := by
    rw [tsum_eq_sum (s := range N)]
    · simp [b]
    · intro n hn
      simpa [b, Finset.mem_range] using hn
  have hsum : Summable (fun n : ℕ => Real.exp (-(δ * (n : ℝ)))) := by
    simpa only [Real.rpow_one] using summable_nat_stretchedExp hδ zero_lt_one
  have hsfinite : (∑' n : ℕ, ENNReal.ofReal (Real.exp (-(δ * (n : ℝ))))) < ∞ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => Real.exp_nonneg _) hsum]
    exact ENNReal.ofReal_lt_top
  have hE : (∑' n, P (E n)) < ∞ := by
    calc
      _ ≤ ∑' n, (b n + ENNReal.ofReal (Real.exp (-(δ * (n : ℝ))))) := by
        apply ENNReal.tsum_le_tsum
        intro n
        by_cases hn : n < N
        · exact prob_le_one.trans (by simp [b, hn])
        · simpa only [b, if_neg hn, zero_add] using hN n (Nat.le_of_not_gt hn)
      _ < ∞ := by rw [ENNReal.tsum_add]; exact ENNReal.add_lt_top.mpr ⟨hbfinite,hsfinite⟩
  simpa only [E, mem_ofPred_eq, not_le] using ae_eventually_notMem hE.ne

private theorem mgf_sum_iid_entries {I : Type*} [Fintype I] (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (index : I ↪ ℕ × ℕ) {f : ℝ → ℝ}
    (hf : Measurable f) (t : ℝ) :
    mgf (fun C : CostArray => ∑ i, f (C (index i))) (iidCosts μ) t =
      mgf f μ t ^ Fintype.card I := by
  let X (i : I) (C : CostArray) := f (C (index i))
  have hi := iIndepFun_infinitePi (P := fun _ : ℕ × ℕ => μ)
    (X := fun _ => (id : ℝ → ℝ)) (fun _ => measurable_id)
  have hX : iIndepFun X (iidCosts μ) := (hi.precomp index.injective).comp
    (fun _ => f) (fun _ => hf)
  have heq : (fun C : CostArray => ∑ i, f (C (index i))) = ∑ i, X i :=
    funext fun C => by simp [X]
  have hmgf (i : I) : mgf (X i) (iidCosts μ) t = mgf f μ t := by
    let Y (C : CostArray) := C (index i)
    have hY : Measurable Y := measurable_pi_apply _
    have h := mgf_map (Y := Y) (X := f) (μ := iidCosts μ) hY.aemeasurable (t := t)
      (hf.const_mul t).exp.aestronglyMeasurable
    rw [show (iidCosts μ).map Y = μ from
      Measure.infinitePi_map_eval (fun _ : ℕ × ℕ => μ) (index i)] at h
    exact h.symm
  rw [heq, hX.mgf_sum (fun i => hf.comp (measurable_pi_apply (index i))) univ]
  simp only [hmgf, prod_const, card_univ]

private theorem exp_le_linear_on_unit {x : ℝ} (h₀ : 0 ≤ x) (h₁ : x ≤ 1) :
    Real.exp x ≤ 1 + (Real.exp 1 - 1) * x := by
  have h := convexOn_exp.2 (mem_univ (0:ℝ)) (mem_univ (1:ℝ))
    (sub_nonneg.mpr h₁) h₀ (sub_add_cancel (1:ℝ) x)
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add, Real.exp_zero] at h
  linarith

private theorem mgf_one_le_exp_mean {A : Type*} [MeasurableSpace A] (P : Measure A)
    [IsProbabilityMeasure P] {f : A → ℝ} (hf : Measurable f)
    (hb : ∀ a, f a ∈ Icc (0:ℝ) 1) :
    mgf f P 1 ≤ Real.exp ((Real.exp 1 - 1) * ∫ a, f a ∂P) := by
  have hfi := Integrable.of_bound (μ := P) hf.aestronglyMeasurable 1
    (Eventually.of_forall fun a => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hb a).1]
      exact (hb a).2)
  have he := Integrable.of_bound (μ := P) hf.exp.aestronglyMeasurable (Real.exp 1)
    (Eventually.of_forall fun a => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (hb a).2)
  have hc : Integrable (fun a => 1 + (Real.exp 1 - 1) * f a) P :=
    (integrable_const _).add (hfi.const_mul _)
  unfold mgf
  simp only [one_mul]
  calc
    _ ≤ ∫ a, 1 + (Real.exp 1 - 1) * f a ∂P := integral_mono he hc
      (fun a => exp_le_linear_on_unit (hb a).1 (hb a).2)
    _ = _ := by rw [integral_add (integrable_const _) (hfi.const_mul _),
      integral_const, probReal_univ, one_smul, integral_const_mul]
    _ ≤ _ := by linarith [Real.add_one_le_exp ((Real.exp 1 - 1) * ∫ a, f a ∂P)]

private noncomputable def longWeight (β d κ R : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  if R < lengthScale d κ n * x then Real.exp (-β * (lengthScale d κ n * x)) else 0

private theorem measurable_longWeight (β d κ R : ℝ) (n : ℕ) :
    Measurable (longWeight β d κ R n) := by
  unfold longWeight
  apply Measurable.ite (measurableSet_lt measurable_const (by fun_prop)) _ measurable_const
  fun_prop

private theorem longWeight_mem {β R : ℝ} (hβ : 0 < β) (hR : 0 ≤ R) (d κ : ℝ)
    (n : ℕ) (x : ℝ) : longWeight β d κ R n x ∈ Icc (0:ℝ) 1 := by
  unfold longWeight
  split_ifs with h
  · exact ⟨Real.exp_nonneg _, Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hβ.le) (hR.trans h.le))⟩
  · exact ⟨le_rfl, zero_le_one⟩

/-- Weight discarded by the length cutoff before any degree trimming. -/
noncomputable def longAssignmentMass (β d κ R : ℝ) (n : ℕ) (C : CostArray) : ℝ :=
  ∑ e : Fin n × Fin n, longWeight β d κ R n (C (e.1.val,e.2.val))

private theorem integrable_exp_longAssignmentMass {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {β R : ℝ} (hβ : 0 < β) (hR : 0 ≤ R) (d κ : ℝ) (n : ℕ) :
    Integrable (fun C => Real.exp (longAssignmentMass β d κ R n C)) (iidCosts μ) := by
  let : IsProbabilityMeasure (iidCosts μ) := by unfold iidCosts; infer_instance
  have hm : Measurable (longAssignmentMass β d κ R n) := by
    unfold longAssignmentMass
    exact Finset.measurable_fun_sum _ fun e _ => (measurable_longWeight ..).comp (measurable_pi_apply _)
  apply Integrable.of_bound hm.exp.aestronglyMeasurable (Real.exp (n^2))
  refine Eventually.of_forall fun C => ?_
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ ∑ _ : Fin n × Fin n, (1:ℝ) :=
      Finset.sum_le_sum fun _ _ => (longWeight_mem hβ hR d κ n _).2
    _ = _ := by simp [pow_two, nsmul_eq_mul]

/-- The normalized omitted weight can be made arbitrarily small almost
surely, eventually in size, simultaneously for all larger length cutoffs. -/
theorem ae_eventually_longAssignmentMass_div_lt {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {β d κ ε : ℝ} (hβ : 0 < β) (hd : 0 < d) (hκ : 0 < κ)
    (hμ : SmallCostTail μ κ d) (hε : 0 < ε) :
    ∃ R : ℕ, 0 < R ∧ ∀ᵐ C ∂iidCosts μ, ∀ᶠ n in atTop, ∀ R' : ℝ, (R : ℝ) ≤ R' →
      longAssignmentMass β d κ R' n C / (n : ℝ) < ε := by
  let : IsProbabilityMeasure (iidCosts μ) := by unfold iidCosts; infer_instance
  obtain ⟨K, hK, htail⟩ := scaled_costWeight_tail_le hκ hd hβ hμ
  let g (x : ℝ) := β * x ^ d * Real.exp (-β * x)
  let a := (Real.exp 1 - 1) * K
  have ha : 0 < a := mul_pos (sub_pos.mpr (Real.one_lt_exp_iff.mpr zero_lt_one)) hK
  have hdecay : Tendsto (fun R : ℕ => a * ∫ x in Ioi (R : ℝ), g x) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_integral_Ioi_zero (μ := volume) (f := g) tendsto_natCast_atTop_atTop).const_mul a
  obtain ⟨R, hp, hR⟩ := ((hdecay.eventually (Iio_mem_nhds (half_pos hε))).and
    (eventually_gt_atTop (0 : ℕ))).exists
  let s := ∫ x in Ioi (R : ℝ), g x
  have hR₀ : 0 ≤ (R : ℝ) := Nat.cast_nonneg _
  have hs₀ : 0 ≤ᵐ[volume.restrict (Ioi (R : ℝ))] g := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioi (a := (R : ℝ)))] with x hx
    exact mul_nonneg (mul_nonneg hβ.le (Real.rpow_nonneg (hR₀.trans hx.le) _)) (Real.exp_nonneg _)
  have hs : 0 ≤ s := integral_nonneg_of_ae hs₀
  have hmean {n : ℕ} (hn : 0 < n) : (∫ c, longWeight β d κ R n c ∂μ) ≤ (K / n) * s := by
    let f := longWeight β d κ R n
    have hm := measurable_longWeight β d κ R n
    have hfi : Integrable f μ := Integrable.of_bound hm.aestronglyMeasurable 1
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (longWeight_mem hβ hR₀ d κ n x).1]
        exact (longWeight_mem hβ hR₀ d κ n x).2)
    have hf : 0 ≤ᵐ[μ] f := Eventually.of_forall fun x => (longWeight_mem hβ hR₀ d κ n x).1
    rw [← ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by positivity) hs),
      ofReal_integral_eq_lintegral_ofReal hfi hf,
      ENNReal.ofReal_mul (by positivity),
      ofReal_integral_eq_lintegral_ofReal (integrable_gamma_tail hβ hd hR₀) hs₀]
    have heq : (fun c => ENNReal.ofReal (f c)) =
        {c | (R : ℝ) < lengthScale d κ n * c}.indicator
          (fun c => ENNReal.ofReal (Real.exp (-β * (lengthScale d κ n * c)))) := by
      funext c
      by_cases hc : (R : ℝ) < lengthScale d κ n * c
      · rw [Set.indicator_of_mem (show c ∈ {c | (R : ℝ) < lengthScale d κ n * c} from hc)]
        simp [f, longWeight, hc]
      · rw [Set.indicator_of_notMem (show c ∉ {c | (R : ℝ) < lengthScale d κ n * c} from hc)]
        simp [f, longWeight, hc]
    rw [heq, lintegral_indicator (measurableSet_lt measurable_const (by fun_prop))]
    exact (lintegral_mono_set (fun _ hc => (show (R : ℝ) < lengthScale d κ n * _ from hc).le)).trans
      (htail n hn R hR₀)
  have hmgf : ∀ᶠ n in atTop,
      mgf (longAssignmentMass β d κ R n) (iidCosts μ) 1 ≤ Real.exp ((ε / 2) * (n : ℝ)) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    let index : Fin n × Fin n ↪ ℕ × ℕ :=
      ⟨fun e => (e.1.val,e.2.val), fun e f he =>
        Prod.ext (Fin.ext (congrArg Prod.fst he)) (Fin.ext (congrArg Prod.snd he))⟩
    unfold longAssignmentMass
    rw [show (fun C : CostArray =>
        ∑ e : Fin n × Fin n, longWeight β d κ R n (C (e.1.val,e.2.val))) =
          (fun C : CostArray => ∑ e : Fin n × Fin n, longWeight β d κ R n (C (index e))) from rfl,
      mgf_sum_iid_entries μ index (measurable_longWeight ..) 1]
    have h' := mgf_one_le_exp_mean μ (measurable_longWeight β d κ R n)
      (longWeight_mem hβ hR₀ d κ n)
    have hM := h'.trans (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (hmean hn) (sub_nonneg.mpr (Real.one_le_exp_iff.mpr zero_le_one))))
    refine (pow_le_pow_left₀ mgf_nonneg hM _).trans ?_
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    rw [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    have hcalc : (n : ℝ) * n * ((Real.exp 1 - 1) * (K / n * s)) = (a * s) * n := by
      dsimp only [a]
      field_simp
    rw [hcalc]
    exact mul_le_mul_of_nonneg_right (show a * s ≤ ε / 2 from hp.le) hn'.le
  refine ⟨R,hR,?_⟩
  filter_upwards [ae_eventually_lt_linear_of_mgf (iidCosts μ) (half_pos hε)
    (integrable_exp_longAssignmentMass hβ hR₀ d κ) hmgf] with C hC
  filter_upwards [hC, eventually_gt_atTop (0 : ℕ)] with n hn1 hn R' hR'
  have hmono : longAssignmentMass β d κ R' n C ≤ longAssignmentMass β d κ R n C := by
    apply sum_le_sum
    intro e _
    unfold longWeight
    split_ifs with hi hj
    · rfl
    · exact False.elim (hj (hR'.trans_lt hi))
    · positivity
    · rfl
  apply (div_lt_iff₀ (Nat.cast_pos.mpr hn)).mpr
  exact hmono.trans_lt (by simpa only [add_halves] using hn1)

end Certificate.Overlap

import Certificate.Model
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Gamma

/-!
# Uniform bounds for scaled edge weights

The CDF bound from the small-cost hypothesis controls the normalized expected
mass of all long edges. The proof uses Tonelli and works for cost laws with atoms.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

namespace Certificate

theorem cdf_le_power {μ : Measure ℝ} [IsProbabilityMeasure μ] {κ d : ℝ}
    (hd : 0 < d) (hκ : 0 < κ) (h : SmallCostTail μ κ d) :
    ∃ K : ℝ, 0 < K ∧ ∀ t > 0, cdf μ t ≤ K * t ^ d := by
  have hnear := (tendsto_order.mp h.2).2 2 (by norm_num)
  obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hnear
  let K := max (2 * κ) (1 / δ ^ d)
  have hK : 0 < K := (mul_pos two_pos hκ).trans_le (le_max_left ..)
  refine ⟨K, hK, ?_⟩
  intro t ht
  by_cases htd : t < δ
  · have hlt : cdf μ t / (κ * t ^ d) < 2 := hsub ⟨ht, htd⟩
    have ht' := Real.rpow_pos_of_pos ht d
    have hcdf := (div_lt_iff₀ (mul_pos hκ ht')).mp hlt
    calc
      cdf μ t ≤ (2 * κ) * t ^ d := by linarith only [hcdf]
      _ ≤ K * t ^ d := mul_le_mul_of_nonneg_right (le_max_left ..) ht'.le
  · have hd' : 0 < δ ^ d := Real.rpow_pos_of_pos hδ _
    have hpow := Real.rpow_le_rpow hδ.le (le_of_not_gt htd) hd.le
    calc
      cdf μ t ≤ 1 := cdf_le_one μ t
      _ ≤ (1 / δ ^ d) * t ^ d := by
        rw [one_div, ← div_eq_inv_mul, one_le_div hd']
        exact hpow
      _ ≤ K * t ^ d :=
        mul_le_mul_of_nonneg_right (le_max_right ..) (Real.rpow_nonneg ht.le _)

theorem scaled_cdf_le_power {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {κ d K : ℝ} (hκ : 0 < κ) (hd : 0 < d)
    (hK : ∀ t > 0, cdf μ t ≤ K * t ^ d) {n : ℕ} (hn : 0 < n)
    {x : ℝ} (hx : 0 < x) :
    μ {c | lengthScale d κ n * c ≤ x} ≤ ENNReal.ofReal (K / κ / n * x ^ d) := by
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hκn := mul_pos hκ hn'
  have hscale : 0 < lengthScale d κ n := Real.rpow_pos_of_pos hκn _
  have hpow : (lengthScale d κ n) ^ d = κ * n := by
    rw [lengthScale, ← Real.rpow_mul hκn.le, one_div_mul_cancel hd.ne', Real.rpow_one]
  have hset : {c : ℝ | lengthScale d κ n * c ≤ x} = Iic (x / lengthScale d κ n) := by
    ext c
    change lengthScale d κ n * c ≤ x ↔ c ≤ x / lengthScale d κ n
    rw [le_div_iff₀ hscale, mul_comm]
  rw [hset, ← ofReal_cdf]
  apply ENNReal.ofReal_le_ofReal
  refine (hK _ (div_pos hx hscale)).trans_eq ?_
  rw [Real.div_rpow hx.le hscale.le, hpow]
  field_simp

private theorem lintegral_exp_kernel (x : ℝ) {β : ℝ} (hβ : 0 < β) :
    ∫⁻ t : ℝ in Ioi x, ENNReal.ofReal (β * Real.exp (-β * t)) =
      ENNReal.ofReal (Real.exp (-β * x)) := by
  have hInt : IntegrableOn (fun t : ℝ ↦ β * Real.exp (-β * t)) (Ioi x) :=
    (exp_neg_integrableOn_Ioi x hβ).const_mul β
  have hNN : 0 ≤ᵐ[volume.restrict (Ioi x)] (fun t : ℝ ↦ β * Real.exp (-β * t)) :=
    .of_forall fun t ↦ mul_nonneg hβ.le (Real.exp_nonneg _)
  rw [← ofReal_integral_eq_lintegral_ofReal hInt hNN, integral_const_mul,
    integral_exp_mul_Ioi (neg_neg_of_pos hβ)]
  congr 1
  field_simp

/-- A Stieltjes tail bound, written as a nonnegative integral to avoid density
assumptions on the random edge lengths. -/
theorem lintegral_exp_tail_le_of_cdf {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] {X : Ω → ℝ} (hX : Measurable X)
    {β d K R : ℝ} (hβ : 0 < β) (hR : 0 ≤ R) (hK : 0 ≤ K)
    (hCDF : ∀ t > 0, μ {ω | X ω ≤ t} ≤ ENNReal.ofReal (K * t ^ d)) :
    (∫⁻ ω in {ω | R ≤ X ω}, ENNReal.ofReal (Real.exp (-β * X ω)) ∂μ) ≤
      ENNReal.ofReal K * ∫⁻ t : ℝ in Ioi R, ENNReal.ofReal (β * t ^ d * Real.exp (-β * t)) := by
  let w : ℝ → ℝ≥0∞ := fun t ↦ ENNReal.ofReal (β * Real.exp (-β * t))
  have hw : Measurable w := by unfold w; fun_prop
  let E : Set (Ω × ℝ) := {p | R ≤ X p.1 ∧ X p.1 < p.2}
  have hE : MeasurableSet E :=
    (measurableSet_le measurable_const (hX.comp measurable_fst)).inter
      (measurableSet_lt (hX.comp measurable_fst) measurable_snd)
  let F : Ω → ℝ → ℝ≥0∞ := fun ω t ↦ E.indicator (fun p ↦ w p.2) (ω, t)
  have hF : Measurable (Function.uncurry F) := (hw.comp measurable_snd).indicator hE
  have hset : MeasurableSet {ω | R ≤ X ω} := measurableSet_le measurable_const hX
  rw [← lintegral_indicator hset]
  have hinner (ω : Ω) :
      {ω | R ≤ X ω}.indicator (fun ω ↦ ENNReal.ofReal (Real.exp (-β * X ω))) ω =
      ∫⁻ t in Ioi R, F ω t := by
    by_cases ht : R ≤ X ω
    · have hEq : F ω = (Ioi (X ω)).indicator w := by
        funext t
        simp [F, E, ht, Set.indicator_apply]
      rw [Set.indicator_of_mem (show ω ∈ {ω | R ≤ X ω} from ht), hEq,
        lintegral_indicator measurableSet_Ioi,
        Measure.restrict_restrict_of_subset (Ioi_subset_Ioi ht)]
      exact (lintegral_exp_kernel _ hβ).symm
    · have hEq : F ω = 0 := by funext t; simp [F, E, ht]
      rw [Set.indicator_of_notMem (show ω ∉ {ω | R ≤ X ω} from ht), hEq]
      simp
  simp_rw [hinner]
  rw [lintegral_lintegral_swap hF.aemeasurable,
    ← lintegral_const_mul _ (by fun_prop)]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
  have ht0 : 0 < t := hR.trans_lt ht
  let A : Set Ω := {ω | R ≤ X ω ∧ X ω < t}
  have hA : MeasurableSet A :=
    hset.inter (measurableSet_lt hX measurable_const)
  have hEq : (fun ω ↦ F ω t) = A.indicator (fun _ ↦ w t) := by
    funext ω
    simp [F, E, A, Set.indicator_apply]
  rw [hEq, lintegral_indicator_const hA]
  calc
    _ ≤ w t * ENNReal.ofReal (K * t ^ d) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (measure_mono (fun _ hω ↦ hω.2.le)).trans (hCDF t ht0)
    _ = _ := by
      dsimp [w]
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hK]
      congr 1
      ring

/-- Uniformly in graph size, expected scaled weight above a cutoff is dominated
by an integrable gamma tail. The cutoff may be zero to bound the entire weight. -/
theorem scaled_costWeight_tail_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {κ d β : ℝ} (hκ : 0 < κ) (hd : 0 < d) (hβ : 0 < β)
    (h : SmallCostTail μ κ d) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 0 < n → ∀ R : ℝ, 0 ≤ R →
      (∫⁻ c in {c | R ≤ lengthScale d κ n * c},
        ENNReal.ofReal (Real.exp (-β * (lengthScale d κ n * c))) ∂μ) ≤
      ENNReal.ofReal (K / n) *
        ∫⁻ t : ℝ in Ioi R, ENNReal.ofReal (β * t ^ d * Real.exp (-β * t)) := by
  obtain ⟨C, hC, hCDF⟩ := cdf_le_power hd hκ h
  refine ⟨C / κ, div_pos hC hκ, fun n hn R hR ↦ ?_⟩
  exact lintegral_exp_tail_le_of_cdf μ (by fun_prop) hβ hR (by positivity)
    (fun _ hx ↦ scaled_cdf_le_power hκ hd hCDF hn hx)

end Certificate

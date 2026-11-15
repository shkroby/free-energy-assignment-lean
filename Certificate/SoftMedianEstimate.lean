import Certificate.ArrivalMedianTail
import Certificate.CavityPrefixTail
import Certificate.HardLogLowerTail

/-!
# Bounding a shifted soft recursion

Use the coarse upper tail on a bounded length window and the first
qualifying child bound beyond that window.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace Certificate

/-- The shifted outgoing mass on the canonical marked arrival process. -/
noncomputable def shiftedArrivalMass (β d b : ℝ) (ω : ArrivalConfiguration) : ℝ≥0∞ :=
  arrivalSum d (fun p ↦ if 0 < p.1
    then ENNReal.ofReal (Real.exp (-β * p.1) * (Real.exp (β * b) * p.2)) else 0) ω

/-- Bound the upper tail of the shifted sum for any nonnegative law and
any real threshold used for splitting its short-edge marks. -/
theorem measure_shiftedArrivalMass_gt_le {β d s b R : ℝ} (hd : 0 < d) (hβ : 0 < β)
    (hR : 0 ≤ R) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {ε : ℝ≥0∞} (hε : ε ≠ 0) (hε' : ε ≠ ∞) :
    markedSpacings μ {ω | ε < shiftedArrivalMass β d b ω} ≤
      (ENNReal.ofReal (R ^ d) * μ (Ioi (Real.exp (β * s))) +
        ∫⁻ x in Ioi R, μ (Ioi (Real.exp (β * (x / 2 - b)))) ∂intensity d) +
      (ENNReal.ofReal (R ^ d * Real.exp (β * (b + s))) +
        ∫⁻ x in Ioi R, ENNReal.ofReal (Real.exp (-β * x / 2)) ∂intensity d) / ε := by
  let near : Set ℝ := Ioc 0 R
  let far : Set ℝ := Ioi R
  let S₀ := near ×ˢ Ioi (Real.exp (β * s))
  let S₁ : Set (ℝ × ℝ) := {p | R < p.1 ∧ Real.exp (β * (p.1 / 2 - b)) < p.2}
  let C := ENNReal.ofReal (Real.exp (β * (b + s)))
  let G (x : ℝ) := near.indicator (fun _ ↦ C) x +
    far.indicator (fun x ↦ ENNReal.ofReal (Real.exp (-β * x / 2))) x
  have hNear : MeasurableSet near := measurableSet_Ioc
  have hFar : MeasurableSet far := measurableSet_Ioi
  have hG : Measurable G :=
    (measurable_const.indicator hNear).add ((by fun_prop : Measurable
      (fun x ↦ ENNReal.ofReal (Real.exp (-β * x / 2)))).indicator hFar)
  have hS₁ : MeasurableSet S₁ :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt (by fun_prop) measurable_snd)
  have hbound (p : ℝ × ℝ) (hp : p ∉ S₀ ∪ S₁) :
      (if 0 < p.1 then ENNReal.ofReal (Real.exp (-β * p.1) * (Real.exp (β * b) * p.2))
        else 0) ≤ G p.1 := by
    by_cases hx : 0 < p.1
    · rw [if_pos hx]
      by_cases hR' : p.1 ≤ R
      · have hn : p.1 ∈ near := ⟨hx, hR'⟩
        have hm : p.2 ≤ Real.exp (β * s) := le_of_not_gt fun h ↦ hp (Or.inl ⟨hn, h⟩)
        have hw : Real.exp (-β * p.1) ≤ 1 := Real.exp_le_one_iff.mpr
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hβ.le) hx.le)
        unfold G
        rw [indicator_of_mem hn]
        refine le_add_right ?_
        apply ENNReal.ofReal_le_ofReal
        calc
          _ ≤ Real.exp (-β * p.1) * (Real.exp (β * b) * Real.exp (β * s)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm (Real.exp_nonneg _)) (Real.exp_nonneg _)
          _ ≤ 1 * (Real.exp (β * b) * Real.exp (β * s)) :=
            mul_le_mul_of_nonneg_right hw (by positivity)
          _ = Real.exp (β * (b + s)) := by rw [one_mul, ← Real.exp_add]; congr 1; ring
      · have hf : p.1 ∈ far := lt_of_not_ge hR'
        have hm : p.2 ≤ Real.exp (β * (p.1 / 2 - b)) :=
          le_of_not_gt fun h ↦ hp (Or.inr ⟨hf, h⟩)
        unfold G
        rw [indicator_of_mem hf]
        refine (ENNReal.ofReal_le_ofReal ?_).trans le_add_self
        calc
          _ ≤ Real.exp (-β * p.1) * (Real.exp (β * b) * Real.exp (β * (p.1 / 2 - b))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm (Real.exp_nonneg _)) (Real.exp_nonneg _)
          _ = Real.exp (-β * p.1 / 2) := by
            rw [← Real.exp_add, ← Real.exp_add]
            congr 1
            ring
    · rw [if_neg hx]
      exact zero_le
  have hs := measure_arrival_sum_gt_le_of_envelope hd μ (hG.comp measurable_fst)
    ((hNear.prod measurableSet_Ioi).union hS₁) hbound hε hε'
  have hS₀Mass : ((intensity d).prod μ) S₀ =
      ENNReal.ofReal (R ^ d) * μ (Ioi (Real.exp (β * s))) := by
    rw [Measure.prod_prod, intensity_Ioc_zero hd hR]
  have hS₁Mass : ((intensity d).prod μ) S₁ =
      ∫⁻ x in Ioi R, μ (Ioi (Real.exp (β * (x / 2 - b)))) ∂intensity d := by
    rw [Measure.prod_apply hS₁, ← lintegral_indicator hFar]
    apply lintegral_congr
    intro x
    by_cases hx : x ∈ far
    · have H : Prod.mk x ⁻¹' S₁ = Ioi (Real.exp (β * (x / 2 - b))) := by
        ext y
        simp [S₁, show R < x from hx]
      rw [H, indicator_of_mem hx]
    · have H : Prod.mk x ⁻¹' S₁ = ∅ := by
        ext y
        simp [S₁, show ¬ R < x from hx]
      rw [H, measure_empty, indicator_of_notMem hx]
  have hGIntegral : (∫⁻ p : ℝ × ℝ, (G ∘ Prod.fst) p ∂(intensity d).prod μ) =
      ENNReal.ofReal (R ^ d * Real.exp (β * (b + s))) +
        ∫⁻ x in Ioi R, ENNReal.ofReal (Real.exp (-β * x / 2)) ∂intensity d := by
    have H : (∫⁻ p : ℝ × ℝ, (G ∘ Prod.fst) p ∂(intensity d).prod μ) = ∫⁻ x, G x ∂intensity d := by
      rw [lintegral_prod _ (hG.comp measurable_fst).aemeasurable]
      simp only [Function.comp_apply, lintegral_const, measure_univ, mul_one]
    rw [H]
    unfold G
    rw [lintegral_add_left (measurable_const.indicator hNear), lintegral_indicator_const hNear,
      lintegral_indicator hFar, intensity_Ioc_zero hd hR,
      ENNReal.ofReal_mul (Real.rpow_nonneg hR d), mul_comm C]
  apply hs.trans
  rw [hGIntegral, ← hS₀Mass, ← hS₁Mass]
  exact add_le_add_left (measure_union_le _ _) _

/-- Half the mass below a proposed median forces the shifted outgoing
sum to exceed one half if the fugacity term already contributes at most a quarter. -/
theorem half_le_measure_shiftedArrivalMass_of_median {β d z b : ℝ} (hz : 0 < z)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hfin : ∀ᵐ ω ∂markedSpacings μ, arrivalWeightedSum β d ω ≠ ∞)
    (hLaw : (markedSpacings μ).map (arrivalSoftOutput β d z) = μ)
    (hb : 1 / 2 ≤ (μ (Iic (Real.exp (β * b)))).toReal)
    (hsmall : z * Real.exp (β * b) ≤ 1 / 4) :
    ENNReal.ofReal (1 / 2) ≤ markedSpacings μ
      {ω | ENNReal.ofReal (1 / 2) < shiftedArrivalMass β d b ω} := by
  let C := Real.exp (β * b)
  have hC : 0 < C := Real.exp_pos _
  have hAE : (arrivalSoftOutput β d z ⁻¹' Iic C) ≤ᵐ[markedSpacings μ]
      {ω | ENNReal.ofReal (1 / 2) < shiftedArrivalMass β d b ω} := by
    filter_upwards [ae_marked_positive_spacings μ, hfin] with ω hω hf hle
    have hd : 0 < z + (arrivalWeightedSum β d ω).toReal := by positivity
    have hlt : (z + (arrivalWeightedSum β d ω).toReal)⁻¹ ≤ C := hle
    have hprod : 1 ≤ C * (z + (arrivalWeightedSum β d ω).toReal) :=
      (inv_le_iff_one_le_mul₀ hd).mp hlt
    have hgt : (1 / 2 : ℝ) < C * (arrivalWeightedSum β d ω).toReal := by
      nlinarith only [hprod, show z * C ≤ 1 / 4 from hsmall]
    have hEq : shiftedArrivalMass β d b ω =
        ENNReal.ofReal C * arrivalWeightedSum β d ω := by
      unfold shiftedArrivalMass arrivalSum arrivalWeightedSum
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro i
      dsimp only [Prod.fst, Prod.snd]
      rw [if_pos (arrivalLength_pos_of_positive_spacings hω i)]
      unfold cavityTerm
      rw [← ENNReal.ofReal_mul hC.le]
      congr 1
      ring
    change ENNReal.ofReal (1 / 2) < shiftedArrivalMass β d b ω
    rw [hEq, ← ENNReal.ofReal_toReal hf, ← ENNReal.ofReal_mul hC.le]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num)).mpr hgt
  have hMeasure : markedSpacings μ (arrivalSoftOutput β d z ⁻¹' Iic C) = μ (Iic C) := by
    rw [← Measure.map_apply (measurable_arrivalSoftOutput ..) measurableSet_Iic, hLaw]
  calc
    _ ≤ μ (Iic C) := (ENNReal.ofReal_le_ofReal hb).trans_eq
      (ENNReal.ofReal_toReal (measure_ne_top _ _))
    _ = markedSpacings μ (arrivalSoftOutput β d z ⁻¹' Iic C) := hMeasure.symm
    _ ≤ _ := measure_mono_ae hAE

end Certificate

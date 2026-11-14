import Certificate.Model
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Interval masses of the pseudodimension intensity

The density used in the cavity formula assigns mass `x ^ d` to `(0, x]`.
The calculation includes the case `0 < d < 1`, where the density need not
be bounded near zero.
-/

open Set MeasureTheory
open scoped ENNReal

namespace Certificate

theorem sigmaFinite_intensity (d : ℝ) : SigmaFinite (intensity d) := by
  unfold intensity
  infer_instance

theorem intensity_Iic_zero (d : ℝ) : intensity d (Iic 0) = 0 := by
  rw [intensity, withDensity_apply _ measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
  have h : Iic (0 : ℝ) ∩ Ioi 0 = ∅ := by
    ext y
    simp only [mem_inter_iff, mem_Iic, mem_Ioi, notMem_empty, iff_false]
    exact fun ⟨hy, hy'⟩ => hy'.not_ge hy
  rw [h, Measure.restrict_empty]
  simp

/-- The intensity of `(a,b]` for nonnegative endpoints. -/
theorem intensity_Ioc {d a b : ℝ} (hd : 0 < d) (ha : 0 ≤ a) (hab : a ≤ b) :
    intensity d (Ioc a b) = ENNReal.ofReal (b ^ d - a ^ d) := by
  rw [intensity, withDensity_apply _ measurableSet_Ioc,
    Measure.restrict_restrict_of_subset (show Ioc a b ⊆ Ioi 0 from
      fun _ hy => ha.trans_lt hy.1)]
  have hr : -1 < d - 1 := by linarith
  have hpow : IntervalIntegrable (fun y : ℝ => y ^ (d - 1)) volume a b :=
    intervalIntegral.intervalIntegrable_rpow' hr
  have hi : Integrable (fun y : ℝ => d * y ^ (d - 1)) (volume.restrict (Ioc a b)) :=
    hpow.1.const_mul d
  have hn : 0 ≤ᵐ[volume.restrict (Ioc a b)] fun y : ℝ => d * y ^ (d - 1) := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with y hy
    exact mul_nonneg hd.le (Real.rpow_nonneg (ha.trans hy.1.le) _)
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn, integral_const_mul,
    ← intervalIntegral.integral_of_le hab, integral_rpow (Or.inl hr)]
  rw [sub_add_cancel, mul_div_cancel₀ _ hd.ne']

/-- The stated pseudodimension intensity has cumulative mass `x ^ d`. -/
theorem intensity_Ioc_zero {d x : ℝ} (hd : 0 < d) (hx : 0 ≤ x) :
    intensity d (Ioc 0 x) = ENNReal.ofReal (x ^ d) := by
  rw [intensity_Ioc hd le_rfl hx, Real.zero_rpow hd.ne', sub_zero]

private theorem clipped_Ioc {a b : ℝ} :
    Ioc a b ∩ Ioi 0 = Ioc (max 0 a) (max 0 b) := by
  ext y
  simp only [mem_inter_iff, mem_Ioc, mem_Ioi, max_lt_iff]
  constructor
  · rintro ⟨⟨hay, hyb⟩, hy⟩
    exact ⟨⟨hy, hay⟩, hyb.trans (le_max_right _ _)⟩
  · rintro ⟨⟨hy, hay⟩, hyb⟩
    exact ⟨⟨hay, (le_max_iff.mp hyb).resolve_left hy.not_ge⟩, hy⟩

/-- The intensity of an arbitrary bounded interval, clipping its endpoints at zero. -/
theorem intensity_Ioc_clipped {d a b : ℝ} (hd : 0 < d) (hab : a ≤ b) :
    intensity d (Ioc a b) = ENNReal.ofReal ((max 0 b) ^ d - (max 0 a) ^ d) := by
  have h := intensity_Ioc hd (le_max_left (0 : ℝ) a) (max_le_max_left 0 hab)
  rw [intensity, withDensity_apply _ measurableSet_Ioc,
    Measure.restrict_restrict_of_subset (show Ioc (max 0 a) (max 0 b) ⊆ Ioi 0 from
      fun _ hy => (le_max_left (0 : ℝ) a).trans_lt hy.1)] at h
  rw [intensity, withDensity_apply _ measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc, clipped_Ioc]
  exact h

private theorem preimage_rpow_Ioc_inter_Ioi {d a b : ℝ} (hd : 0 < d) :
    (fun y : ℝ => y ^ d⁻¹) ⁻¹' Ioc a b ∩ Ioi 0 =
      Ioc ((max 0 a) ^ d) ((max 0 b) ^ d) := by
  ext y
  have hr (hy : 0 < y) :
      y ^ d⁻¹ ∈ Ioc a b ↔ y ∈ Ioc ((max 0 a) ^ d) ((max 0 b) ^ d) := by
    let t := y ^ d⁻¹
    have ht : 0 < t := Real.rpow_pos_of_pos hy _
    have hty : t ^ d = y := Real.rpow_inv_rpow hy.le hd.ne'
    change t ∈ Ioc a b ↔ y ∈ Ioc ((max 0 a) ^ d) ((max 0 b) ^ d)
    rw [← hty]
    simp only [mem_Ioc, Real.rpow_lt_rpow_iff (le_max_left (0 : ℝ) a) ht.le hd,
      Real.rpow_le_rpow_iff ht.le (le_max_left (0 : ℝ) b) hd, max_lt_iff]
    constructor
    · rintro ⟨hat, htb⟩
      exact ⟨⟨ht, hat⟩, htb.trans (le_max_right _ _)⟩
    · rintro ⟨⟨_, hat⟩, htb⟩
      exact ⟨hat, (le_max_iff.mp htb).resolve_left ht.not_ge⟩
  constructor
  · rintro ⟨hy, hpos⟩
    exact (hr hpos).mp hy
  · intro hy
    have hpos : 0 < y := (Real.rpow_nonneg (le_max_left (0 : ℝ) a) d).trans_lt hy.1
    exact ⟨(hr hpos).mpr hy, hpos⟩

/-- Mapping unit-rate positive Lebesgue intensity by the power map gives the
intensity used for lengths in the pseudodimension model. -/
theorem map_volume_rpow_eq_intensity {d : ℝ} (hd : 0 < d) :
    (volume.restrict (Ioi (0 : ℝ))).map (fun y : ℝ => y ^ (1 / d : ℝ)) = intensity d := by
  rw [one_div]
  symm
  refine Measure.ext_of_Ioc' _ _ (fun _ _ hab => ?_) (fun _ _ hab => ?_)
  · rw [intensity_Ioc_clipped hd hab.le]
    exact ENNReal.ofReal_ne_top
  · rw [intensity_Ioc_clipped hd hab.le,
      Measure.map_apply (by fun_prop) measurableSet_Ioc,
      Measure.restrict_apply (measurableSet_Ioc.preimage (by fun_prop)),
      preimage_rpow_Ioc_inter_Ioi hd, Real.volume_Ioc]

end Certificate

import Certificate.CouplingOrthantOrder
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! Reciprocating both coordinates preserves concordance of positive couplings. -/

open Filter MeasureTheory Set
open scoped Topology ENNReal

namespace Certificate

private theorem orthantLE_open {ρ σ : ProbabilityMeasure (ℝ × ℝ)} (h : orthantLE ρ σ)
    (x y : ℝ) : (ρ : Measure (ℝ × ℝ)) (Iio x ×ˢ Iio y) ≤
      (σ : Measure (ℝ × ℝ)) (Iio x ×ˢ Iio y) := by
  let c (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hc (n : ℕ) : 0 < c n := by dsimp [c]; positivity
  have hcLim : Tendsto c atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hcAnti : Antitone c := by
    intro a b h
    exact one_div_le_one_div_of_le (by positivity) (add_le_add_left (Nat.cast_le.mpr h) 1)
  let C (n : ℕ) := Iic (x - c n) ×ˢ Iic (y - c n)
  have hm : Monotone C := by
    intro a b hab p hp
    exact ⟨mem_Iic.mpr ((mem_Iic.mp hp.1).trans (sub_le_sub_left (hcAnti hab) x)),
      mem_Iic.mpr ((mem_Iic.mp hp.2).trans (sub_le_sub_left (hcAnti hab) y))⟩
  have hU : (⋃ n, C n) = Iio x ×ˢ Iio y := by
    ext p
    constructor
    · intro hp
      obtain ⟨n, hn⟩ := mem_iUnion.mp hp
      exact ⟨mem_Iio.mpr ((mem_Iic.mp hn.1).trans_lt (sub_lt_self _ (hc n))),
        mem_Iio.mpr ((mem_Iic.mp hn.2).trans_lt (sub_lt_self _ (hc n)))⟩
    · intro hp
      have hpc : 0 < min (x - p.1) (y - p.2) := lt_min
        (sub_pos.mpr (mem_Iio.mp hp.1)) (sub_pos.mpr (mem_Iio.mp hp.2))
      obtain ⟨n, hn⟩ := (hcLim.eventually (Iio_mem_nhds hpc)).exists
      have hn' := lt_min_iff.mp hn
      exact mem_iUnion.mpr ⟨n, mem_Iic.mpr (by linarith [hn'.1]),
        mem_Iic.mpr (by linarith [hn'.2])⟩
  rw [← hU, hm.measure_iUnion, hm.measure_iUnion]
  exact iSup_mono fun n ↦ h (x - c n) (y - c n)

private theorem upperOrthantLE_of_orthantLE {ρ σ : ProbabilityMeasure (ℝ × ℝ)}
    (h : orthantLE ρ σ)
    (hfst : (ρ : Measure (ℝ × ℝ)).map Prod.fst = (σ : Measure (ℝ × ℝ)).map Prod.fst)
    (hsnd : (ρ : Measure (ℝ × ℝ)).map Prod.snd = (σ : Measure (ℝ × ℝ)).map Prod.snd)
    (x y : ℝ) :
    (ρ : Measure (ℝ × ℝ)) (Ici x ×ˢ Ici y) ≤ (σ : Measure (ℝ × ℝ)) (Ici x ×ˢ Ici y) := by
  let A : Set (ℝ × ℝ) := Prod.fst ⁻¹' Iio x
  let B : Set (ℝ × ℝ) := Prod.snd ⁻¹' Iio y
  have hA : MeasurableSet A := measurable_fst measurableSet_Iio
  have hB : MeasurableSet B := measurable_snd measurableSet_Iio
  have hρA : (ρ : Measure (ℝ × ℝ)) A = (σ : Measure (ℝ × ℝ)) A := by
    rw [← Measure.map_apply measurable_fst measurableSet_Iio, hfst,
      Measure.map_apply measurable_fst measurableSet_Iio]
  have hρB : (ρ : Measure (ℝ × ℝ)) B = (σ : Measure (ℝ × ℝ)) B := by
    rw [← Measure.map_apply measurable_snd measurableSet_Iio, hsnd,
      Measure.map_apply measurable_snd measurableSet_Iio]
  have hmAB : (ρ : Measure (ℝ × ℝ)).real (A ∩ B) ≤ (σ : Measure (ℝ × ℝ)).real (A ∩ B) :=
    ENNReal.toReal_mono (measure_ne_top _ _) (orthantLE_open h x y)
  have h₁ := measureReal_union_add_inter (μ := (ρ : Measure (ℝ × ℝ))) (s := A) hB
  have h₂ := measureReal_union_add_inter (μ := (σ : Measure (ℝ × ℝ))) (s := A) hB
  have hm : (σ : Measure (ℝ × ℝ)).real (A ∪ B) ≤ (ρ : Measure (ℝ × ℝ)).real (A ∪ B) := by
    have ha' := congrArg ENNReal.toReal hρA
    have hb' := congrArg ENNReal.toReal hρB
    change (ρ : Measure (ℝ × ℝ)).real A = (σ : Measure (ℝ × ℝ)).real A at ha'
    change (ρ : Measure (ℝ × ℝ)).real B = (σ : Measure (ℝ × ℝ)).real B at hb'
    linarith
  have he : Ici x ×ˢ Ici y = (A ∪ B)ᶜ := by
    ext p
    simp only [mem_prod, mem_Ici, mem_compl_iff, mem_union, A, B, mem_preimage, mem_Iio, not_or, not_lt]
  rw [he, ← ENNReal.ofReal_toReal (measure_ne_top (ρ : Measure (ℝ × ℝ)) _),
    ← ENNReal.ofReal_toReal (measure_ne_top (σ : Measure (ℝ × ℝ)) _)]
  apply ENNReal.ofReal_le_ofReal
  change (ρ : Measure (ℝ × ℝ)).real (A ∪ B)ᶜ ≤ (σ : Measure (ℝ × ℝ)).real (A ∪ B)ᶜ
  rw [probReal_compl_eq_one_sub (hA.union hB), probReal_compl_eq_one_sub (hA.union hB)]
  exact sub_le_sub_left hm _

/-- The simultaneous reciprocal in the two real coordinates. -/
noncomputable def pairInverse (p : ℝ × ℝ) : ℝ × ℝ := (p.1⁻¹, p.2⁻¹)

theorem measurable_pairInverse : Measurable pairInverse := measurable_fst.inv.prodMk measurable_snd.inv

/-- Simultaneous inversion preserves the orthant order for positive
joint laws with the same two marginals. -/
theorem orthantLE_map_pairInverse {ρ σ : ProbabilityMeasure (ℝ × ℝ)}
    (h : orthantLE ρ σ)
    (hfst : (ρ : Measure (ℝ × ℝ)).map Prod.fst = (σ : Measure (ℝ × ℝ)).map Prod.fst)
    (hsnd : (ρ : Measure (ℝ × ℝ)).map Prod.snd = (σ : Measure (ℝ × ℝ)).map Prod.snd)
    (hρ : ∀ᵐ p ∂(ρ : Measure (ℝ × ℝ)), 0 < p.1 ∧ 0 < p.2)
    (hσ : ∀ᵐ p ∂(σ : Measure (ℝ × ℝ)), 0 < p.1 ∧ 0 < p.2) :
    orthantLE (ρ.map measurable_pairInverse.aemeasurable) (σ.map measurable_pairInverse.aemeasurable) := by
  intro x y
  simp only [ProbabilityMeasure.toMeasure_map, Measure.map_apply measurable_pairInverse
    (measurableSet_Iic.prod measurableSet_Iic)]
  by_cases hx : 0 < x
  · by_cases hy : 0 < y
    · have hpre (Q : ProbabilityMeasure (ℝ × ℝ))
          (hQ : ∀ᵐ p ∂(Q : Measure (ℝ × ℝ)), 0 < p.1 ∧ 0 < p.2) :
          pairInverse ⁻¹' (Iic x ×ˢ Iic y) =ᵐ[(Q : Measure (ℝ × ℝ))] (Ici x⁻¹ ×ˢ Ici y⁻¹) := by
        filter_upwards [hQ] with p hp
        change (p.1⁻¹ ≤ x ∧ p.2⁻¹ ≤ y) = (x⁻¹ ≤ p.1 ∧ y⁻¹ ≤ p.2)
        exact propext (and_congr
          (by simpa only [inv_inv] using (inv_le_inv₀ hp.1 (inv_pos.mpr hx)))
          (by simpa only [inv_inv] using (inv_le_inv₀ hp.2 (inv_pos.mpr hy))))
      rw [measure_congr (hpre ρ hρ), measure_congr (hpre σ hσ)]
      exact upperOrthantLE_of_orthantLE h hfst hsnd x⁻¹ y⁻¹
    · have hzero : (ρ : Measure (ℝ × ℝ)) (pairInverse ⁻¹' (Iic x ×ˢ Iic y)) = 0 := by
        apply measure_eq_zero_iff_ae_notMem.mpr
        filter_upwards [hρ] with p hp H
        exact (not_le_of_gt ((le_of_not_gt hy).trans_lt (inv_pos.mpr hp.2))) H.2
      rw [hzero]
      exact zero_le
  · have hzero : (ρ : Measure (ℝ × ℝ)) (pairInverse ⁻¹' (Iic x ×ˢ Iic y)) = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [hρ] with p hp H
      exact (not_le_of_gt ((le_of_not_gt hx).trans_lt (inv_pos.mpr hp.1))) H.1
    rw [hzero]
    exact zero_le

end Certificate

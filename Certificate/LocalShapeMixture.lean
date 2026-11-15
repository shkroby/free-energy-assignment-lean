import Certificate.TreeBracketContinuity
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Bounded tests can be integrated shape by shape, with a vanishing complement. -/

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

namespace Certificate

/-- The expectation on one shape event, divided by its probability. -/
noncomputable def shapeConditionalMean {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A : Set Ω) (f : Ω → ℝ) : ℝ :=
  (∫ x in A, f x ∂μ) / μ.real A

private theorem setIntegral_mem_mul_interval {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Set Ω) {f : Ω → ℝ} {M : ℝ}
    (hf : Integrable f μ) (hB : ∀ᵐ x ∂μ, f x ∈ Icc 0 M) :
    (∫ x in A, f x ∂μ) ∈ Icc 0 (M * μ.real A) := by
  have hb : ∀ᵐ x ∂μ.restrict A, f x ∈ Icc 0 M := ae_mono Measure.restrict_le_self hB
  refine ⟨integral_nonneg_of_ae (hb.mono fun _ h ↦ h.1), ?_⟩
  have hi := integral_mono_ae hf.integrableOn (integrable_const M (μ := μ.restrict A))
    (hb.mono fun _ h ↦ h.2)
  simpa only [integral_const, measureReal_restrict_apply_univ, smul_eq_mul, mul_comm (μ.real A) M] using hi

/-- Pointwise convergence of shape probabilities and conditional test means
suffices when the limiting shape masses sum to one. The finite models may
put some mass outside all shape events. -/
theorem tendsto_integral_of_shape_cells
    {Ω I : Type*} [MeasurableSpace Ω] [Countable I]
    (P : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (P n)]
    (A : ℕ → I → Set Ω) (hA : ∀ n i, MeasurableSet (A n i))
    (hDisjoint : ∀ n, Pairwise (Disjoint on A n))
    (f : ℕ → Ω → ℝ) (hfi : ∀ n, Integrable (f n) (P n))
    {M : ℝ} (hM : 0 ≤ M) (hB : ∀ n, ∀ᵐ x ∂P n, f n x ∈ Icc 0 M)
    (q b : I → ℝ) (hq : Summable q) (hq₀ : ∀ i, 0 ≤ q i) (hq₁ : ∑' i, q i = 1)
    (hMass : ∀ i, Tendsto (fun n ↦ (P n).real (A n i)) atTop (𝓝 (q i)))
    (hCond : ∀ i, Tendsto (fun n ↦ shapeConditionalMean (P n) (A n i) (f n)) atTop (𝓝 (b i))) :
    Tendsto (fun n ↦ ∫ x, f n x ∂P n) atTop (𝓝 (∑' i, q i * b i)) := by
  let U (n : ℕ) := ⋃ i, A n i
  let p (n : ℕ) (i : I) := (P n).real (A n i)
  let a (n : ℕ) (i : I) := shapeConditionalMean (P n) (A n i) (f n)
  have hU (n : ℕ) : MeasurableSet (U n) := MeasurableSet.iUnion (hA n)
  have hSum (n : ℕ) : (∑' i, (P n) (A n i)) = (P n) (U n) :=
    (measure_iUnion (hDisjoint n) (hA n)).symm
  have hp (n : ℕ) : Summable (p n) := ENNReal.summable_toReal ((hSum n).trans_ne (measure_ne_top _ _))
  have hpU (n : ℕ) : (∑' i, p n i) = (P n).real (U n) := by
    unfold p Measure.real
    rw [← ENNReal.tsum_toReal_eq (fun _ ↦ measure_ne_top _ _), hSum n]
  have hUlim : Tendsto (fun n ↦ (P n).real (U n)) atTop (𝓝 1) := by
    have H := tendsto_tsum_of_shape_subprobabilities (M := (1 : ℝ)) (a := fun _ _ ↦ 1)
      (b := fun _ ↦ (1 : ℝ)) hp hq (fun n i ↦ measureReal_nonneg) hq₀
      (fun n ↦ (hpU n).le.trans measureReal_le_one) hq₁
      (fun _ _ ↦ ⟨zero_le_one, le_rfl⟩) hMass (fun _ ↦ tendsto_const_nhds)
    simpa only [mul_one, hpU, hq₁] using H
  have hWeighted (n : ℕ) (i : I) : p n i * a n i = ∫ x in A n i, f n x ∂P n := by
    have hb := setIntegral_mem_mul_interval (P n) (A n i) (hfi n) (hB n)
    by_cases hzero : p n i = 0
    · rw [hzero, zero_mul]
      have h₀ : (P n).real (A n i) = 0 := hzero
      rw [h₀, mul_zero] at hb
      exact le_antisymm hb.1 hb.2
    · dsimp [a, shapeConditionalMean, p] at *
      field_simp
  have ha (n : ℕ) (i : I) : a n i ∈ Icc 0 M := by
    have hb := setIntegral_mem_mul_interval (P n) (A n i) (hfi n) (hB n)
    by_cases hzero : p n i = 0
    · change (∫ x in A n i, f n x ∂P n) / p n i ∈ Icc 0 M
      rw [hzero, div_zero]
      exact ⟨le_rfl, hM⟩
    · have hpos : 0 < p n i := lt_of_le_of_ne' measureReal_nonneg hzero
      exact ⟨div_nonneg hb.1 measureReal_nonneg, (div_le_iff₀ hpos).mpr hb.2⟩
  have hMain : Tendsto (fun n ↦ ∫ x in U n, f n x ∂P n) atTop (𝓝 (∑' i, q i * b i)) := by
    refine (tendsto_tsum_of_shape_subprobabilities hp hq (fun _ _ ↦ measureReal_nonneg) hq₀
      (fun n ↦ (hpU n).le.trans measureReal_le_one) hq₁ ha hMass hCond).congr fun n ↦ ?_
    rw [integral_iUnion (hA n) (hDisjoint n) (hfi n).integrableOn]
    exact tsum_congr (hWeighted n)
  have hRest : Tendsto (fun n ↦ ∫ x in (U n)ᶜ, f n x ∂P n) atTop (𝓝 0) := by
    have hc : Tendsto (fun n ↦ M * (P n).real (U n)ᶜ) atTop (𝓝 0) := by
      simp_rw [probReal_compl_eq_one_sub (hU _)]
      simpa only [sub_self, mul_zero] using (hUlim.const_sub 1).const_mul M
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc
      (fun n ↦ (setIntegral_mem_mul_interval (P n) (U n)ᶜ (hfi n) (hB n)).1)
      (fun n ↦ (setIntegral_mem_mul_interval (P n) (U n)ᶜ (hfi n) (hB n)).2)
  refine (by simpa only [add_zero] using hMain.add hRest :
    Tendsto (fun n ↦ (∫ x in U n, f n x ∂P n) + (∫ x in (U n)ᶜ, f n x ∂P n)) atTop _).congr fun n ↦ ?_
  exact integral_add_compl (hU n) (hfi n)

end Certificate

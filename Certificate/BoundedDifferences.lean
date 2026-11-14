import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Bounded differences on a finite product

Independent coordinates are integrated one at a time. The conditional mean
at the next coordinate has the same oscillation bound as the original function.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Certificate

private theorem abs_integral_sub_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f g : Ω → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) {c : ℝ}
    (h : ∀ x, |f x - g x| ≤ c) :
    |(∫ x, f x ∂μ) - (∫ x, g x ∂μ)| ≤ c := by
  rw [← integral_sub hf hg, ← Real.norm_eq_abs]
  calc
    _ ≤ ∫ x, ‖(f - g) x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ _x : Ω, c ∂μ :=
      integral_mono (hf.sub hg).norm (integrable_const c)
        (fun x ↦ by simpa only [Pi.sub_apply, Real.norm_eq_abs] using h x)
    _ = c := by simp

/-- A function of `n` independent inputs with coordinate oscillation at most
`c` has a sub-Gaussian moment-generating function with variance proxy `n*c²`
after centering. -/
theorem hasSubgaussianMGF_of_bounded_differences
    {A : Type*} [MeasurableSpace A] (μ : Measure A) [IsProbabilityMeasure μ]
    {c : ℝ≥0} {a b : ℝ} :
    ∀ (n : ℕ) (f : (Fin n → A) → ℝ), Measurable f →
      (∀ x, f x ∈ Icc a b) →
      (∀ x y (i : Fin n), (∀ j ≠ i, x j = y j) → |f x - f y| ≤ c) →
      HasSubgaussianMGF
        (fun x ↦ f x - ∫ y, f y ∂Measure.pi (fun _ : Fin n ↦ μ))
        ((n : ℝ≥0) * c ^ 2) (Measure.pi (fun _ : Fin n ↦ μ)) := by
  intro n
  induction n with
  | zero =>
    intro f _ _ _
    have heq (x y : Fin 0 → A) : x = y := funext fun i ↦ Fin.elim0 i
    have hz : (fun x ↦ f x - ∫ y, f y ∂Measure.pi (fun _ : Fin 0 ↦ μ)) = 0 := by
      funext x
      have hf : f = fun _ ↦ f x := funext fun y ↦ congrArg f (heq y x)
      rw [← show (∫ y, f y ∂Measure.pi (fun _ : Fin 0 ↦ μ)) = f x by rw [hf, integral_const]; simp]
      exact sub_self _
    rw [hz]
    constructor
    · intro t
      simp
    · intro t
      simp [mgf]
  | succ n ih =>
    intro f hf hbounded hdiff
    let P : Measure (Fin n → A) := Measure.pi (fun _ ↦ μ)
    let Q : Measure (Fin (n + 1) → A) := Measure.pi (fun _ ↦ μ)
    let : IsProbabilityMeasure P := by unfold P; infer_instance
    let : IsProbabilityMeasure Q := by unfold Q; infer_instance
    let e : (A × (Fin n → A)) ≃ᵐ (Fin (n + 1) → A) :=
      (MeasurableEquiv.piFinSuccAbove (fun _ ↦ A) 0).symm
    have he : MeasurePreserving e (μ.prod P) Q :=
      (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ μ) 0).symm
    have he_tail (x : A) (y : Fin n → A) (j : Fin n) :
        e (x, y) ((0 : Fin (n + 1)).succAbove j) = y j := by
      change (0 : Fin (n + 1)).insertNth (α := fun _ ↦ A) x y ((0 : Fin (n + 1)).succAbove j) = y j
      exact Fin.insertNth_apply_succAbove (α := fun _ ↦ A) _ _ _ _
    have he_head (x : A) (y : Fin n → A) : e (x, y) 0 = x := by
      change (0 : Fin (n + 1)).insertNth (α := fun _ ↦ A) x y 0 = x
      exact Fin.insertNth_apply_same (α := fun _ ↦ A) _ _ _
    let F (x : A) (y : Fin n → A) := f (e (x, y))
    let G (x : A) : ℝ := ∫ y, F x y ∂P
    let m : ℝ := ∫ z, f z ∂Q
    have hfint : Integrable f Q :=
      Integrable.of_mem_Icc a b hf.aemeasurable (.of_forall hbounded)
    have hF (x : A) : Measurable (F x) :=
      hf.comp (e.measurable.comp (measurable_const.prodMk measurable_id))
    have hFint (x : A) : Integrable (F x) P :=
      Integrable.of_mem_Icc a b (hF x).aemeasurable (.of_forall fun y ↦ hbounded (e (x, y)))
    have hG : Measurable G :=
      ((hf.comp e.measurable).stronglyMeasurable.integral_prod_right' (ν := P)).measurable
    have hm : (∫ x, G x ∂μ) = m := by
      change (∫ x, ∫ y, f (e (x, y)) ∂P ∂μ) = ∫ z, f z ∂Q
      rw [← he.integral_comp' f]
      exact (integral_prod _ (he.integrable_comp_of_integrable hfint)).symm
    have hGb (x : A) : G x ∈ Icc a b := by
      constructor
      · simpa using integral_mono (integrable_const a) (hFint x)
          (fun y ↦ (hbounded (e (x, y))).1)
      · simpa using integral_mono (hFint x) (integrable_const b)
          (fun y ↦ (hbounded (e (x, y))).2)
    have hGint : Integrable G μ :=
      Integrable.of_mem_Icc a b hG.aemeasurable (.of_forall hGb)
    have hGdiff (x y : A) : |G x - G y| ≤ (c : ℝ) := by
      apply abs_integral_sub_le (hFint x) (hFint y)
      intro z
      apply hdiff _ _ 0
      intro j hj
      obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hj
      rw [he_tail, he_tail]
    have hGc (x : A) : |G x - m| ≤ (c : ℝ) := by
      rw [← hm, ← show (∫ _y : A, G x ∂μ) = G x by simp]
      exact abs_integral_sub_le (integrable_const _) hGint (hGdiff x)
    have hGcenter : HasSubgaussianMGF (fun x ↦ G x - m) (c ^ 2) μ := by
      have hzero : (∫ x, G x - m ∂μ) = 0 := by
        rw [integral_sub hGint (integrable_const _), integral_const, probReal_univ, one_smul, hm, sub_self]
      have hmem : ∀ᵐ x ∂μ, G x - m ∈ Icc (-(c : ℝ)) (c : ℝ) :=
        .of_forall fun x ↦ abs_le.mp (hGc x)
      have hh := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
        (hG.sub_const m).aemeasurable hmem hzero
      have hc : ‖(c : ℝ) - -(c : ℝ)‖₊ / 2 = c := by
        apply NNReal.eq
        rw [NNReal.coe_div, NNReal.coe_ofNat, coe_nnnorm,
          Real.norm_of_nonneg (by linarith [c.coe_nonneg])]
        ring
      rwa [hc] at hh
    have hinner (x : A) :
        HasSubgaussianMGF (fun y ↦ F x y - G x) ((n : ℝ≥0) * c ^ 2) P := by
      apply ih (F x) (hF x) (fun y ↦ hbounded (e (x, y)))
      intro y y' i hy
      apply hdiff _ _ ((0 : Fin (n + 1)).succAbove i)
      intro j hj
      by_cases hz : j = 0
      · subst j
        rw [he_head, he_head]
      · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hz
        have hki : k ≠ i := fun h ↦ hj (congrArg _ h)
        rw [he_tail, he_tail, hy k hki]
    have hAll (t : ℝ) : Integrable (fun z ↦ Real.exp (t * (f z - m))) Q :=
      integrable_exp_mul_of_mem_Icc (hf.sub_const m).aemeasurable <|
        .of_forall fun z ↦ ⟨sub_le_sub_right (hbounded z).1 _, sub_le_sub_right (hbounded z).2 _⟩
    constructor
    · exact hAll
    · intro t
      let M := Real.exp ((n : ℝ) * (c : ℝ) ^ 2 * t ^ 2 / 2)
      change (∫ z, Real.exp (t * (f z - m)) ∂Q) ≤ _
      have hI : Integrable (fun p : A × (Fin n → A) ↦ Real.exp (t * (f (e p) - m))) (μ.prod P) :=
        he.integrable_comp_of_integrable (hAll t)
      rw [← he.integral_comp' (fun z ↦ Real.exp (t * (f z - m))), integral_prod _ hI]
      calc
        _ ≤ ∫ x, Real.exp (t * (G x - m)) * M ∂μ := by
          have hL := (he.integrable_comp_of_integrable (hAll t)).integral_prod_left
          have hR := (hGcenter.integrable_exp_mul t).mul_const M
          apply integral_mono hL hR
          intro x
          change (∫ y, Real.exp (t * (F x y - m)) ∂P) ≤ _
          have hfac : (fun y ↦ Real.exp (t * (F x y - m))) =
              fun y ↦ Real.exp (t * (G x - m)) * Real.exp (t * (F x y - G x)) := by
            funext y
            rw [← Real.exp_add]
            congr 1
            ring
          rw [hfac, integral_const_mul]
          exact mul_le_mul_of_nonneg_left (by simpa [mgf, M] using (hinner x).mgf_le t)
            (Real.exp_nonneg _)
        _ ≤ Real.exp (((n + 1 : ℕ) : ℝ≥0) * c ^ 2 * t ^ 2 / 2) := by
          rw [integral_mul_const]
          have hG' := hGcenter.mgf_le t
          change (∫ x, Real.exp (t * (G x - m)) ∂μ) ≤ _ at hG'
          refine (mul_le_mul_of_nonneg_right hG' (Real.exp_nonneg _)).trans_eq ?_
          dsimp [M]
          rw [← Real.exp_add]
          congr 1
          push_cast
          ring

end Certificate

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
# Curvature of the finite Bethe simplex entropy

Weighted Cauchy–Schwarz absorbs the potentially negative contribution
of the largest coordinate. A third large coordinate leaves a uniform
positive remainder on the tangent hyperplane.
-/

open Finset
open scoped BigOperators

namespace Certificate.Overlap

variable {ι : Type*}

/-- A nonnegative vector of total mass one on the specified coordinates. -/
def SimplexOn (s : Finset ι) (b : ι → ℝ) : Prop :=
  (∀ i ∈ s, 0 ≤ b i) ∧ ∑ i ∈ s, b i = 1

/-- Three distinct coordinates in the simplex have mass at least eta. -/
def ThreeLargeOn (s : Finset ι) (b : ι → ℝ) (η : ℝ) : Prop :=
  ∃ i ∈ s, ∃ j ∈ s, ∃ k ∈ s,
    i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ η ≤ b i ∧ η ≤ b j ∧ η ≤ b k

/-- The one-coordinate Bethe entropy, including its continuous endpoint values. -/
noncomputable def betheAtom (x : ℝ) : ℝ :=
  -x * Real.log x + (1 - x) * Real.log (1 - x)

/-- The first derivative of the Bethe entropy on the open unit interval. -/
noncomputable def betheAtomSlope (x : ℝ) : ℝ :=
  -Real.log (x * (1 - x)) - 2

/-- The negative second derivative of the Bethe entropy on the open unit interval. -/
noncomputable def betheCurvature (x : ℝ) : ℝ :=
  (1 - 2 * x) / (x * (1 - x))

private noncomputable def curvatureFactor (x : ℝ) : ℝ :=
  (1 - 2 * x) / (1 - x)

private theorem betheCurvature_eq (x : ℝ) :
    betheCurvature x = curvatureFactor x / x := by
  unfold betheCurvature curvatureFactor
  rw [div_div, mul_comm (1 - x) x]

private theorem curvatureFactor_nonneg {x : ℝ} (hx : x ≤ 1 / 2) :
    0 ≤ curvatureFactor x :=
  div_nonneg (by linarith) (by linarith)

private theorem curvatureFactor_ge_add {x r η : ℝ} (hx : 0 ≤ x) (hx' : x < 1)
    (hr : 0 ≤ r) (hr' : r < 1) (hη : 0 ≤ η) (hSlack : η ≤ r - x) :
    curvatureFactor r + η ≤ curvatureFactor x := by
  have h₁ := sub_pos.mpr hx'
  have h₂ := sub_pos.mpr hr'
  have hid : curvatureFactor x - curvatureFactor r =
      (r - x) / ((1 - x) * (1 - r)) := by
    unfold curvatureFactor
    field_simp [h₁.ne', h₂.ne']
    ring
  have hBound : (1 - x) * (1 - r) ≤ 1 :=
    (mul_le_of_le_one_left h₂.le (by linarith)).trans (by linarith)
  have h := (le_div_iff₀ (mul_pos h₁ h₂)).mpr
    ((mul_le_of_le_one_right hη hBound).trans hSlack)
  rw [← hid] at h
  linarith only [h]

private theorem ThreeLargeOn.exists_outside {s : Finset ι} {b : ι → ℝ} {η : ℝ}
    (h : ThreeLargeOn s b η) (i j : ι) :
    ∃ k ∈ s, k ≠ i ∧ k ≠ j ∧ η ≤ b k := by
  classical
  obtain ⟨a, ha, b', hb, c, hc, hab, hac, hbc, hA, hB, hC⟩ := h
  by_cases h₁ : a ≠ i ∧ a ≠ j
  · exact ⟨a, ha, h₁.1, h₁.2, hA⟩
  by_cases h₂ : b' ≠ i ∧ b' ≠ j
  · exact ⟨b', hb, h₂.1, h₂.2, hB⟩
  have ha' : a = i ∨ a = j := by
    by_cases h : a = i
    · exact Or.inl h
    · exact Or.inr (not_not.mp fun h' => h₁ ⟨h, h'⟩)
  have hb' : b' = i ∨ b' = j := by
    by_cases h : b' = i
    · exact Or.inl h
    · exact Or.inr (not_not.mp fun h' => h₂ ⟨h, h'⟩)
  rcases ha' with hAi | hAj <;> rcases hb' with hBi | hBj
  · exact (hab (hAi.trans hBi.symm)).elim
  · exact ⟨c, hc, fun h' => hac (hAi.trans h'.symm), fun h' => hbc (hBj.trans h'.symm), hC⟩
  · exact ⟨c, hc, fun h' => hbc (hBi.trans h'.symm), fun h' => hac (hAj.trans h'.symm), hC⟩
  · exact (hab (hAj.trans hBj.symm)).elim

private theorem pairSlack_of_three {s : Finset ι} {b : ι → ℝ} {η : ℝ}
    (hb : SimplexOn s b) (h : ThreeLargeOn s b η) {i j : ι}
    (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) :
    η ≤ 1 - b i - b j := by
  classical
  obtain ⟨k, hk, hki, hkj, hlarge⟩ := h.exists_outside i j
  have hS : ({i, j, k} : Finset ι) ⊆ s :=
    Finset.insert_subset hi (Finset.insert_subset hj (Finset.singleton_subset_iff.mpr hk))
  have hs := Finset.sum_le_sum_of_subset_of_nonneg hS (fun a ha _ => hb.1 a ha)
  rw [hb.2] at hs
  simp [Finset.sum_insert, hij, hki.symm, hkj.symm] at hs
  linarith only [hs, hlarge]

private theorem pairSlack_nonneg {s : Finset ι} {b : ι → ℝ}
    (hb : SimplexOn s b) {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) :
    0 ≤ 1 - b i - b j := by
  classical
  have hS : ({i, j} : Finset ι) ⊆ s :=
    Finset.insert_subset hi (Finset.singleton_subset_iff.mpr hj)
  have hs := Finset.sum_le_sum_of_subset_of_nonneg hS (fun a ha _ => hb.1 a ha)
  rw [hb.2] at hs
  simp [Finset.sum_insert, hij] at hs
  linarith only [hs]

private theorem simplex_hessian_ge_of_pairSlack {s : Finset ι} {b v : ι → ℝ} {η : ℝ}
    (hb : SimplexOn s b) (hp : ∀ i ∈ s, b i ∈ Set.Ioo (0 : ℝ) 1)
    (hv : ∑ i ∈ s, v i = 0) (hη : 0 ≤ η)
    (hSlack : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → η ≤ 1 - b i - b j) :
    η / 4 * (∑ i ∈ s, |v i|)^2 ≤ ∑ i ∈ s, betheCurvature (b i) * v i^2 := by
  classical
  have hs : s.Nonempty := by
    by_contra h
    have ht := hb.2
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty] at ht
    exact zero_ne_one ht
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image s b hs
  let S := s.erase j
  let r := 1 - b j
  let A := ∑ i ∈ S, |v i|
  let T := ∑ i ∈ S, v i^2 / b i
  have hr : 0 < r := sub_pos.mpr (hp j hj).2
  have hr₁ : r ≤ 1 := by dsimp [r]; linarith [(hp j hj).1]
  have hrSum : ∑ i ∈ S, b i = r := by
    exact eq_sub_of_add_eq ((Finset.sum_erase_add s b hj).trans hb.2)
  have hvSum : ∑ i ∈ S, v i = -v j := by
    have hh := (Finset.sum_erase_add s v hj).trans hv
    change (∑ i ∈ S, v i) + v j = 0 at hh
    linarith only [hh]
  have hS (i : ι) (hi : i ∈ S) : i ∈ s := Finset.mem_of_mem_erase hi
  have hne (i : ι) (hi : i ∈ S) : i ≠ j := Finset.ne_of_mem_erase hi
  have hT : 0 ≤ T := Finset.sum_nonneg fun i hi => div_nonneg (sq_nonneg _) (hp i (hS i hi)).1.le
  have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hV : |v j| ≤ A := by
    calc
      |v j| = |∑ i ∈ S, v i| := by rw [hvSum, abs_neg]
      _ ≤ _ := Finset.abs_sum_le_sum_abs _ _
  have hCS : A^2 ≤ r * T := by
    have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul S
      (r := fun i => |v i|) (f := b) (g := fun i => v i^2 / b i)
      (fun i hi => (hp i (hS i hi)).1.le)
      (fun i hi => div_nonneg (sq_nonneg _) (hp i (hS i hi)).1.le)
      (fun i hi => by rw [sq_abs, mul_div_cancel₀ _ (hp i (hS i hi)).1.ne'])
    rw [hrSum] at h
    exact h
  have hL : ∑ i ∈ s, |v i| ≤ 2 * A := by
    rw [← Finset.sum_erase_add s (fun i => |v i|) hj]
    change A + |v j| ≤ 2 * A
    linarith only [hV]
  have hL₀ : 0 ≤ ∑ i ∈ s, |v i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hLT : (∑ i ∈ s, |v i|)^2 ≤ 4 * T := by
    calc
      _ ≤ (2 * A)^2 := pow_le_pow_left₀ hL₀ hL 2
      _ = 4 * A^2 := by ring
      _ ≤ 4 * T := mul_le_mul_of_nonneg_left
        (hCS.trans (mul_le_of_le_one_left hT hr₁)) (by norm_num)
  have hFirst : η / 4 * (∑ i ∈ s, |v i|)^2 ≤ η * T := by
    have h := mul_le_mul_of_nonneg_left hLT (div_nonneg hη (by norm_num : (0 : ℝ) ≤ 4))
    linarith only [h]
  apply hFirst.trans
  have hOutside (c : ℝ) (hc : ∀ i ∈ S, c ≤ curvatureFactor (b i)) :
      c * T ≤ ∑ i ∈ S, betheCurvature (b i) * v i^2 := by
    unfold T
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [betheCurvature_eq]
    have he : curvatureFactor (b i) / b i * v i^2 =
        curvatureFactor (b i) * (v i^2 / b i) := by ring
    rw [he]
    exact mul_le_mul_of_nonneg_right (hc i hi)
      (div_nonneg (sq_nonneg _) (hp i (hS i hi)).1.le)
  rw [← Finset.sum_erase_add s (fun i => betheCurvature (b i) * v i^2) hj]
  by_cases hjSmall : b j ≤ 1/2
  · have hOutsideη (i : ι) (hi : i ∈ S) : η ≤ curvatureFactor (b i) := by
      have hpair := hSlack i (hS i hi) j hj (hne i hi)
      have hnum : η ≤ 1 - 2 * b i := by linarith only [hpair, hmax i (hS i hi)]
      unfold curvatureFactor
      exact (le_div_iff₀ (sub_pos.mpr (hp i (hS i hi)).2)).mpr
        ((mul_le_of_le_one_right hη (by linarith [(hp i (hS i hi)).1])).trans hnum)
    have hzero : 0 ≤ betheCurvature (b j) * v j^2 := by
      rw [betheCurvature_eq]
      exact mul_nonneg (div_nonneg (curvatureFactor_nonneg hjSmall) (hp j hj).1.le) (sq_nonneg _)
    exact (hOutside η hOutsideη).trans (le_add_of_nonneg_right hzero)
  · have hrf : 0 ≤ curvatureFactor r := curvatureFactor_nonneg (by dsimp [r]; linarith [lt_of_not_ge hjSmall])
    have hOutsideη (i : ι) (hi : i ∈ S) : curvatureFactor r + η ≤ curvatureFactor (b i) := by
      apply curvatureFactor_ge_add (hp i (hS i hi)).1.le (hp i (hS i hi)).2 hr.le
        (by dsimp [r]; linarith [(hp j hj).1]) hη
      have h := hSlack i (hS i hi) j hj (hne i hi)
      dsimp [r]
      linarith only [h]
    have hheavy : betheCurvature (b j) * v j^2 = -curvatureFactor r * (v j^2 / r) := by
      dsimp [betheCurvature, curvatureFactor, r]
      field_simp [(hp j hj).1.ne', hr.ne']
      ring
    have hVj : v j^2 ≤ r * T := by
      have h := pow_le_pow_left₀ (abs_nonneg (v j)) hV 2
      rw [sq_abs] at h
      exact h.trans hCS
    have hAbsorb : curvatureFactor r * (v j^2 / r) ≤ curvatureFactor r * T :=
      mul_le_mul_of_nonneg_left ((div_le_iff₀ hr).mpr (by simpa only [mul_comm] using hVj)) hrf
    rw [hheavy]
    have h := hOutside _ hOutsideη
    change (curvatureFactor r + η) * T ≤ ∑ i ∈ S, betheCurvature (b i) * v i^2 at h
    linarith only [h, hAbsorb]

/-- The Bethe simplex Hessian is negative semidefinite on tangent vectors
at every vector with strictly interior coordinates. -/
theorem simplex_hessian_nonneg {s : Finset ι} {b v : ι → ℝ}
    (hb : SimplexOn s b) (hp : ∀ i ∈ s, b i ∈ Set.Ioo (0 : ℝ) 1)
    (hv : ∑ i ∈ s, v i = 0) :
    0 ≤ ∑ i ∈ s, betheCurvature (b i) * v i^2 := by
  simpa using simplex_hessian_ge_of_pairSlack hb hp hv (le_refl (0 : ℝ))
    (fun _ hi _ hj hne => pairSlack_nonneg hb hi hj hne)

/-- Three coordinates of size at least eta give the manuscript's
quantitative lower bound for the negative simplex Hessian. -/
theorem simplex_hessian_ge_l1 {s : Finset ι} {b v : ι → ℝ} {η : ℝ}
    (hb : SimplexOn s b) (hp : ∀ i ∈ s, b i ∈ Set.Ioo (0 : ℝ) 1)
    (hv : ∑ i ∈ s, v i = 0) (hη : 0 ≤ η) (hLarge : ThreeLargeOn s b η) :
    η / 4 * (∑ i ∈ s, |v i|)^2 ≤ ∑ i ∈ s, betheCurvature (b i) * v i^2 :=
  simplex_hessian_ge_of_pairSlack hb hp hv hη fun _ hi _ hj hne =>
    pairSlack_of_three hb hLarge hi hj hne

end Certificate.Overlap

import Certificate.OverlapSimplexCurvature
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Concavity and tangent loss for the Bethe simplex entropy

Concavity on closed segments is checked on the coordinates active in their
interior. The quantitative tangent inequality uses the curvature on the
first half and the ordinary tangent bound on the rest.
-/

open Set Finset
open scoped BigOperators

namespace Certificate.Overlap

variable {ι : Type*}

theorem SimplexOn.le_one {s : Finset ι} {b : ι → ℝ} (h : SimplexOn s b) {i : ι}
    (hi : i ∈ s) : b i ≤ 1 :=
  (Finset.single_le_sum (fun j hj => h.1 j hj) hi).trans_eq h.2

/-- Bethe entropy of a finite probability vector. -/
noncomputable def simplexEntropy (s : Finset ι) (b : ι → ℝ) : ℝ :=
  ∑ i ∈ s, betheAtom (b i)

/-- The affine segment from the first simplex vector to the second. -/
def simplexSegment (b p : ι → ℝ) (t : ℝ) (i : ι) : ℝ :=
  b i + t * (p i - b i)

/-- The first variation of the simplex entropy at an interior vector. -/
noncomputable def simplexTangent (s : Finset ι) (b p : ι → ℝ) : ℝ :=
  ∑ i ∈ s, betheAtomSlope (b i) * (p i - b i)

theorem simplexSegment_mem {s : Finset ι} {b p : ι → ℝ} (hb : SimplexOn s b)
    (hp : SimplexOn s p) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    SimplexOn s (simplexSegment b p t) := by
  constructor
  · intro i hi
    have he : simplexSegment b p t i = (1-t) * b i + t * p i := by
      unfold simplexSegment
      ring
    rw [he]
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) (hb.1 i hi))
      (mul_nonneg ht.1 (hp.1 i hi))
  · simp only [simplexSegment, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
      hb.2, hp.2, sub_self, mul_zero, add_zero]

theorem continuous_betheAtom : Continuous betheAtom := by
  have hc : Continuous (fun x : ℝ => 1-x) := continuous_const.sub continuous_id
  unfold betheAtom
  simpa only [Function.comp_def, neg_mul] using
    Real.continuous_mul_log.fun_neg.fun_add (Real.continuous_mul_log.comp hc)

theorem hasDerivAt_betheAtom {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt betheAtom (betheAtomSlope x) x := by
  have hcomp : HasDerivAt (fun y : ℝ => (1-y)*Real.log (1-y))
      ((Real.log (1-x) + 1) * (-1)) x :=
    (Real.hasDerivAt_mul_log (sub_pos.mpr hx.2).ne').comp x
      ((hasDerivAt_id x).const_sub (1 : ℝ))
  have h := (Real.hasDerivAt_mul_log hx.1.ne').fun_neg.fun_add hcomp
  have hs : -(Real.log x + 1) + (Real.log (1-x) + 1) * (-1) = betheAtomSlope x := by
    rw [betheAtomSlope, Real.log_mul hx.1.ne' (sub_pos.mpr hx.2).ne']
    ring
  rw [hs] at h
  unfold betheAtom
  simpa only [neg_mul] using h

theorem hasDerivAt_betheAtomSlope {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt betheAtomSlope (-betheCurvature x) x := by
  have hi : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  have hsub : HasDerivAt (fun y : ℝ => 1-y) (-1) x := hi.const_sub 1
  have h : HasDerivAt (fun y : ℝ => y * (1-y)) (1-2*x) x :=
    (hi.fun_mul hsub).congr_deriv (by ring)
  unfold betheAtomSlope betheCurvature
  exact (h.log (mul_ne_zero hx.1.ne' (sub_pos.mpr hx.2).ne')).fun_neg.sub_const 2

private theorem continuous_simplexEntropy_curve (s : Finset ι) (b p : ι → ℝ) :
    Continuous (fun t => simplexEntropy s (simplexSegment b p t)) := by
  unfold simplexEntropy
  apply continuous_finsetSum
  intro i _
  apply continuous_betheAtom.comp
  unfold simplexSegment
  fun_prop

private theorem hasDerivAt_simplexEntropy_curve {s : Finset ι} {b p : ι → ℝ} {t : ℝ}
    (ht : ∀ i ∈ s, simplexSegment b p t i ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun u => simplexEntropy s (simplexSegment b p u))
      (∑ i ∈ s, betheAtomSlope (simplexSegment b p t i) * (p i - b i)) t := by
  unfold simplexEntropy
  apply HasDerivAt.fun_sum
  intro i hi
  have hlin : HasDerivAt (fun u => simplexSegment b p u i) (p i-b i) t := by
    simpa only [simplexSegment, id_eq, one_mul] using
      (((hasDerivAt_id t).mul_const (p i-b i)).const_add (b i))
  exact (hasDerivAt_betheAtom (ht i hi)).comp t hlin

private noncomputable def entropySlopeCurve (s : Finset ι) (b p : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i ∈ s, betheAtomSlope (simplexSegment b p t i) * (p i - b i)

private noncomputable def entropyCurvatureCurve (s : Finset ι) (b p : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i ∈ s, betheCurvature (simplexSegment b p t i) * (p i - b i)^2

private theorem hasDerivAt_simplexSlope_curve {s : Finset ι} {b p : ι → ℝ} {t : ℝ}
    (ht : ∀ i ∈ s, simplexSegment b p t i ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (entropySlopeCurve s b p) (-entropyCurvatureCurve s b p t) t := by
  unfold entropySlopeCurve entropyCurvatureCurve
  rw [← Finset.sum_neg_distrib]
  apply HasDerivAt.fun_sum
  intro i hi
  have hlin : HasDerivAt (fun u => simplexSegment b p u i) (p i-b i) t := by
    simpa only [simplexSegment, id_eq, one_mul] using
      (((hasDerivAt_id t).mul_const (p i-b i)).const_add (b i))
  exact (((hasDerivAt_betheAtomSlope (ht i hi)).comp t hlin).mul_const (p i-b i)).congr_deriv
    (by ring)

private theorem entropyCurvatureCurve_nonneg {s : Finset ι} {b p : ι → ℝ}
    (hb : SimplexOn s b) (hp : SimplexOn s p) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hstrict : ∀ i ∈ s, simplexSegment b p t i ∈ Ioo (0 : ℝ) 1) :
    0 ≤ entropyCurvatureCurve s b p t :=
  simplex_hessian_nonneg (simplexSegment_mem hb hp ht) hstrict
    (by simp only [Finset.sum_sub_distrib, hp.2, hb.2, sub_self])

private theorem simplexEntropy_curve_concave_of_interior {s : Finset ι} {b p : ι → ℝ}
    (hb : SimplexOn s b) (hp : SimplexOn s p)
    (hstrict : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ i ∈ s, simplexSegment b p t i ∈ Ioo (0 : ℝ) 1) :
    ConcaveOn ℝ (Icc (0 : ℝ) 1) (fun t => simplexEntropy s (simplexSegment b p t)) := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _)
    (continuous_simplexEntropy_curve s b p).continuousOn
    (f' := entropySlopeCurve s b p) (f'' := fun t => -entropyCurvatureCurve s b p t)
  · intro t ht
    rw [interior_Icc] at ht
    exact (hasDerivAt_simplexEntropy_curve (hstrict t ht)).hasDerivWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    exact (hasDerivAt_simplexSlope_curve (hstrict t ht)).hasDerivWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    exact neg_nonpos.mpr (entropyCurvatureCurve_nonneg hb hp ⟨ht.1.le, ht.2.le⟩ (hstrict t ht))

/-- Concavity holds on the closed segment between any two simplex vectors,
including vectors with zero coordinates at either endpoint. -/
theorem simplexEntropy_segment_concave {s : Finset ι} {b p : ι → ℝ}
    (hb : SimplexOn s b) (hp : SimplexOn s p) :
    ConcaveOn ℝ (Icc (0 : ℝ) 1) (fun t => simplexEntropy s (simplexSegment b p t)) := by
  classical
  let S := s.filter (fun i => 0 < b i + p i)
  have hSub : S ⊆ s := Finset.filter_subset _ _
  have hzero (i : ι) (hi : i ∈ s) (hn : i ∉ S) : b i = 0 ∧ p i = 0 := by
    have h := fun ht : 0 < b i + p i => hn (Finset.mem_filter.mpr ⟨hi, ht⟩)
    exact ⟨by linarith [hb.1 i hi, hp.1 i hi, le_of_not_gt h],
      by linarith [hb.1 i hi, hp.1 i hi, le_of_not_gt h]⟩
  have hbS : SimplexOn S b := ⟨fun i hi => hb.1 i (hSub hi),
    (Finset.sum_subset hSub (fun i hi hn => (hzero i hi hn).1)).trans hb.2⟩
  have hpS : SimplexOn S p := ⟨fun i hi => hp.1 i (hSub hi),
    (Finset.sum_subset hSub (fun i hi hn => (hzero i hi hn).2)).trans hp.2⟩
  have he : (fun t => simplexEntropy s (simplexSegment b p t)) =
      (fun t => simplexEntropy S (simplexSegment b p t)) := by
    funext t
    unfold simplexEntropy
    symm
    apply Finset.sum_subset hSub
    intro i hi hn
    obtain ⟨hz₁, hz₂⟩ := hzero i hi hn
    simp [simplexSegment, betheAtom, hz₁, hz₂]
  rw [he]
  by_cases hOne : ∃ j ∈ S, ∀ i ∈ S, i = j
  · obtain ⟨j, hj, hAll⟩ := hOne
    have hSingle : S = {j} := by
      ext i
      rw [Finset.mem_singleton]
      exact ⟨hAll i, fun hi => hi.symm ▸ hj⟩
    have hb1 : b j = 1 := by simpa only [hSingle, Finset.sum_singleton] using hbS.2
    have hp1 : p j = 1 := by simpa only [hSingle, Finset.sum_singleton] using hpS.2
    have hc : (fun t => simplexEntropy S (simplexSegment b p t)) = (fun _ : ℝ => 0) := by
      funext t
      simp [simplexEntropy, hSingle, simplexSegment, hb1, hp1, betheAtom]
    rw [hc]
    exact concaveOn_const 0 (convex_Icc _ _)
  · apply simplexEntropy_curve_concave_of_interior hbS hpS
    intro t ht i hi
    have hq := simplexSegment_mem hbS hpS (show t ∈ Icc (0 : ℝ) 1 from ⟨ht.1.le, ht.2.le⟩)
    have hPos (j : ι) (hj : j ∈ S) : 0 < simplexSegment b p t j := by
      have hz := (Finset.mem_filter.mp hj).2
      have hq' : simplexSegment b p t j = (1-t) * b j + t * p j := by
        unfold simplexSegment
        ring
      rw [hq']
      rcases (hbS.1 j hj).eq_or_lt with h | h
      · rw [← h, mul_zero, zero_add]
        exact mul_pos ht.1 (by linarith only [hz, h])
      · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr ht.2) h)
          (mul_nonneg ht.1.le (hpS.1 j hj))
    have hOther : ∃ j ∈ S, j ≠ i := by
      by_contra! h
      exact hOne ⟨i, hi, h⟩
    obtain ⟨j, hj, hne⟩ := hOther
    have hj' := Finset.mem_erase.mpr ⟨hne, hj⟩
    have hsum := Finset.sum_erase_add S (simplexSegment b p t) hi
    have hle := Finset.single_le_sum (fun k hk => hq.1 k (Finset.mem_of_mem_erase hk)) hj'
    refine ⟨hPos i hi, ?_⟩
    rw [hq.2] at hsum
    linarith only [hsum, hle, hPos j hj]

/-- The finite Bethe simplex entropy is concave on the nonnegative simplex. -/
theorem simplexEntropy_concave (s : Finset ι) :
    ConcaveOn ℝ {b | SimplexOn s b} (simplexEntropy s) := by
  have hComb (b p : ι → ℝ) (a t : ℝ) (h : a+t=1) :
      a • b + t • p = simplexSegment b p t := by
    funext i
    change a*b i + t*p i = b i+t*(p i-b i)
    have he : a = 1-t := by linarith only [h]
    rw [he]
    ring
  refine ⟨?_, ?_⟩
  · intro b hb p hp a t ha ht h
    rw [hComb b p a t h]
    exact simplexSegment_mem hb hp ⟨ht, by linarith only [ha, h]⟩
  · intro b hb p hp a t ha ht h
    have hC := simplexEntropy_segment_concave hb hp
    have hc := hC.2 (show 0 ∈ Icc (0 : ℝ) 1 by norm_num)
      (show 1 ∈ Icc (0 : ℝ) 1 by norm_num) ha ht h
    have h0 : simplexSegment b p 0 = b := by funext i; simp [simplexSegment]
    have h1 : simplexSegment b p 1 = p := by funext i; simp [simplexSegment]
    rw [hComb b p a t h]
    simpa only [smul_eq_mul, mul_zero, mul_one, zero_add, h0, h1] using hc

private theorem simplexSegment_strict_of_left {s : Finset ι} {b p : ι → ℝ}
    (hp : SimplexOn s p) (hb : ∀ i ∈ s, b i ∈ Ioo (0 : ℝ) 1)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    ∀ i ∈ s, simplexSegment b p t i ∈ Ioo (0 : ℝ) 1 := by
  intro i hi
  have h₁ : 0 < 1-t := sub_pos.mpr ht.2
  have h₂ : 0 ≤ 1-p i := sub_nonneg.mpr (hp.le_one hi)
  have h₃ : simplexSegment b p t i = (1-t)*b i+t*p i := by unfold simplexSegment; ring
  have h₄ : 1-simplexSegment b p t i = (1-t)*(1-b i)+t*(1-p i) := by
    unfold simplexSegment
    ring
  constructor
  · rw [h₃]
    exact add_pos_of_pos_of_nonneg (mul_pos h₁ (hb i hi).1) (mul_nonneg ht.1 (hp.1 i hi))
  · apply sub_pos.mp
    rw [h₄]
    exact add_pos_of_pos_of_nonneg (mul_pos h₁ (sub_pos.mpr (hb i hi).2)) (mul_nonneg ht.1 h₂)

/-- A closed-simplex vector lies below the tangent plane at an
interior vector. -/
theorem simplexEntropy_tangent {s : Finset ι} {b p : ι → ℝ}
    (hb : SimplexOn s b) (hp : SimplexOn s p)
    (hstrict : ∀ i ∈ s, b i ∈ Ioo (0 : ℝ) 1) :
    simplexEntropy s p ≤ simplexEntropy s b + simplexTangent s b p := by
  have hC := simplexEntropy_segment_concave hb hp
  have hs := hC.slope_le_of_hasDerivAt
    (show 0 ∈ Icc (0 : ℝ) 1 by norm_num)
    (show 1 ∈ Icc (0 : ℝ) 1 by norm_num) zero_lt_one
    (hasDerivAt_simplexEntropy_curve (simplexSegment_strict_of_left hp hstrict
      (show 0 ∈ Ico (0 : ℝ) 1 by norm_num)))
  have h0 : simplexSegment b p 0 = b := by funext i; simp [simplexSegment]
  have h1 : simplexSegment b p 1 = p := by funext i; simp [simplexSegment]
  simp only [slope_def_field, h0, h1, sub_zero, div_one] at hs
  unfold simplexTangent
  linarith only [hs]

/-- The quantitative tangent loss used in the overlap estimate, before
the factor of one half in the graph entropy decomposition. -/
theorem simplexEntropy_tangent_loss {s : Finset ι} {b p : ι → ℝ} {η : ℝ}
    (hb : SimplexOn s b) (hp : SimplexOn s p)
    (hstrict : ∀ i ∈ s, b i ∈ Ioo (0 : ℝ) 1) (hη : 0 ≤ η) (hlarge : ThreeLargeOn s b η) :
    simplexEntropy s p ≤ simplexEntropy s b + simplexTangent s b p -
      (η/32) * (∑ i ∈ s, |p i-b i|)^2 := by
  let f (t : ℝ) := simplexEntropy s (simplexSegment b p t)
  let df := entropySlopeCurve s b p
  let K := (η/8) * (∑ i ∈ s, |p i-b i|)^2
  let g (t : ℝ) := f t + (K/2)*t^2
  have hInt (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (1/2)) :=
    simplexSegment_strict_of_left hp hstrict (show t ∈ Ico (0 : ℝ) 1 from
      ⟨ht.1, lt_of_le_of_lt ht.2 (by norm_num)⟩)
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (1/2)) : HasDerivAt f (df t) t :=
    hasDerivAt_simplexEntropy_curve (hInt t ht)
  have hdd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (1/2)) :
      HasDerivAt df (-entropyCurvatureCurve s b p t) t :=
    hasDerivAt_simplexSlope_curve (hInt t ht)
  have hgD (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (1/2)) : HasDerivAt g (df t + K*t) t := by
    exact ((hd t ht).fun_add ((hasDerivAt_pow 2 t).const_mul (K/2))).congr_deriv (by ring)
  have hgDD (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (1/2)) :
      HasDerivAt (fun u => df u + K*u) (-entropyCurvatureCurve s b p t + K) t := by
    simpa only [id_eq, mul_one] using (hdd t ht).fun_add ((hasDerivAt_id t).const_mul K)
  have hQ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (1/2)) : K ≤ entropyCurvatureCurve s b p t := by
    have hlarge' : ThreeLargeOn s (simplexSegment b p t) (η/2) := by
      have hcoord (i : ι) (hi : i ∈ s) (hbi : η ≤ b i) :
          η/2 ≤ simplexSegment b p t i := by
        have h := mul_le_mul_of_nonneg_left hbi (show 0 ≤ 1-t by linarith [ht.2])
        have hn := mul_nonneg ht.1 (hp.1 i hi)
        have ha := mul_le_mul_of_nonneg_right (show (1/2 : ℝ) ≤ 1-t by linarith [ht.2]) hη
        unfold simplexSegment
        linarith only [h, hn, ha]
      obtain ⟨i, hi, j, hj, k, hk, hij, hik, hjk, hbi, hbj, hbk⟩ := hlarge
      exact ⟨i, hi, j, hj, k, hk, hij, hik, hjk, hcoord i hi hbi, hcoord j hj hbj, hcoord k hk hbk⟩
    have h := simplex_hessian_ge_l1
      (simplexSegment_mem hb hp (show t ∈ Icc (0 : ℝ) 1 from ⟨ht.1, ht.2.trans (by norm_num)⟩))
      (hInt t ht) (v := fun i => p i-b i)
      (by simp only [Finset.sum_sub_distrib, hp.2, hb.2, sub_self])
      (div_nonneg hη (by norm_num : (0 : ℝ) ≤ 2)) hlarge'
    unfold K
    simpa only [entropyCurvatureCurve, show η / 2 / 4 = η / 8 by ring] using h
  have hC : ConcaveOn ℝ (Icc (0 : ℝ) (1/2)) g := by
    have hCont : Continuous g := by
      unfold g f
      exact (continuous_simplexEntropy_curve s b p).add (by fun_prop)
    apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _) hCont.continuousOn
      (f' := fun t => df t+K*t) (f'' := fun t => -entropyCurvatureCurve s b p t + K)
    · exact fun t ht => (hgD t (interior_subset ht)).hasDerivWithinAt
    · exact fun t ht => (hgDD t (interior_subset ht)).hasDerivWithinAt
    · intro t ht
      linarith only [hQ t (interior_subset ht)]
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) (1/2) := by norm_num
  have hhalf : (1/2 : ℝ) ∈ Icc (0 : ℝ) (1/2) := by norm_num
  have hLeft := hC.slope_le_of_hasDerivAt h0 hhalf (by norm_num) (hgD 0 h0)
  have hSlope := hC.antitoneOn_deriv (fun t ht => (hgD t ht).differentiableAt)
    h0 hhalf (by norm_num)
  rw [(hgD 0 h0).deriv, (hgD (1/2) hhalf).deriv] at hSlope
  have hRight := (simplexEntropy_segment_concave hb hp).slope_le_of_hasDerivAt
    (show (1/2 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num) (by norm_num) (hd (1/2) hhalf)
  have hRight' : (f 1 - f (1/2)) / (1-1/2) ≤ df (1/2) := by simpa only [slope_def_field] using hRight
  simp only [slope_def_field, g, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero,
    add_zero, sub_zero] at hLeft
  have hResult : f 1 ≤ f 0 + df 0 - 3*K/8 := by
    have hLeft' := (div_le_iff₀ (by norm_num : (0 : ℝ) < 1/2)).mp hLeft
    have hRight'' := (div_le_iff₀ (by norm_num : (0 : ℝ) < 1-1/2)).mp hRight'
    norm_num at hLeft' hRight''
    linarith only [hLeft', hSlope, hRight'']
  have he0 : simplexSegment b p 0 = b := by funext i; simp [simplexSegment]
  have he1 : simplexSegment b p 1 = p := by funext i; simp [simplexSegment]
  have hF0 : f 0 = simplexEntropy s b := by simp only [f, he0]
  have hF1 : f 1 = simplexEntropy s p := by simp only [f, he1]
  have hDf0 : df 0 = simplexTangent s b p := by simp [df, entropySlopeCurve, simplexTangent, simplexSegment]
  rw [hF0, hF1, hDf0] at hResult
  have hK : 0 ≤ K := mul_nonneg (div_nonneg hη (by norm_num)) (sq_nonneg _)
  have hK32 : (η/32) * (∑ i ∈ s, |p i-b i|)^2 = K/4 := by unfold K; ring
  rw [hK32]
  linarith only [hResult, hK]

/-- The binary entropy of the unmatched mass. -/
noncomputable def binaryEntropy (x : ℝ) : ℝ := Real.negMulLog x + Real.negMulLog (1-x)

/-- Derivative of the binary entropy on the open unit interval. -/
noncomputable def binaryEntropySlope (x : ℝ) : ℝ := Real.log (1-x) - Real.log x

private theorem negMulLog_tangent {b p : ℝ} (hb : 0 < b) (hp : 0 ≤ p) :
    Real.negMulLog p ≤ Real.negMulLog b + (-Real.log b-1)*(p-b) := by
  rcases lt_trichotomy b p with h | h | h
  · have hs := Real.concaveOn_negMulLog.slope_le_of_hasDerivAt hb.le hp h
      (Real.hasDerivAt_negMulLog hb.ne')
    rw [slope_def_field, div_le_iff₀ (sub_pos.mpr h)] at hs
    linarith only [hs]
  · rw [h, sub_self, mul_zero, add_zero]
  · have hs := Real.concaveOn_negMulLog.le_slope_of_hasDerivAt hp hb.le h
      (Real.hasDerivAt_negMulLog hb.ne')
    rw [slope_def_field, le_div_iff₀ (sub_pos.mpr h)] at hs
    nlinarith only [hs]

theorem binaryEntropy_tangent {b p : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1) (hp : p ∈ Icc (0 : ℝ) 1) :
    binaryEntropy p ≤ binaryEntropy b + binaryEntropySlope b * (p-b) := by
  have h₁ := negMulLog_tangent hb.1 hp.1
  have h₂ := negMulLog_tangent (sub_pos.mpr hb.2) (sub_nonneg.mpr hp.2)
  unfold binaryEntropy binaryEntropySlope
  nlinarith only [h₁, h₂]

end Certificate.Overlap

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# The probability-vector inequality

The logarithmic comparison in the appendix to *Free energy of bipartite random
assignment*. The proof integrates the same quadratic form along the segment of
probability vectors. Completing the square replaces weighted Cauchy–Schwarz
and isolates a summable correction of total zero.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Certificate

variable {ι : Type*}

/-- The summand in the manuscript's simplex comparison. -/
noncomputable def simplexTerm (a b : ι → ℝ) (i : ι) : ℝ :=
  (a i - b i) * Real.log (a i * (1 - a i) / (b i * (1 - b i)))

private theorem pair_lt_one
    (three : ∀ i j : ι, ∃ k, k ≠ i ∧ k ≠ j)
    {q : ι → ℝ} (hq : HasSum q 1) (qp : ∀ i, 0 < q i)
    {i j : ι} (hij : i ≠ j) : q i + q j < 1 := by
  classical
  obtain ⟨k, hki, hkj⟩ := three i j
  have hs := hq.summable.sum_le_tsum ({i, j, k} : Finset ι) (fun t _ => (qp t).le)
  rw [hq.tsum_eq] at hs
  simp [Finset.sum_insert, hij, hki.symm, hkj.symm] at hs
  linarith [qp k]

private theorem coordinate_lt_one
    (three : ∀ i j : ι, ∃ k, k ≠ i ∧ k ≠ j)
    {q : ι → ℝ} (hq : HasSum q 1) (qp : ∀ i, 0 < q i) (i : ι) : q i < 1 := by
  obtain ⟨j, hji, _⟩ := three i i
  linarith [pair_lt_one three hq qp hji.symm, qp j]

private theorem nonzero_outside {v : ι → ℝ} (hv : HasSum v 0)
    (hne : v ≠ 0) (j : ι) : ∃ i, i ≠ j ∧ v i ≠ 0 := by
  classical
  by_contra hn
  push Not at hn
  have hsingle : HasSum (fun i : ι => if i = j then v j else 0) (v j) := hasSum_ite_eq j (v j)
  have heq : (fun i : ι => if i = j then v j else 0) = v := by
    funext i
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, hn i hij]
  rw [heq] at hsingle
  have h0 : v j = 0 := hsingle.unique hv
  apply hne
  funext i
  rw [← heq]
  simp [h0]

private noncomputable def curvature (q : ℝ) : ℝ :=
  (1 - 2*q) / (q * (1-q))

private noncomputable def heavyCoefficient (q : ℝ) : ℝ :=
  max 0 ((2*q - 1) / q)

private noncomputable def tilt (q v : ℝ) : ℝ :=
  -v / (1-q)

private noncomputable def linearCoefficient (q v : ℝ) : ℝ :=
  2 * heavyCoefficient q * tilt q v

private noncomputable def massCoefficient (q v : ℝ) : ℝ :=
  -(heavyCoefficient q * tilt q v ^ 2)

private noncomputable def correction [DecidableEq ι] (q v : ι → ℝ)
    (j i : ι) : ℝ :=
  linearCoefficient (q j) (v j) * v i +
  massCoefficient (q j) (v j) * (q i - if i = j then 1 else 0)

private theorem correction_eq_zero [DecidableEq ι] {q v : ι → ℝ} {j : ι}
    (hq : 0 < q j) (hsmall : q j ≤ 1/2) (i : ι) :
    correction q v j i = 0 := by
  have hc : heavyCoefficient (q j) = 0 :=
    max_eq_left (div_nonpos_of_nonpos_of_nonneg (by linarith) hq.le)
  simp [correction, linearCoefficient, massCoefficient, hc]

private theorem correction_self [DecidableEq ι] {q v : ι → ℝ} {j : ι}
    (hq : q j < 1) (hl : 1/2 < q j) :
    correction q v j j = curvature (q j) * v j ^ 2 := by
  have hqp : 0 < q j := by linarith
  have hc : 0 ≤ (2*q j - 1) / q j := div_nonneg (by linarith) hqp.le
  simp only [correction, linearCoefficient, massCoefficient, heavyCoefficient,
    max_eq_right hc, tilt, if_true, curvature, eq_self]
  field_simp [hqp.ne', (sub_pos.mpr hq).ne']
  ring

private theorem correction_other [DecidableEq ι] {q v : ι → ℝ} {i j : ι}
    (hij : i ≠ j) (hp : 0 < q i) (hl : 1/2 < q j) (hs : q i + q j < 1) :
    correction q v j i ≤ curvature (q i) * v i ^ 2 ∧
      (v i ≠ 0 → correction q v j i < curvature (q i) * v i ^ 2) := by
  have hqp : 0 < q j := by linarith
  have hi₁ : 0 < 1 - q i := by linarith
  have hj₁ : 0 < 1 - q j := by linarith
  let c := (2*q j - 1) / q j
  let t := tilt (q j) (v j)
  have hc : 0 ≤ c := div_nonneg (by linarith) hqp.le
  have hbase : correction q v j i = 2*c*t*v i - c*t^2*q i := by
    simp only [correction, linearCoefficient, massCoefficient, heavyCoefficient,
      if_neg hij, sub_zero]
    change 2 * max 0 c * t * v i + -(max 0 c * t^2) * q i = _
    rw [max_eq_right hc]
    ring
  have hscale : 0 < curvature (q i) - c / q i := by
    have hid : curvature (q i) - c / q i =
        (1 - q i - q j) / (q i * (1 - q i) * q j) := by
      dsimp [curvature, c]
      field_simp
      ring
    rw [hid]
    exact div_pos (by linarith) (mul_pos (mul_pos hp hi₁) hqp)
  have hsq : 0 ≤ c / q i * (v i - t*q i)^2 :=
    mul_nonneg (div_nonneg hc hp.le) (sq_nonneg _)
  have hid : curvature (q i) * v i^2 - correction q v j i =
      (curvature (q i) - c / q i) * v i^2 + c / q i * (v i - t*q i)^2 := by
    rw [hbase]
    field_simp
    ring
  constructor
  · apply sub_nonneg.mp
    rw [hid]
    exact add_nonneg (mul_nonneg hscale.le (sq_nonneg _)) hsq
  · intro hvi
    apply sub_pos.mp
    rw [hid]
    exact add_pos_of_pos_of_nonneg (mul_pos hscale (sq_pos_of_ne_zero hvi)) hsq

private theorem one_heavy
    (three : ∀ i j : ι, ∃ k, k ≠ i ∧ k ≠ j)
    {q : ι → ℝ} (hq : HasSum q 1) (qp : ∀ i, 0 < q i)
    {i j : ι} (hj : 1/2 < q j) (hij : i ≠ j) : q i ≤ 1/2 := by
  linarith [pair_lt_one three hq qp hij]

private theorem quadratic_comparison [DecidableEq ι]
    (three : ∀ i j : ι, ∃ k, k ≠ i ∧ k ≠ j)
    {q v : ι → ℝ} (hq : HasSum q 1) (qp : ∀ i, 0 < q i) (hv : HasSum v 0)
    (exceptional : Finset ι) (hE : ∀ j, 1/2 < q j → j ∈ exceptional) :
    (∀ i, (∑ j ∈ exceptional, correction q v j i) ≤ curvature (q i) * v i ^ 2) ∧
    (v ≠ 0 → ∃ i, (∑ j ∈ exceptional, correction q v j i) < curvature (q i) * v i ^ 2) := by
  by_cases hbig : ∃ j, 1/2 < q j
  · obtain ⟨j, hj⟩ := hbig
    have hsum (i : ι) : (∑ k ∈ exceptional, correction q v k i) = correction q v j i := by
      apply Finset.sum_eq_single_of_mem j (hE j hj)
      intro k _ hkj
      exact correction_eq_zero (qp k) (one_heavy three hq qp hj hkj) i
    have hother (i : ι) (hij : i ≠ j) := correction_other (v := v)
      hij (qp i) hj (pair_lt_one three hq qp hij)
    constructor
    · intro i
      rw [hsum]
      by_cases hij : i = j
      · subst i
        exact (correction_self (coordinate_lt_one three hq qp j) hj).le
      · exact (hother i hij).1
    · intro hne
      obtain ⟨i, hij, hvi⟩ := nonzero_outside hv hne j
      exact ⟨i, by rw [hsum]; exact (hother i hij).2 hvi⟩
  · push Not at hbig
    have hsum (i : ι) : (∑ j ∈ exceptional, correction q v j i) = 0 :=
      Finset.sum_eq_zero fun j _ => correction_eq_zero (qp j) (hbig j) i
    have hden (i : ι) : 0 < q i * (1-q i) :=
      mul_pos (qp i) (sub_pos.mpr (coordinate_lt_one three hq qp i))
    constructor
    · intro i
      rw [hsum]
      exact mul_nonneg (div_nonneg (by linarith [hbig i]) (hden i).le) (sq_nonneg _)
    · intro hne
      have hex : ∃ i, v i ≠ 0 := by
        by_contra hn
        push Not at hn
        exact hne (funext hn)
      obtain ⟨j, hvj⟩ := hex
      have hsmall : ∃ i, q i < 1/2 ∧ v i ≠ 0 := by
        by_cases hj : q j < 1/2
        · exact ⟨j, hj, hvj⟩
        · obtain ⟨i, hij, hvi⟩ := nonzero_outside hv hne j
          exact ⟨i, by linarith [pair_lt_one three hq qp hij], hvi⟩
      obtain ⟨i, hi, hvi⟩ := hsmall
      refine ⟨i, ?_⟩
      rw [hsum]
      exact mul_pos (div_pos (by linarith) (hden i)) (sq_pos_of_ne_zero hvi)

private noncomputable def segment (a b : ι → ℝ) (s : ℝ) (i : ι) : ℝ :=
  (1-s) * b i + s * a i

private theorem segment_hasSum {a b : ι → ℝ} (ha : HasSum a 1) (hb : HasSum b 1)
    (s : ℝ) : HasSum (segment a b s) 1 := by
  have h : (1-s)*1+s*1 = 1 := by ring
  rw [← h]
  exact (hb.mul_left (1-s)).add (ha.mul_left s)

private theorem segment_pos {a b : ι → ℝ} (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (i : ι) : 0 < segment a b s i := by
  by_cases h : s = 0
  · simpa [h, segment] using hb i
  · exact add_pos_of_nonneg_of_pos (mul_nonneg (by linarith [hs.2]) (hb i).le)
      (mul_pos (lt_of_le_of_ne hs.1 (Ne.symm h)) (ha i))

private theorem segment_continuous (a b : ι → ℝ) (i : ι) :
    Continuous (fun s => segment a b s i) := by
  unfold segment
  fun_prop

private theorem segCorrection_coeff_continuous
    (three : ∀ i j : ι, ∃ k, k ≠ i ∧ k ≠ j)
    {a b : ι → ℝ} (ha : HasSum a 1) (hb : HasSum b 1)
    (ap : ∀ i, 0 < a i) (bp : ∀ i, 0 < b i) (j : ι) :
    ContinuousOn (fun s => linearCoefficient (segment a b s j) (a j - b j))
      (Icc (0 : ℝ) 1) ∧
    ContinuousOn (fun s => massCoefficient (segment a b s j) (a j - b j))
      (Icc (0 : ℝ) 1) := by
  have Q := (segment_continuous a b j).continuousOn (s := Icc (0 : ℝ) 1)
  have hpos s hs := segment_pos ap bp (s := s) hs j
  have hlt s hs := coordinate_lt_one three (segment_hasSum ha hb s)
    (segment_pos ap bp (s := s) hs) j
  have K : ContinuousOn (fun s => heavyCoefficient (segment a b s j)) (Icc (0 : ℝ) 1) :=
    continuousOn_const.sup' (((continuousOn_const.mul Q).sub continuousOn_const).div Q
      (fun s hs => (hpos s hs).ne'))
  have T : ContinuousOn (fun s => tilt (segment a b s j) (a j - b j)) (Icc (0 : ℝ) 1) :=
    continuousOn_const.div (continuousOn_const.sub Q)
      (fun s hs => (sub_pos.mpr (hlt s hs)).ne')
  exact ⟨(continuousOn_const.mul K).mul T, (K.mul (T.pow 2)).neg⟩

private theorem correction_integral_hasSum [DecidableEq ι]
    {a b : ι → ℝ} (ha : HasSum a 1) (hb : HasSum b 1) (j : ι)
    (A B : ℝ → ℝ) (hcA : ContinuousOn A (Icc 0 1)) (hcB : ContinuousOn B (Icc 0 1)) :
    HasSum (fun i => ∫ s in (0 : ℝ)..1,
      A s * (a i - b i) + B s * (segment a b s i - if i = j then 1 else 0)) 0 := by
  let B₀ : ℝ → ℝ := fun s => B s * (1-s)
  let B₁ : ℝ → ℝ := fun s => B s * s
  have intA := hcA.intervalIntegrable_of_Icc (μ := volume)
    (a := (0:ℝ)) (b := 1) zero_le_one
  have intB := hcB.intervalIntegrable_of_Icc (μ := volume)
    (a := (0:ℝ)) (b := 1) zero_le_one
  have intB₀ : IntervalIntegrable B₀ volume 0 1 :=
    (hcB.mul (continuousOn_const.sub continuous_id.continuousOn)).intervalIntegrable_of_Icc
      zero_le_one
  have intB₁ : IntervalIntegrable B₁ volume 0 1 :=
    (hcB.mul continuous_id.continuousOn).intervalIntegrable_of_Icc zero_le_one
  have hBc : (∫ s in (0:ℝ)..1, B₀ s) + (∫ s in (0:ℝ)..1, B₁ s) =
      ∫ s in (0:ℝ)..1, B s := by
    rw [← intervalIntegral.integral_add intB₀ intB₁]
    congr 1
    funext s
    dsimp [B₀, B₁]
    ring
  have hformula (i : ι) : (∫ s in (0:ℝ)..1,
      A s * (a i - b i) + B s * (segment a b s i - if i = j then 1 else 0)) =
      (∫ s in (0:ℝ)..1, A s) * (a i - b i) +
      ((∫ s in (0:ℝ)..1, B₀ s) * b i + (∫ s in (0:ℝ)..1, B₁ s) * a i -
        (∫ s in (0:ℝ)..1, B s) * (if i = j then 1 else 0)) := by
    have hpoint (s : ℝ) :
        A s * (a i - b i) + B s * (segment a b s i - if i = j then 1 else 0) =
        A s * (a i - b i) +
          (B₀ s * b i + B₁ s * a i - B s * (if i = j then 1 else 0)) := by
      dsimp [segment, B₀, B₁]
      ring
    simp_rw [hpoint]
    rw [intervalIntegral.integral_add (intA.mul_const _)
      (((intB₀.mul_const _).add (intB₁.mul_const _)).sub (intB.mul_const _)),
      intervalIntegral.integral_sub ((intB₀.mul_const _).add (intB₁.mul_const _))
      (intB.mul_const _), intervalIntegral.integral_add (intB₀.mul_const _) (intB₁.mul_const _)]
    simp only [intervalIntegral.integral_mul_const]
  let cA := ∫ s in (0:ℝ)..1, A s
  let cB := ∫ s in (0:ℝ)..1, B s
  let c₀ := ∫ s in (0:ℝ)..1, B₀ s
  let c₁ := ∫ s in (0:ℝ)..1, B₁ s
  have hsingle : HasSum (fun i : ι => if i = j then (1:ℝ) else 0) 1 := hasSum_ite_eq j 1
  have h := ((ha.sub hb).mul_left cA).add
    (((hb.mul_left c₀).add (ha.mul_left c₁)).sub (hsingle.mul_left cB))
  simp only [sub_self, mul_zero, mul_one, zero_add] at h
  change c₀ + c₁ = cB at hBc
  rw [hBc, sub_self] at h
  have heq : (fun i => ∫ s in (0:ℝ)..1,
      A s * (a i - b i) + B s * (segment a b s i - if i = j then 1 else 0)) =
      (fun i => cA * (a i - b i) + (c₀ * b i + c₁ * a i - cB * (if i = j then 1 else 0))) :=
    funext hformula
  rw [heq]
  exact h

private theorem integral_curvature
    (three : ∀ i j : ι, ∃ k, k ≠ i ∧ k ≠ j)
    {a b : ι → ℝ} (ha : HasSum a 1) (hb : HasSum b 1)
    (ap : ∀ i, 0 < a i) (bp : ∀ i, 0 < b i) (i : ι) :
    ContinuousOn (fun s => curvature (segment a b s i) * (a i - b i)^2) (Icc 0 1) ∧
    (∫ s in (0:ℝ)..1, curvature (segment a b s i) * (a i - b i)^2) =
      simplexTerm a b i := by
  let v := a i - b i
  let q := fun s => segment a b s i
  have qpos s hs : 0 < q s := segment_pos ap bp (s := s) hs i
  have qlt s hs : q s < 1 :=
    coordinate_lt_one three (segment_hasSum ha hb s) (segment_pos ap bp (s := s) hs) i
  have qprod s hs : 0 < q s * (1 - q s) := mul_pos (qpos s hs) (sub_pos.mpr (qlt s hs))
  have hQ : ContinuousOn q (Icc (0:ℝ) 1) := (segment_continuous a b i).continuousOn
  have hnum : ContinuousOn (fun s => 1 - 2*q s) (Icc 0 1) :=
    continuousOn_const.sub (continuousOn_const.mul hQ)
  have hden : ContinuousOn (fun s => q s * (1-q s)) (Icc 0 1) :=
    hQ.mul (continuousOn_const.sub hQ)
  have hc : ContinuousOn (fun s => curvature (q s) * v^2) (Icc 0 1) :=
    (hnum.div hden (fun s hs => (qprod s hs).ne')).mul continuousOn_const
  refine ⟨hc, ?_⟩
  have hdiff (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      HasDerivAt (fun t => v * Real.log (q t * (1-q t))) (curvature (q s) * v^2) s := by
    have qd : HasDerivAt q v s := by
      have hv : (-1 : ℝ) * b i + 1 * a i = v := by
        dsimp [v]
        ring
      rw [← hv]
      exact (((hasDerivAt_id s).const_sub 1).mul_const (b i)).add
        ((hasDerivAt_id s).mul_const (a i))
    have hcoef : v * ((v * (1-q s) + q s * (-v)) / (q s * (1-q s))) =
        curvature (q s) * v^2 := by
      unfold curvature
      field_simp [(qpos s hs).ne', (sub_pos.mpr (qlt s hs)).ne']
      ring
    rw [← hcoef]
    exact ((qd.fun_mul (qd.const_sub 1)).log (qprod s hs).ne').const_mul v
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (by simpa only [uIcc_of_le (show (0:ℝ) ≤ 1 by norm_num)] using hdiff)
    (hc.intervalIntegrable_of_Icc (μ := volume) zero_le_one)
  have ha1 : a i < 1 := coordinate_lt_one three ha ap i
  have hb1 : b i < 1 := coordinate_lt_one three hb bp i
  rw [h]
  simp only [simplexTerm, q, segment, sub_self, zero_mul, one_mul, zero_add, sub_zero, add_zero]
  rw [Real.log_div (mul_pos (ap i) (sub_pos.mpr ha1)).ne'
    (mul_pos (bp i) (sub_pos.mpr hb1)).ne']
  ring

/-- The logarithmic comparison dominates a summable correction of total zero, and
strictly dominates it in at least one coordinate when the vectors differ.

This form works for countably many coordinates even when the positive contribution
to the logarithmic comparison has infinite sum. -/
theorem simplex_term_comparison
    (three : ∀ i j : ι, ∃ k, k ≠ i ∧ k ≠ j)
    {a b : ι → ℝ} (ha : HasSum a 1) (hb : HasSum b 1)
    (ap : ∀ i, 0 < a i) (bp : ∀ i, 0 < b i) :
    ∃ c : ι → ℝ, HasSum c 0 ∧ (∀ i, c i ≤ simplexTerm a b i) ∧
      (a ≠ b → ∃ i, c i < simplexTerm a b i) := by
  classical
  have hfin {q : ι → ℝ} (hq : HasSum q 1) (qp : ∀ i, 0 < q i) :
      {j | 1/2 < q j}.Finite := by
    apply Set.Subsingleton.finite
    intro j hj k hk
    by_contra hjk
    have h := pair_lt_one three hq qp hjk
    change 1/2 < q j at hj
    change 1/2 < q k at hk
    linarith
  let E := (hfin ha ap).toFinset ∪ (hfin hb bp).toFinset
  let v := fun i => a i - b i
  have hv : HasSum v 0 := by simpa [v] using ha.sub hb
  have HE (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) (j : ι)
      (hj : 1/2 < segment a b s j) : j ∈ E := by
    simp only [E, Finset.mem_union, Set.Finite.mem_toFinset, mem_ofPred_eq]
    by_contra H
    push Not at H
    have h₀ : 0 ≤ 1-s := sub_nonneg.mpr hs.2
    have h₁ := mul_le_mul_of_nonneg_left H.1 hs.1
    have h₂ := mul_le_mul_of_nonneg_left H.2 h₀
    dsimp [segment] at hj
    linarith
  have Hcomp (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :=
    quadratic_comparison three (segment_hasSum ha hb s) (segment_pos ap bp hs) hv E (HE s hs)
  have hcoeff j := segCorrection_coeff_continuous three ha hb ap bp j
  have hcorr j i : ContinuousOn (fun s => correction (segment a b s) v j i) (Icc 0 1) :=
    ((hcoeff j).1.mul continuousOn_const).add
      ((hcoeff j).2.mul ((segment_continuous a b i).continuousOn.sub continuousOn_const))
  let corr := fun s i => ∑ j ∈ E, correction (segment a b s) v j i
  have hcorrSum (i : ι) : ContinuousOn (fun s => corr s i) (Icc 0 1) :=
    continuousOn_finsetSum _ (fun j _ => hcorr j i)
  let c := fun i => ∫ s in (0:ℝ)..1, corr s i
  have hci (i : ι) : c i = ∑ j ∈ E, ∫ s in (0:ℝ)..1, correction (segment a b s) v j i :=
    intervalIntegral.integral_finsetSum (fun j _ => (hcorr j i).intervalIntegrable_of_Icc zero_le_one)
  have hsum (j : ι) : HasSum (fun i => ∫ s in (0:ℝ)..1, correction (segment a b s) v j i) 0 :=
    correction_integral_hasSum ha hb j _ _ (hcoeff j).1 (hcoeff j).2
  have hcsum : HasSum c 0 := by
    have H := hasSum_sum (s := E) (fun j _ => hsum j)
    simp only [Finset.sum_const_zero] at H
    convert H using 1
    funext i
    exact hci i
  let r := fun s i => curvature (segment a b s i) * v i ^ 2 - corr s i
  have hr (i : ι) : ContinuousOn (fun s => r s i) (Icc 0 1) :=
    (integral_curvature three ha hb ap bp i).1.sub (hcorrSum i)
  have hR (i : ι) : (∫ s in (0:ℝ)..1, r s i) = simplexTerm a b i - c i := by
    rw [show (fun s => r s i) =
      (fun s => curvature (segment a b s i) * v i ^ 2 - corr s i) from rfl]
    rw [intervalIntegral.integral_sub
      ((integral_curvature three ha hb ap bp i).1.intervalIntegrable_of_Icc zero_le_one)
      ((hcorrSum i).intervalIntegrable_of_Icc zero_le_one),
      (integral_curvature three ha hb ap bp i).2]
  have hpos (i : ι) (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : 0 ≤ r s i :=
    sub_nonneg.mpr ((Hcomp s hs).1 i)
  refine ⟨c, hcsum, ?_, ?_⟩
  · intro i
    apply sub_nonneg.mp
    rw [← hR]
    exact intervalIntegral.integral_nonneg zero_le_one (hpos i)
  · intro hn
    have hvn : v ≠ 0 := fun H => hn (funext (fun i =>
      sub_eq_zero.mp (congrFun H i)))
    have hs : (1/2 : ℝ) ∈ Icc 0 1 := by constructor <;> norm_num
    obtain ⟨i, hi⟩ := (Hcomp (1/2) hs).2 hvn
    refine ⟨i, sub_pos.mp ?_⟩
    rw [← hR]
    exact intervalIntegral.integral_pos zero_lt_one (hr i)
      (fun s ht => hpos i s (Ioc_subset_Icc_self ht)) ⟨1/2, hs, sub_pos.mpr hi⟩

/-- For a real-summable logarithmic comparison (in particular for finitely many
coordinates), the sum is nonnegative. -/
theorem simplex_divergence_nonneg
    (three : ∀ i j : ι, ∃ k, k ≠ i ∧ k ≠ j)
    {a b : ι → ℝ} (ha : HasSum a 1) (hb : HasSum b 1)
    (ap : ∀ i, 0 < a i) (bp : ∀ i, 0 < b i)
    (hs : Summable (simplexTerm a b)) : 0 ≤ ∑' i, simplexTerm a b i := by
  obtain ⟨c, hc, hle, _⟩ := simplex_term_comparison three ha hb ap bp
  rw [← hc.tsum_eq]
  exact hc.summable.tsum_le_tsum hle hs

/-- Strict positivity for distinct vectors when the divergence is real-summable. -/
theorem simplex_divergence_pos
    (three : ∀ i j : ι, ∃ k, k ≠ i ∧ k ≠ j)
    {a b : ι → ℝ} (ha : HasSum a 1) (hb : HasSum b 1)
    (ap : ∀ i, 0 < a i) (bp : ∀ i, 0 < b i)
    (hs : Summable (simplexTerm a b)) (hne : a ≠ b) :
    0 < ∑' i, simplexTerm a b i := by
  obtain ⟨c, hc, hle, hlt⟩ := simplex_term_comparison three ha hb ap bp
  obtain ⟨i, hi⟩ := hlt hne
  rw [← hc.tsum_eq]
  exact Summable.tsum_lt_tsum hle hi hc.summable hs

/-- The positive part of the comparison minus its negative part as a nonnegative
extended real. The theorem below proves that the negative part is finite and that
the subtraction represents the signed comparison. -/
noncomputable def simplexExtendedDivergence (a b : ι → ℝ) : ℝ≥0∞ :=
  (∑' i, ENNReal.ofReal (simplexTerm a b i)) -
    ∑' i, ENNReal.ofReal (-simplexTerm a b i)

private theorem ofReal_parts_balance {x y : ℝ} (h : x ≤ y) :
    ENNReal.ofReal y + ENNReal.ofReal (-x) =
      ENNReal.ofReal (-y) + ENNReal.ofReal x + ENNReal.ofReal (y-x) := by
  by_cases hx : 0 ≤ x
  · have hy := hx.trans h
    simp only [ENNReal.ofReal_of_nonpos (neg_nonpos.mpr hx),
      ENNReal.ofReal_of_nonpos (neg_nonpos.mpr hy), add_zero, zero_add]
    rw [← ENNReal.ofReal_add hx (sub_nonneg.mpr h)]
    congr 1
    ring
  · have hxn : x ≤ 0 := le_of_not_ge hx
    by_cases hy : 0 ≤ y
    · simp only [ENNReal.ofReal_of_nonpos hxn, ENNReal.ofReal_of_nonpos (neg_nonpos.mpr hy),
        add_zero, zero_add, sub_eq_add_neg]
      exact (ENNReal.ofReal_add hy (neg_nonneg.mpr hxn)).symm
    · have hyn : y ≤ 0 := le_of_not_ge hy
      simp only [ENNReal.ofReal_of_nonpos hxn, ENNReal.ofReal_of_nonpos hyn,
        add_zero, zero_add]
      rw [← ENNReal.ofReal_add (neg_nonneg.mpr hyn) (sub_nonneg.mpr h)]
      congr 1
      ring

/-- The appendix inequality, including the countable case and its equality
criterion. The negative part is finite, is dominated by the positive part,
and the extended divergence vanishes exactly when the vectors agree. -/
theorem simplex_extended_divergence
    (three : ∀ i j : ι, ∃ k, k ≠ i ∧ k ≠ j)
    {a b : ι → ℝ} (ha : HasSum a 1) (hb : HasSum b 1)
    (ap : ∀ i, 0 < a i) (bp : ∀ i, 0 < b i) :
    (∑' i, ENNReal.ofReal (-simplexTerm a b i)) ≠ ∞ ∧
    (∑' i, ENNReal.ofReal (-simplexTerm a b i)) ≤ (∑' i, ENNReal.ofReal (simplexTerm a b i)) ∧
    (simplexExtendedDivergence a b = 0 ↔ a = b) := by
  obtain ⟨c, hc, hle, hlt⟩ := simplex_term_comparison three ha hb ap bp
  let p := fun i => max (c i) 0
  let n := fun i => max (-c i) 0
  have hp₀ (i : ι) : 0 ≤ p i := le_max_right _ _
  have hn₀ (i : ι) : 0 ≤ n i := le_max_right _ _
  have hp : Summable p := hc.summable.abs.of_nonneg_of_le hp₀ fun i =>
    max_le (le_abs_self _) (abs_nonneg _)
  have hn : Summable n := hc.summable.abs.of_nonneg_of_le hn₀ fun i =>
    max_le (neg_le_abs _) (abs_nonneg _)
  have hd : HasSum c ((∑' i, p i) - ∑' i, n i) := by
    have heq : (fun i => p i - n i) = c := by
      funext i
      change max (c i) 0 - max (-c i) 0 = c i
      by_cases hi : 0 ≤ c i
      · simp [max_eq_left hi, max_eq_right (neg_nonpos.mpr hi)]
      · simp [max_eq_right (le_of_not_ge hi), max_eq_left (neg_nonneg.mpr (le_of_not_ge hi))]
    rw [← heq]
    exact hp.hasSum.sub hn.hasSum
  have hpEq : (∑' i, p i) = ∑' i, n i := sub_eq_zero.mp (hd.unique hc)
  have hpR (i : ι) : ENNReal.ofReal (p i) = ENNReal.ofReal (c i) :=
    by simp [p, ENNReal.ofReal_max]
  have hnR (i : ι) : ENNReal.ofReal (n i) = ENNReal.ofReal (-c i) :=
    by simp [n, ENNReal.ofReal_max]
  have hbEq : (∑' i, ENNReal.ofReal (c i)) = ∑' i, ENNReal.ofReal (-c i) := by
    simp_rw [← hpR, ← hnR]
    rw [← ENNReal.ofReal_tsum_of_nonneg hp₀ hp, ← ENNReal.ofReal_tsum_of_nonneg hn₀ hn, hpEq]
  have hbc : (∑' i, ENNReal.ofReal (-c i)) ≠ ∞ := by
    simp_rw [← hnR]
    rw [← ENNReal.ofReal_tsum_of_nonneg hn₀ hn]
    exact ENNReal.ofReal_ne_top
  have hN : (∑' i, ENNReal.ofReal (-simplexTerm a b i)) ≠ ∞ :=
    ne_top_of_le_ne_top hbc (ENNReal.tsum_le_tsum fun i => ENNReal.ofReal_le_ofReal (neg_le_neg (hle i)))
  have H := congrArg (fun f : ι → ℝ≥0∞ => ∑' i, f i) (funext (fun i => ofReal_parts_balance (hle i)))
  simp only [ENNReal.tsum_add, hbEq] at H
  have htot : (∑' i, ENNReal.ofReal (simplexTerm a b i)) =
      (∑' i, ENNReal.ofReal (-simplexTerm a b i)) +
      ∑' i, ENNReal.ofReal (simplexTerm a b i - c i) := by
    apply (ENNReal.add_left_inj hbc).mp
    simpa only [add_right_comm] using H
  refine ⟨hN, ?_, ?_⟩
  · rw [htot]
    exact le_self_add
  · constructor
    · intro hz
      by_contra hne
      obtain ⟨i, hi⟩ := hlt hne
      unfold simplexExtendedDivergence at hz
      rw [htot, ENNReal.add_sub_cancel_left hN] at hz
      have hii := ENNReal.tsum_eq_zero.mp hz i
      linarith [ENNReal.ofReal_eq_zero.mp hii]
    · rintro rfl
      simp [simplexExtendedDivergence, simplexTerm]

end Certificate

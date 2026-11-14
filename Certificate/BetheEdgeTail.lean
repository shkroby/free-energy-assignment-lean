import Certificate.PressureFormula
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# An integrable bound for the Bethe edge term

The good event gives an exponential edge envelope. On the complementary
event Cauchy–Schwarz reduces the bound to a second moment and a log tail.
-/

open Filter MeasureTheory Set
open scoped ENNReal

namespace Certificate

private theorem softplus_le_log_two_add_pos (t : ℝ) :
    Real.log (1 + Real.exp t) ≤ Real.log 2 + max t 0 := by
  have h₁ : Real.exp t ≤ Real.exp (max t 0) := Real.exp_le_exp.mpr (le_max_left _ _)
  have h₂ : 1 ≤ Real.exp (max t 0) := Real.one_le_exp (le_max_right _ _)
  calc
    _ ≤ Real.log (2 * Real.exp (max t 0)) := by
      apply Real.log_le_log (by positivity)
      linarith
    _ = _ := by rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp]

/-- A second-moment bound and stretched logarithmic tail give the exact
shape of the integrable edge envelope used in the pressure formula. -/
theorem integral_softplus_le_of_tail {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {β d c K x : ℝ} (hβ : 0 < β) (hK : 0 ≤ K) (hx : 0 ≤ x)
    (hm : MemLp (fun s : ℝ ↦ Real.log 2 + β * max s 0) 2 μ)
    (htail : μ.real (Ioi (x / 2)) ≤ K * Real.exp (-c * (x / 2) ^ d)) :
    (∫ s, Real.log (1 + Real.exp (β * (s - x))) ∂μ) ≤
      Real.exp (-β * x / 2) +
        ((∫ s, (Real.log 2 + β * max s 0) ^ (2 : ℕ) ∂μ) ^ (1 / 2 : ℝ) *
          K ^ (1 / 2 : ℝ)) * Real.exp (-(c / 2 / (2 : ℝ) ^ d) * x ^ d) := by
  let S := Ioi (x / 2)
  let I : ℝ → ℝ := S.indicator 1
  let g : ℝ → ℝ := fun s ↦ Real.log 2 + β * max s 0
  let a := Real.exp (-β * x / 2)
  have hg (s : ℝ) : 0 ≤ g s := add_nonneg (Real.log_nonneg (by norm_num))
    (mul_nonneg hβ.le (le_max_right _ _))
  have hI : Measurable I := measurable_const.indicator measurableSet_Ioi
  have hIb : ∀ s, I s ∈ Icc (0 : ℝ) 1 := by
    intro s
    by_cases hs : s ∈ S <;> simp [I, hs]
  have hIm : MemLp I 2 μ := memLp_of_bounded (.of_forall hIb) hI.aestronglyMeasurable 2
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (.of_forall hg) (.of_forall fun s ↦ (hIb s).1)
    (show MemLp g (ENNReal.ofReal 2) μ from by simpa using hm)
    (show MemLp I (ENNReal.ofReal 2) μ from by simpa using hIm)
  have hprod : Integrable (fun s ↦ g s * I s) μ := hm.integrable_mul hIm
  have hdom (s : ℝ) : Real.log (1 + Real.exp (β * (s - x))) ≤ a + g s * I s := by
    by_cases hs : s ∈ S
    · rw [show I s = 1 from indicator_of_mem hs _, mul_one]
      refine (softplus_le_log_two_add_pos _).trans ?_
      have hmax : max (β * (s - x)) 0 ≤ β * max s 0 := by
        apply max_le
        · exact mul_le_mul_of_nonneg_left ((sub_le_self _ hx).trans (le_max_left _ _)) hβ.le
        · exact mul_nonneg hβ.le (le_max_right _ _)
      linarith [Real.exp_nonneg (-β * x / 2)]
    · rw [show I s = 0 from indicator_of_notMem hs _, mul_zero, add_zero]
      have hlog : Real.log (1 + Real.exp (β * (s - x))) ≤ Real.exp (β * (s - x)) := by
        linarith [Real.log_le_sub_one_of_pos (show 0 < 1 + Real.exp (β * (s - x)) by positivity)]
      refine hlog.trans ?_
      apply Real.exp_le_exp.mpr
      have hs' : s ≤ x / 2 := le_of_not_gt hs
      nlinarith [mul_nonneg hβ.le (sub_nonneg.mpr hs')]
  have hpos (s : ℝ) : 0 ≤ Real.log (1 + Real.exp (β * (s - x))) :=
    Real.log_nonneg (le_add_of_nonneg_right (Real.exp_nonneg _))
  have hqi : Integrable (fun s ↦ Real.log (1 + Real.exp (β * (s - x)))) μ :=
    ((integrable_const a).add hprod).mono' (Real.measurable_log.comp (by fun_prop)).aestronglyMeasurable
      (.of_forall fun s ↦ by rw [Real.norm_of_nonneg (hpos s)]; exact hdom s)
  have hQ : (∫ s, Real.log (1 + Real.exp (β * (s - x))) ∂μ) ≤
      ∫ s, a + g s * I s ∂μ :=
    integral_mono hqi ((integrable_const a).add hprod) hdom
  rw [integral_add (integrable_const a) hprod, integral_const, probReal_univ, smul_eq_mul, one_mul] at hQ
  have hIsq : (fun s ↦ I s ^ (2 : ℝ)) = I := by
    funext s
    by_cases hs : s ∈ S
    · simp [I, hs]
    · simp [I, hs]
  rw [hIsq, show (∫ s, I s ∂μ) = μ.real S by
    exact integral_indicator_one (s := S) measurableSet_Ioi] at hH
  have hpow : (μ.real S) ^ (1 / 2 : ℝ) ≤
      K ^ (1 / 2 : ℝ) * Real.exp (-(c / 2 / (2 : ℝ) ^ d) * x ^ d) := by
    refine (Real.rpow_le_rpow measureReal_nonneg htail (by positivity)).trans_eq ?_
    rw [Real.mul_rpow hK (Real.exp_nonneg _), ← Real.exp_mul, Real.div_rpow hx (by norm_num) d]
    congr 2
    ring
  simp only [Real.rpow_two] at hH
  calc
    _ ≤ a + ∫ s, g s * I s ∂μ := hQ
    _ ≤ a + (∫ s, g s ^ (2 : ℕ) ∂μ) ^ (1 / 2 : ℝ) * (μ.real S) ^ (1 / 2 : ℝ) :=
      add_le_add_right hH _
    _ ≤ _ := by
      dsimp only [a, g]
      rw [mul_assoc]
      gcongr

end Certificate

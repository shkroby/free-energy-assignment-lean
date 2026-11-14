import Certificate.PoissonShift

/-! The normalized Poisson recurrence characterizes the count law. -/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace Certificate

/-- A normalized nonnegative sequence with the Poisson size-bias recurrence
is the Poisson probability mass function. -/
theorem poisson_eq_of_count_recurrence (r : ℝ≥0) (p : ℕ → ℝ≥0∞)
    (hp : ∑' n, p n = 1)
    (hrec : ∀ n : ℕ, (↑(n+1 : ℕ) : ℝ≥0∞) * p (n+1) = (r : ℝ≥0∞) * p n) :
    ∀ n, p n = poissonMeasure r {n} := by
  have hfin : (∑' n, p n) ≠ ∞ := by rw [hp]; exact ENNReal.one_ne_top
  have hf (n : ℕ) : p n ≠ ∞ := ENNReal.ne_top_of_tsum_ne_top hfin n
  let q : ℕ → ℝ := fun n => (p n).toReal
  have hq : HasSum q 1 := by
    have h := (ENNReal.summable_toReal hfin).hasSum
    rw [← ENNReal.tsum_toReal_eq hf, hp, ENNReal.toReal_one] at h
    exact h
  have hstep (n : ℕ) : q (n+1) = (r : ℝ) * q n / ↑(n+1 : ℕ) := by
    have h := congrArg ENNReal.toReal (hrec n)
    simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.coe_toReal] at h
    apply (eq_div_iff (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))).mpr
    rw [mul_comm]
    exact h
  have hformula (n : ℕ) : q n = q 0 * ((r : ℝ) ^ n / n.factorial) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [hstep, ih, Nat.factorial_succ, Nat.cast_mul, pow_succ]
      field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)]
  have hsum : HasSum (fun n : ℕ => q 0 * ((r : ℝ)^n / n.factorial))
      (q 0 * Real.exp r) := by
    simpa only [← exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp (r : ℝ)).mul_left (q 0)
  rw [← funext hformula] at hsum
  have hnorm := hsum.unique hq
  have hzero : q 0 = Real.exp (-(r : ℝ)) := by
    rw [Real.exp_neg, ← one_div]
    exact (eq_div_iff (Real.exp_pos _).ne').mpr hnorm
  intro n
  rw [poissonMeasure_singleton, ← ENNReal.ofReal_toReal (hf n)]
  change ENNReal.ofReal (q n) = _
  rw [hformula n, hzero, mul_div_assoc]

end Certificate

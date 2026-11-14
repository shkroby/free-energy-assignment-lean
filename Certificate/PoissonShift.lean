import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Marked insertion at finite Poisson intensity

A Poisson count and conditionally iid marks satisfy the deletion/insertion
identity for nonnegative marked tests. This statement uses only finite product
laws and a scalar Poisson shift.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Certificate

/-- Size bias shifts the Poisson count by one. -/
theorem poisson_count_succ (r : ℝ≥0) (n : ℕ) :
    (↑(n + 1 : ℕ) : ℝ≥0∞) * poissonMeasure r {n+1} =
      (r : ℝ≥0∞) * poissonMeasure r {n} := by
  rw [poissonMeasure_singleton, poissonMeasure_singleton,
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_coe_nnreal,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
  field_simp

/-- The nonnegative expectation form of the Poisson size-bias identity. -/
theorem poisson_count_shift (r : ℝ≥0) (f : ℕ → ℝ≥0∞) :
    (∫⁻ n, (n : ℝ≥0∞) * f n ∂poissonMeasure r) =
      (r : ℝ≥0∞) * ∫⁻ n, f (n+1) ∂poissonMeasure r := by
  rw [lintegral_countable', lintegral_countable', ← ENNReal.tsum_mul_left]
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [Nat.cast_zero, zero_mul, zero_add]
  apply tsum_congr
  intro n
  calc
    (↑(n+1 : ℕ) * f (n+1)) * poissonMeasure r {n+1} =
        f (n+1) * (↑(n+1 : ℕ) * poissonMeasure r {n+1}) := by ac_rfl
    _ = ↑r * (f (n+1) * poissonMeasure r {n}) := by rw [poisson_count_succ]; ac_rfl

variable {X : Type*} [MeasurableSpace X]

/-- Under an iid product law, the expected sum over distinguished coordinates
is the number of coordinates times the expectation for one independent
distinguished mark and the remaining marks. -/
theorem lintegral_iid_deletion_sum (μ : Measure X) [SigmaFinite μ] (n : ℕ)
    (f : X × (Fin n → X) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ xs, ∑ i : Fin (n+1), f ((MeasurableEquiv.piFinSuccAbove (fun _ => X) i) xs)
      ∂(Measure.pi (fun _ : Fin (n+1) => μ))) =
      (↑(n+1 : ℕ) : ℝ≥0∞) *
        ∫⁻ z, f z ∂(μ.prod (Measure.pi (fun _ : Fin n => μ))) := by
  rw [lintegral_finsetSum _
    (f := fun i xs => f ((MeasurableEquiv.piFinSuccAbove (fun _ => X) i) xs))
    (fun i _ =>
    hf.comp (MeasurableEquiv.piFinSuccAbove (fun _ => X) i).measurable)]
  have h (i : Fin (n+1)) :
      (∫⁻ xs, f ((MeasurableEquiv.piFinSuccAbove (fun _ => X) i) xs)
        ∂(Measure.pi (fun _ : Fin (n+1) => μ))) =
        ∫⁻ z, f z ∂(μ.prod (Measure.pi (fun _ : Fin n => μ))) :=
    ((measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) i).lintegral_map_equiv
      f (MeasurableEquiv.piFinSuccAbove (fun _ => X) i)).symm
  simp_rw [h]
  simp [nsmul_eq_mul]

/-- Expected sum over all distinguished marks, given the current count. -/
noncomputable def conditionalDeletion (μ : Measure X)
    (f : (n : ℕ) → X × (Fin n → X) → ℝ≥0∞) : ℕ → ℝ≥0∞
  | 0 => 0
  | n+1 => ∫⁻ xs, ∑ i : Fin (n+1), f n ((MeasurableEquiv.piFinSuccAbove (fun _ => X) i) xs)
      ∂(Measure.pi (fun _ : Fin (n+1) => μ))

/-- Finite intensity marked insertion. For a Poisson count with rate `r` and
iid marks with law `μ`, the expected sum over distinguished marks equals
`r` times the expected contribution of an independent inserted mark. The
input `f n` sees the distinguished mark together with the other `n` marks. -/
theorem finite_marked_poisson_insertion (r : ℝ≥0) (μ : Measure X) [IsProbabilityMeasure μ]
    (f : (n : ℕ) → X × (Fin n → X) → ℝ≥0∞) (hf : ∀ n, Measurable (f n)) :
    (∫⁻ k, conditionalDeletion μ f k ∂poissonMeasure r) =
      (r : ℝ≥0∞) * ∫⁻ n, (∫⁻ z, f n z ∂(μ.prod (Measure.pi (fun _ : Fin n => μ))))
        ∂poissonMeasure r := by
  let g (n : ℕ) : ℝ≥0∞ := ∫⁻ z, f n z ∂(μ.prod (Measure.pi (fun _ : Fin n => μ)))
  let G : ℕ → ℝ≥0∞ := fun
    | 0 => 0
    | n+1 => g n
  have hG : (fun k => conditionalDeletion μ f k) = fun k : ℕ => (k : ℝ≥0∞) * G k := by
    funext k
    cases k with
    | zero => simp [conditionalDeletion, G]
    | succ n => exact lintegral_iid_deletion_sum μ n (f n) (hf n)
  rw [hG, poisson_count_shift r G]

end Certificate

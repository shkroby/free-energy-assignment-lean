import Certificate.PoissonFull
import Mathlib.MeasureTheory.Measure.Real

/-!
# Void probabilities for the countable marked Poisson model
-/

open Filter MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal NNReal BigOperators Topology

namespace Certificate

variable {X : Type*} [MeasurableSpace X]

/-- The event that a batch contains no mark in the specified set. -/
def poissonBatchAvoid (s : Set X) : Set (PoissonBatch X) :=
  {b | ∀ i : Fin b.1, b.2 i ∉ s}

theorem measurableSet_poissonBatchAvoid {s : Set X} (hs : MeasurableSet s) :
    MeasurableSet (poissonBatchAvoid s) := by
  unfold poissonBatchAvoid
  rw [measurableSet_setOfPred]
  apply measurable_on_poissonBatch
  intro n
  change Measurable (fun xs : Fin n → X => ∀ i : Fin n, xs i ∉ s)
  exact Measurable.forall (fun i => hs.compl.mem.comp (measurable_pi_apply i))

private theorem poissonBatchAvoid_series (r : ℝ≥0) (μ : Measure X) [IsProbabilityMeasure μ]
    {s : Set X} (hs : MeasurableSet s) :
    poissonBatchLaw r μ (poissonBatchAvoid s) =
      ∑' n : ℕ, poissonMeasure r {n} * (μ sᶜ)^n := by
  rw [poissonBatchLaw, Measure.sum_apply _ (measurableSet_poissonBatchAvoid hs)]
  apply tsum_congr
  intro n
  have hmap : (fun xs : Fin n → X => (⟨n,xs⟩ : PoissonBatch X)) ⁻¹'
      poissonBatchAvoid s = Set.univ.pi (fun _ : Fin n => sᶜ) := by
    ext xs
    simp [poissonBatchAvoid, Set.mem_pi]
  rw [Measure.smul_apply, Measure.map_apply (measurable_poissonBatch_mk n)
    (measurableSet_poissonBatchAvoid hs), hmap, Measure.pi_pi, smul_eq_mul]
  simp

/-- Void probability for a finite intensity marked Poisson batch. -/
theorem poissonBatch_void (r : ℝ≥0) (μ : Measure X) [IsProbabilityMeasure μ]
    {s : Set X} (hs : MeasurableSet s) :
    poissonBatchLaw r μ (poissonBatchAvoid s) =
      ENNReal.ofReal (Real.exp (-(r * (μ s).toReal : ℝ))) := by
  rw [poissonBatchAvoid_series r μ hs]
  let a : ℝ := r
  let p : ℝ := (μ sᶜ).toReal
  let q : ℝ := (μ s).toReal
  have ha : 0 ≤ a := r.coe_nonneg
  have hp : 0 ≤ p := ENNReal.toReal_nonneg
  have hpq : p = 1 - q := by
    change μ.real sᶜ = 1 - μ.real s
    rw [measureReal_compl hs, probReal_univ]
  have hsum : HasSum (fun n : ℕ => Real.exp (-a) * ((a*p)^n / n.factorial))
      (Real.exp (-a) * Real.exp (a*p)) := by
    simpa only [← exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp (a*p)).mul_left (Real.exp (-a))
  have hterm (n : ℕ) : poissonMeasure r {n} * (μ sᶜ)^n =
      ENNReal.ofReal (Real.exp (-a) * ((a*p)^n / n.factorial)) := by
    have hco : μ sᶜ = ENNReal.ofReal p :=
      (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
    rw [poissonMeasure_singleton, hco, ← ENNReal.ofReal_pow hp,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [mul_pow]
    dsimp [a]
    ring
  simp_rw [hterm]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum.summable, hsum.tsum_eq,
    ← Real.exp_add]
  congr 2
  change -a + a*p = -(a*q)
  rw [hpq]
  ring

/-- The event that there is no mark in the specified set in any batch. -/
def poissonAvoid {I : Type*} (s : Set X) : Set (I → PoissonBatch X) :=
  Set.univ.pi (fun _ => poissonBatchAvoid s)

theorem measurableSet_poissonAvoid {I : Type*} [Countable I] {s : Set X}
    (hs : MeasurableSet s) : MeasurableSet (poissonAvoid (I := I) s) :=
  MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_poissonBatchAvoid hs)

private theorem hasProd_ofReal_exp_of_hasSum {I : Type*} {a : I → ℝ} {v : ℝ}
    (h : HasSum a v) : HasProd (fun j => ENNReal.ofReal (Real.exp (a j)))
      (ENNReal.ofReal (Real.exp v)) := by
  unfold HasProd
  have heq (s : Finset I) : (∏ j ∈ s, ENNReal.ofReal (Real.exp (a j))) =
      ENNReal.ofReal (Real.exp (∑ j ∈ s, a j)) := by
    rw [Real.exp_sum, ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le)]
  simp_rw [heq]
  exact ((ENNReal.continuous_ofReal.comp Real.continuous_exp).tendsto v).comp h

/-- Void probability for the countable marked process on a measurable set of
finite intensity. -/
theorem poisson_void {I : Type*} [Countable I]
    (rate : I → ℝ≥0) (μ : I → Measure X) [∀ j, IsProbabilityMeasure (μ j)]
    {s : Set X} (hs : MeasurableSet s) (hfin : poissonIntensity rate μ s ≠ ∞) :
    poissonProcessLaw rate μ (poissonAvoid s) =
      ENNReal.ofReal (Real.exp (-(poissonIntensity rate μ s).toReal)) := by
  let c (j : I) := (rate j : ℝ≥0∞) * μ j s
  have hC : (∑' j, c j) = poissonIntensity rate μ s := by
    rw [poissonIntensity, Measure.sum_apply _ hs]
    rfl
  have hsumFin : (∑' j, c j) ≠ ∞ := hC ▸ hfin
  have hterms : ∀ j, c j ≠ ∞ := ENNReal.ne_top_of_tsum_ne_top hsumFin
  have hsum₀ := (ENNReal.summable_toReal hsumFin).hasSum
  rw [← ENNReal.tsum_toReal_eq hterms, hC] at hsum₀
  have hsum : HasSum (fun j : I => -((rate j : ℝ) * (μ j s).toReal))
      (-(poissonIntensity rate μ s).toReal) := by
    simpa only [c, ENNReal.toReal_mul, ENNReal.coe_toReal] using hsum₀.neg
  rw [poissonProcessLaw, poissonAvoid,
    Measure.infinitePi_pi_univ _ (fun _ => measurableSet_poissonBatchAvoid hs)]
  simp_rw [poissonBatch_void _ _ hs]
  exact (hasProd_ofReal_exp_of_hasSum hsum).tprod_eq

end Certificate

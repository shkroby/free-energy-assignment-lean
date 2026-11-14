import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.ProductMeasure
import Mathlib.GroupTheory.Perm.Finite

/-!
# The square bipartite assignment problem

Concrete definitions and a statement of the manuscript's main theorem.
`FreeEnergyClaim` is a proposition; this file does not assert a proof of it.
-/

open scoped BigOperators Topology
open Filter Set MeasureTheory ProbabilityTheory

namespace Certificate

/-- All matrix sizes use the same infinite array; a size-`n` matrix uses its first
`n` rows and columns. -/
abbrev CostArray := (ℕ × ℕ) → ℝ

/-- The joint law of the infinite array of independent costs. -/
noncomputable def iidCosts (μ : Measure ℝ) : Measure CostArray :=
  Measure.infinitePi (fun _ : ℕ × ℕ ↦ μ)

noncomputable def lengthScale (d κ : ℝ) (n : ℕ) : ℝ :=
  (κ * (n : ℝ)) ^ (1 / d : ℝ)

/-- The perfect matching partition function of a square matrix of weights. -/
noncomputable def permanent {n : ℕ} (w : Fin n → Fin n → ℝ) : ℝ :=
  ∑ σ : Equiv.Perm (Fin n), ∏ i : Fin n, w i (σ i)

theorem permanent_pos {n : ℕ} {w : Fin n → Fin n → ℝ} (hw : ∀ i j, 0 < w i j) :
    0 < permanent w := by
  unfold permanent
  exact Finset.sum_pos (fun σ _ ↦ Finset.prod_pos (fun i _ ↦ hw i (σ i)))
    ⟨Equiv.refl _, Finset.mem_univ _⟩

noncomputable def assignmentPartition (β d κ : ℝ) (n : ℕ) (C : CostArray) : ℝ :=
  permanent (n := n) (fun i j ↦ Real.exp (-(β * lengthScale d κ n * C (i.val, j.val))))

noncomputable def pressure (β d κ : ℝ) (n : ℕ) (C : CostArray) : ℝ :=
  Real.log (assignmentPartition β d κ n C) / (n : ℝ)

theorem assignmentPartition_pos (β d κ : ℝ) (n : ℕ) (C : CostArray) :
    0 < assignmentPartition β d κ n C :=
  permanent_pos (fun _ _ ↦ Real.exp_pos _)

/-- Log-sum pressure is an everywhere measurable function of the array. -/
theorem measurable_pressure (β d κ : ℝ) (n : ℕ) : Measurable (pressure β d κ n) := by
  unfold pressure assignmentPartition permanent
  fun_prop

/-- The law of the independent rate-one exponential waiting times. -/
noncomputable def exponentialSpacings : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ ↦ expMeasure 1)

theorem isProbabilityMeasure_exponentialSpacings : IsProbabilityMeasure exponentialSpacings := by
  let : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure zero_lt_one
  unfold exponentialSpacings
  infer_instance

/-- The increasing points of the usual arrival-time representation of the PWIT intensity.
Summing the first `i+1` spacings gives arrival `i` at unit rate, then the map
`x ↦ x^(1/d)` changes Lebesgue intensity to `d * x^(d-1) dx`.
The Poisson process characterization is a further theorem, not assumed here. -/
noncomputable def arrivalLength (d : ℝ) (E : ℕ → ℝ) (i : ℕ) : ℝ :=
  (∑ j ∈ Finset.range (i + 1), E j) ^ (1 / d : ℝ)

noncomputable def intensity (d : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity (fun x ↦ ENNReal.ofReal (d * x ^ (d - 1)))

/-- Spacings and the infinite family of child marks are sampled independently. -/
noncomputable def markedSpacings (μ : Measure ℝ) : Measure ((ℕ → ℝ) × (ℕ → ℝ)) :=
  exponentialSpacings.prod (Measure.infinitePi (fun _ : ℕ ↦ μ))

noncomputable def cavityTerm (β d : ℝ) (ω : (ℕ → ℝ) × (ℕ → ℝ)) (i : ℕ) : ℝ :=
  Real.exp (-β * arrivalLength d ω.1 i) * ω.2 i

noncomputable def cavityMap (β d : ℝ) (ω : (ℕ → ℝ) × (ℕ → ℝ)) : ℝ :=
  (∑' i, cavityTerm β d ω i)⁻¹

/-- The zero-fugacity recursive law, with almost sure summability recorded explicitly
because a bare Lean `tsum` uses a default value outside the convergent case. -/
def IsCavityLaw (β d : ℝ) (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ μ (Ioi 0) = 1 ∧
    (∀ᵐ ω ∂markedSpacings μ, Summable (cavityTerm β d ω) ∧
      0 < ∑' i, cavityTerm β d ω i) ∧
    (markedSpacings μ).map (cavityMap β d) = μ

noncomputable def edgeLogCorrection (β : ℝ) (μ : Measure ℝ) (x : ℝ) : ℝ :=
  ∫ h : ℝ × ℝ, Real.log (1 + Real.exp (-β * x) * h.1 * h.2) ∂(μ.prod μ)

noncomputable def bethePressure (β d : ℝ) (μ : Measure ℝ) : ℝ :=
  -2 * (∫ h, Real.log h ∂μ) - ∫ x, edgeLogCorrection β μ x ∂intensity d

/-- The small-cost CDF hypothesis, with both the scale and the exponent specified. -/
def SmallCostTail (μ : Measure ℝ) (κ d : ℝ) : Prop :=
  μ (Iio 0) = 0 ∧
    Tendsto (fun s ↦ cdf μ s / (κ * s ^ d)) (𝓝[>] 0) (𝓝 1)

/-- Target statement for the main theorem of the manuscript.
The term-by-term integrability hypotheses in the conclusion distinguish the Bethe
formula from a default value of a nonintegrable Bochner integral. -/
def FreeEnergyClaim : Prop :=
  ∀ (μ : Measure ℝ) (_ : IsProbabilityMeasure μ) (κ d β : ℝ),
    0 < κ → 0 < d → 0 < β → SmallCostTail μ κ d →
    ∃ H : Measure ℝ, IsCavityLaw β d H ∧
      (∀ H' : Measure ℝ, IsCavityLaw β d H' → H' = H) ∧
      Integrable Real.log H ∧
      (∀ x ∈ Ioi (0 : ℝ),
        Integrable (fun h : ℝ × ℝ ↦ Real.log (1 + Real.exp (-β * x) * h.1 * h.2))
          (H.prod H)) ∧
      Integrable (edgeLogCorrection β H) (intensity d) ∧
      (∀ᵐ C ∂iidCosts μ, Tendsto (fun n ↦ pressure β d κ n C) atTop
        (𝓝 (bethePressure β d H))) ∧
      ((∃ q : ℝ, 0 < q ∧ Integrable (fun c : ℝ ↦ c ^ q) μ) →
        (∀ᶠ n in atTop, Integrable (pressure β d κ n) (iidCosts μ)) ∧
        Tendsto (fun n ↦ ∫ C, |pressure β d κ n C - bethePressure β d H| ∂iidCosts μ)
          atTop (𝓝 0))

/-- Additional uniqueness target, stated separately to quantify over all positive
finite solution laws, without already assuming any log moments. -/
def CavityUniquenessClaim : Prop :=
  ∀ d β : ℝ, 0 < d → 0 < β → ∃! H : Measure ℝ, IsCavityLaw β d H

end Certificate

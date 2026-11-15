import Certificate.SoftLogLowerTail
import Certificate.HardLogMoment

/-! Common logarithmic second-moment bounds for the positive-fugacity laws. -/

open Filter MeasureTheory Set
open scoped ENNReal

namespace Certificate

/-- The cubic bound on the two-sided scaled logarithmic tail starts at a
threshold common to the whole soft family. -/
theorem eventually_uniform_soft_cavity_absolute_log_power_tail {ι : Type*} {β d K : ℝ}
    (hd : 0 < d) (hβ : 0 < β) (hK : 0 ≤ K)
    (z : ι → ℝ) (ν : ι → ProbabilityMeasure ℝ)
    (hz : ∀ i, 0 < z i) (hz₁ : ∀ i, z i ≤ 1)
    (hμ : ∀ i, ∀ᵐ x ∂(ν i : Measure ℝ), x ∈ Ioc 0 (z i)⁻¹)
    (hLaw : ∀ i, (markedSpacings (ν i : Measure ℝ)).map (arrivalSoftOutput β d (z i)) =
      (ν i : Measure ℝ))
    (hUpper : ∀ i t, 0 ≤ t → (ν i : Measure ℝ) (Ioi (Real.exp (β*t))) ≤
      ENNReal.ofReal (K * Real.exp (-((t/2)^d/2)))) :
    ∀ᶠ t : ℝ in atTop, ∀ i, (ν i : Measure ℝ) {x | t < |Real.log x| / β} ≤
      ENNReal.ofReal (t^(-3:ℝ)) := by
  obtain ⟨C₁, C₂, h₁, h₂, hLower⟩ := exists_uniform_soft_cavity_log_lowerTail hd hβ hK
  filter_upwards [eventually_log_tail_envelope_le_cubic hd hβ hK h₁ h₂,
    eventually_ge_atTop (Real.log 2 / β)] with t hEnv ht
  intro i
  have hp := (hμ i).mono (fun _ h => h.1)
  have hb : ∀ᵐ x ∂(ν i : Measure ℝ), x ∈ Icc 0 (z i)⁻¹ :=
    (hμ i).mono (fun _ h => ⟨h.1.le, h.2⟩)
  exact ((absolute_log_div_tail_le_union hβ (ν i : Measure ℝ) hp t).trans
    (add_le_add (hUpper i t hEnv.1)
      (hLower (z i) (hz i) (hz₁ i) (ν i : Measure ℝ) inferInstance hb
        (hLaw i) (hUpper i) t ht))).trans hEnv.2

/-- A single finite L² bound controls the logarithms of all soft laws in
the family. -/
theorem exists_uniform_soft_cavity_log_eLpNorm_two_le {ι : Type*} {β d K : ℝ}
    (hd : 0 < d) (hβ : 0 < β) (hK : 0 ≤ K)
    (z : ι → ℝ) (ν : ι → ProbabilityMeasure ℝ)
    (hz : ∀ i, 0 < z i) (hz₁ : ∀ i, z i ≤ 1)
    (hμ : ∀ i, ∀ᵐ x ∂(ν i : Measure ℝ), x ∈ Ioc 0 (z i)⁻¹)
    (hLaw : ∀ i, (markedSpacings (ν i : Measure ℝ)).map (arrivalSoftOutput β d (z i)) =
      (ν i : Measure ℝ))
    (hUpper : ∀ i t, 0 ≤ t → (ν i : Measure ℝ) (Ioi (Real.exp (β*t))) ≤
      ENNReal.ofReal (K * Real.exp (-((t/2)^d/2)))) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ i, eLpNorm Real.log 2 (ν i : Measure ℝ) ≤ ENNReal.ofReal B := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (eventually_uniform_soft_cavity_absolute_log_power_tail hd hβ hK z ν hz hz₁ hμ hLaw hUpper)
  let M : ℝ := max T 1
  have hM : 1 ≤ M := le_max_right T 1
  have hM₀ : 0 ≤ M := zero_le_one.trans hM
  refine ⟨β * M * (3 : ℝ)^(1 / 2 : ℝ), by positivity, fun i => ?_⟩
  exact eLpNorm_two_log_le_of_power_tail_after hβ hM (ν i : Measure ℝ)
    (fun t ht => hT t ((le_max_left T 1).trans ht) i)

end Certificate

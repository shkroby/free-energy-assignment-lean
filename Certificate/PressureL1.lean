import Certificate.PressurePositive
import Certificate.Integrability

/-!
# From the almost-sure hard-pressure limit to its L¹ limit

The moment hypothesis alone gives eventual integrability. To obtain convergence,
the negative part is bounded on good arrays, while the polynomial exceptional
probability and the cyclic-assignment second moment control the error.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace Certificate

private theorem positive_sub_negative (β d κ : ℝ) (n : ℕ) (C : CostArray) :
    positivePressure β d κ n C - negativePressure β d κ n C = pressure β d κ n C := by
  unfold positivePressure negativePressure
  rcases le_total 0 (pressure β d κ n C) with h | h
  · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), sub_zero]
  · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h), zero_sub, neg_neg]

/-- A finite positive-order moment makes the square assignment pressures
integrable once the number of disjoint cyclic assignments is sufficiently large. -/
theorem eventually_integrable_pressure
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {β d κ q : ℝ}
    (hβ : 0 < β) (hd : 0 < d) (hκ : 0 < κ) (hq : 0 < q)
    (hμ : SmallCostTail μ κ d) (hM : Integrable (fun c : ℝ ↦ c ^ q) μ) :
    ∀ᶠ n in atTop, Integrable (pressure β d κ n) (iidCosts μ) := by
  let : IsProbabilityMeasure (iidCosts μ) := by unfold iidCosts; infer_instance
  obtain ⟨A, _, ℓ, hA⟩ := eLpNorm_negativePressure_le_of_moment μ hβ hd hκ hq hμ.1 hM
  obtain ⟨B, _, hB⟩ := eLpNorm_positivePressure_bdd hβ hd hκ hμ
  filter_upwards [eventually_ge_atTop (max ℓ 1)] with n hn
  have hn₁ : 0 < n := lt_of_lt_of_le zero_lt_one ((le_max_right ℓ 1).trans hn)
  have hnℓ : ℓ ≤ n := (le_max_left ℓ 1).trans hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn₁.ne'
  have hp : MemLp (positivePressure β d κ (m + 1)) 2 (iidCosts μ) :=
    ⟨(measurable_positivePressure β d κ _).aestronglyMeasurable,
      (hB _ hn₁).trans_lt ENNReal.ofReal_lt_top⟩
  have hm : MemLp (negativePressure β d κ (m + 1)) 2 (iidCosts μ) :=
    ⟨(measurable_negativePressure β d κ _).aestronglyMeasurable,
      (hA m hnℓ).trans_lt ENNReal.ofReal_lt_top⟩
  have heq : positivePressure β d κ (m + 1) - negativePressure β d κ (m + 1) =
      pressure β d κ (m + 1) := funext (fun C ↦ positive_sub_negative β d κ (m + 1) C)
  rw [← heq]
  exact (hp.sub hm).integrable (by norm_num)

/-- Restricting a function to a small event reduces the L¹ norm by the square
root of the event probability, at a cost of using its L² norm. -/
theorem eLpNorm_indicator_one_le_two {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {s : Set Ω} (hs : MeasurableSet s)
    {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) :
    eLpNorm (s.indicator f) 1 μ ≤ eLpNorm f 2 μ * μ s ^ (1 / 2 : ℝ) := by
  have hh := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2)
    (by norm_num) (hf.restrict : AEStronglyMeasurable f (μ.restrict s))
  rw [Measure.restrict_apply_univ] at hh
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]
  calc
    _ ≤ eLpNorm f 2 (μ.restrict s) * μ s ^ (1 / 2 : ℝ) := by
      convert hh using 2
      norm_num
    _ ≤ _ := by
      gcongr
      exact Measure.restrict_le_self

/-- The L¹ conclusion under the two stochastic conclusions used in the
manuscript. The exceptional bound is needed only at one sufficiently high
polynomial rate, and only for sufficiently large sizes. -/
theorem pressure_L1_of_ae_of_completion_events
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {β d κ q limit : ℝ}
    (hβ : 0 < β) (hd : 0 < d) (hκ : 0 < κ) (hq : 0 < q)
    (hμ : SmallCostTail μ κ d) (hM : Integrable (fun c : ℝ ↦ c ^ q) μ)
    (hlim : ∀ᵐ C ∂iidCosts μ, Tendsto (fun n ↦ pressure β d κ n C) atTop (𝓝 limit))
    {L D : ℝ} (hL : 0 ≤ L) (hD : 0 ≤ D) (bad : ℕ → Set CostArray)
    (hbad : ∀ᶠ n in atTop,
      MeasurableSet (bad n) ∧
      iidCosts μ (bad n) ≤ ENNReal.ofReal (D * (n : ℝ) ^ (-(2 * (1 / d + 1 / q + 1)))) ∧
      ∀ C ∉ bad n, negativePressure β d κ n C ≤ L) :
    Tendsto (fun n ↦ ∫ C, |pressure β d κ n C - limit| ∂iidCosts μ) atTop (𝓝 0) := by
  let : IsProbabilityMeasure (iidCosts μ) := by unfold iidCosts; infer_instance
  obtain ⟨A, hA, ℓ, hNeg⟩ := eLpNorm_negativePressure_le_of_moment μ hβ hd hκ hq hμ.1 hM
  obtain ⟨P, hP, hPos⟩ := eLpNorm_positivePressure_bdd hβ hd hκ hμ
  obtain ⟨J, hJ⟩ := eventually_atTop.mp hbad
  let k : ℕ := max J ℓ
  let N (n : ℕ) := n + k + 1
  let W := iidCosts μ
  let α : ℝ := 1 / d + 1 / q
  have hSize (n : ℕ) : 0 < N n := by dsimp [N]; omega
  have hJ' (n : ℕ) : J ≤ N n := by dsimp [N, k]; omega
  have hℓ' (n : ℕ) : ℓ ≤ N n := by dsimp [N, k]; omega
  have hs (n : ℕ) := (hJ _ (hJ' n)).1
  let U : ℕ → CostArray → ℝ := fun n ↦ positivePressure β d κ (N n)
  let V : ℕ → CostArray → ℝ := fun n ↦ negativePressure β d κ (N n)
  let f : ℕ → CostArray → ℝ := fun n ↦ U n - (bad (N n))ᶜ.indicator (V n)
  let g : ℕ → CostArray → ℝ := fun n ↦ -((bad (N n)).indicator (V n))
  have hmeasU (n : ℕ) : Measurable (U n) := measurable_positivePressure _ _ _ _
  have hmeasV (n : ℕ) : Measurable (V n) := measurable_negativePressure _ _ _ _
  have hbV (n : ℕ) : eLpNorm (V n) 2 W ≤ ENNReal.ofReal (A * (N n : ℝ) ^ α) := by
    simpa [V, W, N, α, Nat.cast_add] using hNeg (n + k) (hℓ' n)
  have hgf (n : ℕ) (C : CostArray) : f n C + g n C = pressure β d κ (N n) C := by
    by_cases h : C ∈ bad (N n)
    · have hn : C ∉ (bad (N n))ᶜ := by simpa
      simp only [f, g, Pi.sub_apply, Pi.neg_apply, Set.indicator_of_notMem hn,
        Set.indicator_of_mem h, sub_zero, ← sub_eq_add_neg]
      exact positive_sub_negative _ _ _ _ _
    · have hh : C ∈ (bad (N n))ᶜ := h
      simp only [f, g, Pi.sub_apply, Pi.neg_apply, Set.indicator_of_notMem h,
        Set.indicator_of_mem hh, neg_zero, add_zero]
      exact positive_sub_negative _ _ _ _ _
  have hmF (n : ℕ) : AEStronglyMeasurable (f n) W :=
    (hmeasU n).aestronglyMeasurable.sub ((hmeasV n).indicator (hs n).compl).aestronglyMeasurable
  have hfBound (n : ℕ) : eLpNorm (f n) 2 W ≤ ENNReal.ofReal (P + L) := by
    have hc : ∀ C, ‖(bad (N n))ᶜ.indicator (V n) C‖ ≤ L := by
      intro C
      by_cases h : C ∈ bad (N n)
      · rw [Set.indicator_of_notMem (show C ∉ (bad (N n))ᶜ by simpa), norm_zero]
        exact hL
      · rw [Set.indicator_of_mem (show C ∈ (bad (N n))ᶜ from h),
          Real.norm_of_nonneg (show 0 ≤ V n C from le_max_right _ _)]
        exact (hJ _ (hJ' n)).2.2 C h
    have hb := eLpNorm_le_of_ae_bound (μ := W) (p := (2 : ℝ≥0∞)) (.of_forall hc)
    rw [measure_univ, ENNReal.one_rpow, one_mul] at hb
    have hTri := eLpNorm_sub_le (p := (2 : ℝ≥0∞)) (hmeasU n).aestronglyMeasurable
      ((hmeasV n).indicator (hs n).compl).aestronglyMeasurable (by norm_num)
      (μ := W)
    calc
      _ ≤ eLpNorm (U n) 2 W + eLpNorm ((bad (N n))ᶜ.indicator (V n)) 2 W := hTri
      _ ≤ ENNReal.ofReal P + ENNReal.ofReal L := add_le_add (hPos _ (hSize n)) hb
      _ = _ := (ENNReal.ofReal_add hP hL).symm
  have hgBound (n : ℕ) : eLpNorm (g n) 1 W ≤
      ENNReal.ofReal (A * D ^ (1 / 2 : ℝ) / (N n : ℝ)) := by
    have hNpos : 0 < (N n : ℝ) := Nat.cast_pos.mpr (hSize n)
    have hNnon := hNpos.le
    dsimp only [g]
    rw [eLpNorm_neg]
    calc
      _ ≤ eLpNorm (V n) 2 W * (W (bad (N n))) ^ (1 / 2 : ℝ) :=
        eLpNorm_indicator_one_le_two (hs n) (hmeasV n).aestronglyMeasurable
      _ ≤ ENNReal.ofReal (A * (N n : ℝ) ^ α) *
            ENNReal.ofReal (D * (N n : ℝ) ^ (-(2 * (α + 1)))) ^ (1 / 2 : ℝ) := by
        gcongr
        · exact hbV n
        · exact (hJ _ (hJ' n)).2.1
      _ = _ := by
        have hd' : 0 ≤ D * (N n : ℝ) ^ (-(2 * (α + 1))) := by positivity
        rw [ENNReal.ofReal_rpow_of_nonneg hd' (by norm_num), ← ENNReal.ofReal_mul (by positivity),
          Real.mul_rpow hD (by positivity), ← Real.rpow_mul hNnon]
        congr 1
        have hExp : -(2 * (α + 1)) * (1 / 2) = -1 - α := by ring
        rw [hExp]
        calc
          A * (N n : ℝ) ^ α * (D ^ (1 / 2 : ℝ) * (N n : ℝ) ^ (-1 - α)) =
              (A * D ^ (1 / 2 : ℝ)) * ((N n : ℝ) ^ α * (N n : ℝ) ^ (-1 - α)) := by ring
          _ = _ := by
            rw [← Real.rpow_add hNpos, show α + (-1 - α) = -1 by ring, Real.rpow_neg_one]
            exact (div_eq_mul_inv _ _).symm
  have hgLp (n : ℕ) : MemLp (g n) 1 W :=
    ⟨((hmeasV n).indicator (hs n)).aestronglyMeasurable.neg,
      (hgBound n).trans_lt ENNReal.ofReal_lt_top⟩
  have hgLim : Tendsto (fun n ↦ eLpNorm (g n) 1 W) atTop (𝓝 0) := by
    have hDenom : Tendsto (fun n : ℕ ↦ (N n : ℝ)) atTop atTop := by
      simpa only [N, Nat.add_assoc, Function.comp_def] using
        (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat (k + 1))
    have hbLim : Tendsto (fun n ↦ ENNReal.ofReal (A * D ^ (1 / 2 : ℝ) / (N n : ℝ)))
        atTop (𝓝 0) := by
      simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal (hDenom.const_div_atTop (A * D ^ (1 / 2 : ℝ)))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbLim
      (fun _ ↦ by positivity) hgBound
  have hlShift : ∀ᵐ C ∂W, Tendsto (fun n ↦ f n C + g n C) atTop (𝓝 limit) := by
    filter_upwards [hlim] with C hC
    simp only [hgf, N, Nat.add_assoc]
    exact (tendsto_add_atTop_iff_nat (k + 1)).mpr hC
  have hL1 := tendsto_L1_of_ae_of_L2_add_small_L1 (μ := W)
    (add_nonneg hP hL) hmF hfBound hgLp hgLim hlShift
  simp only [hgf, N, Nat.add_assoc] at hL1
  exact (tendsto_add_atTop_iff_nat (k + 1)).mp hL1

end Certificate

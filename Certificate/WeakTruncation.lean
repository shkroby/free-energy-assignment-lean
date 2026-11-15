import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-!
# Removing truncations in a weak limit

The laws of the finite truncations may be computed on a different
probability space at each index. Uniform tails for the approximation
errors still suffice to pass to the full laws.
-/

open Filter MeasureTheory Set
open scoped Topology NNReal

namespace Certificate

private theorem integral_lipschitz_map_sub_le {Ω T : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace T] [MeasurableSpace T] [OpensMeasurableSpace T]
    [SecondCountableTopology T] [Inhabited T]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : T → ℝ} {L : ℝ≥0} {M : ℝ}
    (hLip : LipschitzWith L f) (hM : ∀ x y, dist (f x) (f y) ≤ M)
    {X Y : Ω → T} (hX : Measurable X) (hY : Measurable Y) {δ : ℝ} (hδ : 0 ≤ δ) :
    |(∫ x, f x ∂μ.map X) - ∫ x, f x ∂μ.map Y| ≤
      (L : ℝ) * δ + M * μ.real {ω | δ ≤ dist (X ω) (Y ω)} := by
  let A : Set Ω := {ω | δ ≤ dist (X ω) (Y ω)}
  have hA : MeasurableSet A :=
    measurableSet_le measurable_const (hX.dist hY)
  have hF : Measurable f := hLip.continuous.measurable
  have hFi {Z : Ω → T} (hZ : Measurable Z) : Integrable (fun ω ↦ f (Z ω)) μ := by
    apply Integrable.of_bound (hF.comp hZ).aestronglyMeasurable (|f default| + M)
    refine .of_forall fun ω ↦ ?_
    have h := (abs_sub_abs_le_abs_sub (f (Z ω)) (f default)).trans
      (by simpa only [Real.dist_eq] using hM (Z ω) default)
    change |f (Z ω)| ≤ |f default| + M
    linarith
  have hi := (hFi hX).sub (hFi hY)
  have hi' : Integrable (fun ω ↦ |f (X ω) - f (Y ω)|) μ := hi.abs
  have hf : ∀ ω, |f (X ω) - f (Y ω)| ≤ ((L : ℝ) * δ) + A.indicator (fun _ ↦ M) ω := by
    intro ω
    by_cases hω : ω ∈ A
    · rw [indicator_of_mem hω]
      exact (by simpa only [Real.dist_eq] using hM (X ω) (Y ω) :
        |f (X ω) - f (Y ω)| ≤ M).trans (le_add_of_nonneg_left (by positivity))
    · rw [indicator_of_notMem hω, add_zero]
      have hl : dist (X ω) (Y ω) ≤ δ := (lt_of_not_ge hω).le
      simpa only [Real.dist_eq] using hLip.dist_le_mul_of_le hl
  have hInd := (integrable_const M (μ := μ)).indicator hA
  have hCalc : (∫ ω, (L : ℝ) * δ + A.indicator (fun _ ↦ M) ω ∂μ) =
      (L : ℝ) * δ + M * μ.real A := by
    rw [integral_add (integrable_const _) hInd, integral_const, probReal_univ,
      integral_indicator_const _ hA, smul_eq_mul, smul_eq_mul, one_mul, mul_comm (μ.real A) M]
  rw [integral_map hX.aemeasurable hF.aestronglyMeasurable,
    integral_map hY.aemeasurable hF.aestronglyMeasurable, ← integral_sub (hFi hX) (hFi hY)]
  calc
    _ ≤ ∫ ω, |f (X ω) - f (Y ω)| ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun ω ↦ f (X ω) - f (Y ω))
    _ ≤ ∫ ω, (L : ℝ) * δ + A.indicator (fun _ ↦ M) ω ∂μ :=
      integral_mono hi' ((integrable_const ((L : ℝ) * δ)).add hInd) hf
    _ = _ := hCalc

/-- Uniform truncation in probability for the laws of the sequence and
its proposed limit, plus the weak limit at each truncation, gives the
full weak limit. -/
theorem tendstoInDistribution_of_uniform_truncations_dist
    {Ω Ψ T : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ]
    [PseudoMetricSpace T] [MeasurableSpace T] [OpensMeasurableSpace T]
    [SecondCountableTopology T] [Inhabited T]
    {P : ℕ → Measure Ω} [∀ n, IsProbabilityMeasure (P n)]
    {Q : Measure Ψ} [IsProbabilityMeasure Q]
    {X : ℕ → Ω → T} {Y : Ψ → T}
    {Xcut : ℕ → ℕ → Ω → T} {Ycut : ℕ → Ψ → T}
    (hX : ∀ n, Measurable (X n)) (hY : Measurable Y)
    (hXcut : ∀ R n, Measurable (Xcut R n)) (hYcut : ∀ R, Measurable (Ycut R))
    (hCut : ∀ R, TendstoInDistribution (Xcut R) atTop (Ycut R) P Q)
    (hErr : ∀ δ > (0 : ℝ), ∀ η > (0 : ℝ), ∃ R,
      (∀ᶠ n in atTop, (P n).real {ω | δ ≤ dist (X n ω) (Xcut R n ω)} ≤ η) ∧
      Q.real {ω | δ ≤ dist (Ycut R ω) (Y ω)} ≤ η) :
    TendstoInDistribution X atTop Y P Q := by
  refine ⟨fun n ↦ (hX n).aemeasurable, hY.aemeasurable, ?_⟩
  refine (tendsto_iff_forall_lipschitz_integral_tendsto
    (μs := fun n ↦ (⟨(P n).map (X n), Measure.isProbabilityMeasure_map (hX n).aemeasurable⟩ :
      ProbabilityMeasure T))
    (μ := ⟨Q.map Y, Measure.isProbabilityMeasure_map hY.aemeasurable⟩)).mpr ?_
  rintro f ⟨M, hM⟩ ⟨L, hL⟩
  let I (n : ℕ) := ∫ x, f x ∂(P n).map (X n)
  let J := ∫ x, f x ∂Q.map Y
  change Tendsto I atTop (𝓝 J)
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hM₀ : 0 ≤ M := by simpa using hM (default : T) default
  let a := 1 + (L : ℝ) + M
  have ha : 0 < a := by dsimp [a]; positivity
  let δ := ε / (8 * a)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨R, hXR, hYR⟩ := hErr δ hδ δ hδ
  let IC (n : ℕ) := ∫ x, f x ∂(P n).map (Xcut R n)
  let JC := ∫ x, f x ∂Q.map (Ycut R)
  have hIC : Tendsto IC atTop (𝓝 JC) :=
    tendsto_iff_forall_lipschitz_integral_tendsto.mp (hCut R).tendsto f ⟨M, hM⟩ ⟨L, hL⟩
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hIC (ε / 2) (by positivity)
  obtain ⟨N', hN'⟩ := eventually_atTop.mp hXR
  refine ⟨max N N', fun n hn ↦ ?_⟩
  have h1 : dist (I n) (IC n) ≤ (L : ℝ) * δ + M * δ := by
    rw [Real.dist_eq]
    exact (integral_lipschitz_map_sub_le hL hM (hX n) (hXcut R n) hδ.le).trans
      (add_le_add_right (mul_le_mul_of_nonneg_left (hN' n ((le_max_right _ _).trans hn)) hM₀) _)
  have h3 : dist JC J ≤ (L : ℝ) * δ + M * δ := by
    rw [Real.dist_eq]
    exact (integral_lipschitz_map_sub_le hL hM (hYcut R) hY hδ.le).trans
      (add_le_add_right (mul_le_mul_of_nonneg_left hYR hM₀) _)
  have haδ : a * δ = ε / 8 := by
    dsimp [δ]
    field_simp [ha.ne']
  have hcalc : (L : ℝ) * δ + M * δ ≤ ε / 8 := by
    rw [← haδ]
    dsimp [a]
    nlinarith
  have h2 := hN n ((le_max_left _ _).trans hn)
  have ht := (dist_triangle (I n) (IC n) J).trans
    (add_le_add_right (dist_triangle (IC n) JC J) (dist (I n) (IC n)))
  linarith [h1.trans hcalc, h3.trans hcalc]

/-- Scalar form of the uniform truncation criterion. -/
theorem tendstoInDistribution_of_uniform_truncations
    {Ω Ψ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ]
    {P : ℕ → Measure Ω} [∀ n, IsProbabilityMeasure (P n)]
    {Q : Measure Ψ} [IsProbabilityMeasure Q]
    {X : ℕ → Ω → ℝ} {Y : Ψ → ℝ}
    {Xcut : ℕ → ℕ → Ω → ℝ} {Ycut : ℕ → Ψ → ℝ}
    (hX : ∀ n, Measurable (X n)) (hY : Measurable Y)
    (hXcut : ∀ R n, Measurable (Xcut R n)) (hYcut : ∀ R, Measurable (Ycut R))
    (hCut : ∀ R, TendstoInDistribution (Xcut R) atTop (Ycut R) P Q)
    (hErr : ∀ δ > (0 : ℝ), ∀ η > (0 : ℝ), ∃ R,
      (∀ᶠ n in atTop, (P n).real {ω | δ ≤ |X n ω - Xcut R n ω|} ≤ η) ∧
      Q.real {ω | δ ≤ |Ycut R ω - Y ω|} ≤ η) :
    TendstoInDistribution X atTop Y P Q :=
  tendstoInDistribution_of_uniform_truncations_dist hX hY hXcut hYcut hCut
    (by simpa only [Real.dist_eq] using hErr)

end Certificate

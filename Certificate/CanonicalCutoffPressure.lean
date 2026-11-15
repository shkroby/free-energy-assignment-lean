import Certificate.AssignmentCutoffPressure
import Certificate.CanonicalBetheLimit
import Certificate.CanonicalCutoffLimit

/-! Transfer from the cutoff local vacancy profile to the original Bethe limit. -/

open Filter MeasureTheory Set
open scoped Topology

namespace Certificate.CanonicalTree

private theorem measurable_depthFor_logFugacity {K : ℝ → ℝ} (hK : Measurable K)
    (d : ℝ) (n : ℕ) (v : Vertex) :
    Measurable (fun p : ℝ × Environment => depthFor K d (Real.exp p.1) n v p.2) := by
  induction n generalizing v with
  | zero => exact measurable_const.prodMk (Real.measurable_exp.comp measurable_fst).inv
  | succ n ih =>
    have hz : Measurable (fun p : ℝ × Environment => Real.exp p.1) :=
      Real.measurable_exp.comp measurable_fst
    have hw (i : ℕ) : Measurable (fun p : ℝ × Environment => weightFor K d p.2 v i) := by
      apply hK.comp
      unfold arrivalLength
      fun_prop
    unfold depthFor TreeBoundary.bounds TreeBoundary.update
    exact ((hz.add (Measurable.tsum fun i => (hw i).mul (ih (child v i)).snd)).inv).prodMk
      ((hz.add (Measurable.tsum fun i => (hw i).mul (ih (child v i)).fst)).inv)

noncomputable def expectedCutoffVacancy (β d R t : ℝ) : ℝ :=
  ∫ ω, Real.exp t * lowerFor (cutoffKernel β R) d (Real.exp t) [] ω ∂law

theorem measurable_expectedCutoffVacancy (β d R : ℝ) :
    Measurable (expectedCutoffVacancy β d R) := by
  let : IsProbabilityMeasure law := isProbabilityMeasure_law
  have h : Measurable (fun p : ℝ × Environment =>
      lowerFor (cutoffKernel β R) d (Real.exp p.1) [] p.2) :=
    Measurable.iSup fun k => (measurable_depthFor_logFugacity (measurable_cutoffKernel β R) d k []).fst
  exact ((Real.measurable_exp.comp measurable_fst).mul h).stronglyMeasurable.integral_prod_right'.measurable

private theorem ae_cutoffVacancy_deficit_le {β d : ℝ} (hβ : 0 < β) (hd : 0 < d) (R t : ℝ) :
    ∀ᵐ ω ∂law, 1 - Real.exp t * lowerFor (cutoffKernel β R) d (Real.exp t) [] ω ∈
      Icc 0 (Real.exp (-2*t) * ∑' i, weight β d ω [] i) := by
  let z := Real.exp t
  let K := cutoffKernel β R
  have hz : 0 < z := Real.exp_pos t
  have h₀ := cutoffKernel_nonneg β R
  filter_upwards [ae_boundary_limitsFor hz h₀ (ae_summable_cutoffKernel hβ hd R),
    ae_summable_weight hβ hd] with ω hrec hw
  let f (i : ℕ) := weightFor K d ω [] i * upperFor K d z (child [] i) ω
  let S := ∑' i, f i
  have hF₀ (i : ℕ) : 0 ≤ f i := mul_nonneg (h₀ _)
    ((hrec (child [] i)).2.2.1.le.trans (hrec (child [] i)).2.2.2.1)
  have hF₁ (i : ℕ) : f i ≤ weight β d ω [] i * z⁻¹ := by
    have hk : weightFor K d ω [] i ≤ weight β d ω [] i := by
      unfold weightFor K cutoffKernel weight
      split
      · rfl
      · positivity
    have hb := hrec (child [] i)
    exact mul_le_mul hk hb.2.2.2.2.1 (hb.2.2.1.le.trans hb.2.2.2.1) (weight_nonneg β d ω [] i)
  have hS₀ : 0 ≤ S := tsum_nonneg hF₀
  have hsum : S ≤ (∑' i, weight β d ω [] i) * z⁻¹ := by
    rw [← tsum_mul_right]
    exact (Summable.of_nonneg_of_le hF₀ hF₁ ((hw []).mul_right _)).tsum_le_tsum hF₁ ((hw []).mul_right _)
  have hD : 0 < z + S := add_pos_of_pos_of_nonneg hz hS₀
  rw [(hrec []).2.2.2.2.2.1]
  change (1 - z * (z + S)⁻¹) ∈ Icc 0 (Real.exp (-2*t) * ∑' i, weight β d ω [] i)
  have heq : (1 - z * (z + S)⁻¹) = S / (z + S) := by
    field_simp [hD.ne']
    ring
  rw [heq]
  refine ⟨div_nonneg hS₀ hD.le, ?_⟩
  have hh := div_le_div_of_nonneg_left hS₀ hz (le_add_of_nonneg_right hS₀)
  have hupper := mul_le_mul_of_nonneg_right hsum (inv_nonneg.mpr hz.le)
  change S / (z+S) ≤ _
  refine hh.trans ?_
  rw [div_eq_mul_inv]
  refine hupper.trans_eq ?_
  change (∑' i, weight β d ω [] i) * (Real.exp t)⁻¹ * (Real.exp t)⁻¹ =
    Real.exp (-2*t) * (∑' i, weight β d ω [] i)
  rw [mul_assoc, ← Real.exp_neg, ← Real.exp_add, show -t + -t = -2*t by ring, mul_comm]

private theorem bound_expectedCutoffVacancy_deficit {β d : ℝ} (hβ : 0 < β) (hd : 0 < d) (R t : ℝ) :
    ‖1 - expectedCutoffVacancy β d R t‖ ≤
      Real.exp (-2*t) * ∫ ω, (∑' i, weight β d ω [] i) ∂law := by
  let : IsProbabilityMeasure law := isProbabilityMeasure_law
  let z := Real.exp t
  let K := cutoffKernel β R
  have hz : 0 < z := Real.exp_pos t
  have hi : Integrable (fun ω => z * lowerFor K d z [] ω) law := by
    refine (integrable_const (1 : ℝ)).mono'
      (measurable_const.mul (measurable_lowerFor (measurable_cutoffKernel β R) d z [])).aestronglyMeasurable ?_
    filter_upwards [ae_boundary_limitsFor hz (cutoffKernel_nonneg β R)
      (ae_summable_cutoffKernel hβ hd R)] with ω h
    have hb := h []
    rw [Real.norm_of_nonneg (mul_nonneg hz.le hb.2.2.1.le)]
    exact (mul_le_mul_of_nonneg_left (hb.2.2.2.1.trans hb.2.2.2.2.1) hz.le).trans_eq
      (mul_inv_cancel₀ hz.ne')
  have heq : 1 - expectedCutoffVacancy β d R t = ∫ ω, 1 - z * lowerFor K d z [] ω ∂law := by
    rw [integral_sub (integrable_const (1 : ℝ)) hi, integral_const]
    simp [expectedCutoffVacancy, K, z]
  rw [heq, ← integral_const_mul]
  refine norm_integral_le_of_norm_le ((integrable_root_totalWeight hβ hd).const_mul _) ?_
  filter_upwards [ae_cutoffVacancy_deficit_le hβ hd R t] with ω h
  rw [Real.norm_of_nonneg h.1]
  exact h.2

theorem tendsto_expectedCutoffVacancy {β d : ℝ} (hβ : 0 < β) (hd : 0 < d) (t : ℝ) :
    Tendsto (fun R : ℕ => expectedCutoffVacancy β d R t) atTop (𝓝 (expectedVacancy β d t)) := by
  unfold expectedCutoffVacancy expectedVacancy
  simp_rw [integral_const_mul]
  exact (tendsto_expectation_cutoff_root hβ hd (Real.exp_pos t)).const_mul (Real.exp t)

/-- Removing the tree cutoff in the integrated local profile is justified by an
integrable envelope, uniformly in the finite cutoff. -/
theorem tendsto_cutoffVacancy_pressure_integral {β d : ℝ} (hβ : 0 < β) (hd : 0 < d) (t : ℝ) :
    Tendsto (fun R : ℕ => 2 * t + 2 * ∫ s in Ioi t, (1 - expectedCutoffVacancy β d R s))
      atTop (𝓝 (softBethePressure β d t)) := by
  rw [softBethePressure_eq_integral hβ hd t]
  let W := ∫ ω, (∑' i, weight β d ω [] i) ∂law
  have hi : IntegrableOn (fun s => Real.exp (-2*s) * W) (Ioi t) :=
    (integrableOn_exp_mul_Ioi (show (-2 : ℝ) < 0 by norm_num) t).mul_const W
  have ht := tendsto_integral_of_dominated_convergence (μ := volume.restrict (Ioi t))
    (fun s => Real.exp (-2*s) * W)
    (fun R : ℕ => (measurable_const.sub (measurable_expectedCutoffVacancy β d R)).aestronglyMeasurable)
    hi (fun R => Eventually.of_forall fun s => bound_expectedCutoffVacancy_deficit hβ hd R s)
    (Eventually.of_forall fun s => (tendsto_expectedCutoffVacancy hβ hd s).const_sub 1)
  exact (ht.const_mul 2).const_add (2*t)

/-- The actual expected soft pressure equals the Bethe pressure when the
finite graph cutoff deficits converge to the canonical cutoff profiles. -/
theorem tendsto_expected_softAssignmentPressure_to_bethe_of_cutoff_local
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {β d κ : ℝ}
    (hβ : 0 < β) (hd : 0 < d) (hκ : 0 < κ) (hμ : SmallCostTail μ κ d) (t : ℝ)
    (hlocal : ∀ R : ℕ, ∀ᵐ s ∂volume.restrict (Ioi t),
      Tendsto (fun n => ∫ C, (cutoffAssignmentGraph β d κ R n C).deficit s / n ∂iidCosts μ)
        atTop (𝓝 (2 * (1 - expectedCutoffVacancy β d R s)))) :
    Tendsto (fun n => ∫ C, softAssignmentPressure β d κ t n C ∂iidCosts μ) atTop
      (𝓝 (bethePressure β d (law.map (lower β d (Real.exp t) [])))) := by
  rw [← softBethePressure_eq_bethePressure hβ hd t]
  exact tendsto_expected_softAssignmentPressure_of_cutoff_limits hβ hd hκ hμ
    (fun R => tendsto_expected_cutoffAssignmentPressure_of_local hβ hd hκ hμ R t _ (hlocal R))
    (tendsto_cutoffVacancy_pressure_integral hβ hd t)

/-- The cutoff route also identifies the almost-sure pressure limit on the
full finite assignment graphs. -/
theorem ae_monomerPressure_tendsto_bethe_of_cutoff_local
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {β d κ : ℝ}
    (hβ : 0 < β) (hd : 0 < d) (hκ : 0 < κ) (hμ : SmallCostTail μ κ d) {z : ℝ} (hz : 0 < z)
    (hlocal : ∀ R : ℕ, ∀ᵐ s ∂volume.restrict (Ioi (Real.log z)),
      Tendsto (fun n => ∫ C, (cutoffAssignmentGraph β d κ R n C).deficit s / n ∂iidCosts μ)
        atTop (𝓝 (2 * (1 - expectedCutoffVacancy β d R s)))) :
    ∀ᵐ C ∂iidCosts μ, Tendsto (fun n => Completion.monomerPressure β d κ n C z) atTop
      (𝓝 (bethePressure β d (law.map (lower β d z [])))) := by
  have ht := tendsto_expected_softAssignmentPressure_to_bethe_of_cutoff_local hβ hd hκ hμ
    (Real.log z) hlocal
  have ha := ae_tendsto_softAssignmentPressure_of_expected hμ.1 hβ.le d κ (Real.log z) hκ.le ht
  simpa only [softAssignmentPressure_eq_monomerPressure, Real.exp_log hz] using ha

/-- The cutoff route reaches the hard pressure using the zero-fugacity limit
of the canonical Bethe marginal laws. -/
theorem hard_pressure_formula_of_canonical_cutoff_bethe_limits
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {β d κ : ℝ}
    (hβ : 0 < β) (hd : 0 < d) (hκ : 0 < κ) (hμ : SmallCostTail μ κ d)
    (hlocal : ∀ (t : ℝ) (R : ℕ), ∀ᵐ s ∂volume.restrict (Ioi t),
      Tendsto (fun n => ∫ C, (cutoffAssignmentGraph β d κ R n C).deficit s / n ∂iidCosts μ)
        atTop (𝓝 (2 * (1 - expectedCutoffVacancy β d R s))))
    (H : Measure ℝ)
    (hBethe : Tendsto (fun z => bethePressure β d (law.map (lower β d z [])))
      (𝓝[>] (0 : ℝ)) (𝓝 (bethePressure β d H))) :
    (∀ᵐ C ∂iidCosts μ, Tendsto (fun n => pressure β d κ n C) atTop (𝓝 (bethePressure β d H))) ∧
      ((∃ q : ℝ, 0 < q ∧ Integrable (fun c => c ^ q) μ) →
        (∀ᶠ n in atTop, Integrable (pressure β d κ n) (iidCosts μ)) ∧
        Tendsto (fun n => ∫ C, |pressure β d κ n C - bethePressure β d H| ∂iidCosts μ)
          atTop (𝓝 0)) := by
  have hp := ae_pressure_limit_of_positive_fugacity_limit hβ hd hκ hμ
    (fun z hz => ae_monomerPressure_tendsto_bethe_of_cutoff_local hβ hd hκ hμ hz (hlocal (Real.log z)))
    hBethe
  refine ⟨hp, ?_⟩
  rintro ⟨q, hq, hM⟩
  exact ⟨eventually_integrable_pressure hβ hd hκ hq hμ hM,
    pressure_L1_of_ae_limit hβ hd hκ hq hμ hM hp⟩

end Certificate.CanonicalTree

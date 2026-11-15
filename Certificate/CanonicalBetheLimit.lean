import Certificate.CanonicalBetheExchange
import Certificate.PressureFromLocal

/-! Identification with the manuscript's marginal-law Bethe formula. -/

open Filter MeasureTheory Set
open scoped Topology

namespace Certificate.CanonicalTree

theorem softBethePressure_eq_bethePressure {β d : ℝ}
    (hβ : 0 < β) (hd : 0 < d) (t : ℝ) :
    softBethePressure β d t = bethePressure β d (law.map (lower β d (Real.exp t) [])) := by
  let : IsProbabilityMeasure law := isProbabilityMeasure_law
  let : SigmaFinite (intensity d) := sigmaFinite_intensity d
  let H := lower β d (Real.exp t) []
  have hH : Measurable H := measurable_lower β d (Real.exp t) []
  have hp : Measurable (Prod.map H H) := hH.prodMap hH
  have hmap : (law.prod law).map (Prod.map H H) = (law.map H).prod (law.map H) :=
    (Measure.map_prod_map _ _ hH hH).symm
  unfold softBethePressure bethePressure
  rw [integral_map hH.aemeasurable Real.measurable_log.aestronglyMeasurable]
  rw [show betheEdgeMeasure d = (intensity d).prod (law.prod law) from rfl,
    integral_prod _ (integrable_edgeLogTerm hβ hd t)]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  let g (p : ℝ × ℝ) := Real.log (1 + Real.exp (-β * x) * p.1 * p.2)
  have hg : Measurable g := by
    dsimp only [g]
    exact (measurable_const.add ((measurable_const.mul measurable_fst).mul measurable_snd)).log
  change (∫ p, g (Prod.map H H p) ∂law.prod law) =
    ∫ p, g p ∂(law.map H).prod (law.map H)
  rw [← hmap, integral_map hp.aemeasurable hg.aestronglyMeasurable]

/-- The almost-sure finite graph pressure limit has the canonical Bethe expression
whenever the local vacancy profile converges. -/
theorem ae_monomerPressure_tendsto_bethe_of_local {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {β d κ : ℝ} (hβ : 0 < β) (hd : 0 < d) (hκ : 0 < κ) (hμ : SmallCostTail μ κ d)
    (hlocal : ∀ t : ℝ, ∀ᵐ s ∂volume.restrict (Ioi t),
      Tendsto (fun n : ℕ => ∫ C, (assignmentGraph β d κ n C).deficit s / n ∂iidCosts μ)
        atTop (𝓝 (2 * (1 - expectedVacancy β d s))))
    {z : ℝ} (hz : 0 < z) :
    ∀ᵐ C ∂iidCosts μ, Tendsto (fun n => Completion.monomerPressure β d κ n C z)
      atTop (𝓝 (bethePressure β d (law.map (lower β d z [])))) := by
  have h := ae_monomerPressure_limit_of_local_deficit_limits hβ hd hκ hμ
    (expectedVacancy β d) hlocal hz
  rw [← softBethePressure_eq_integral hβ hd (Real.log z),
    softBethePressure_eq_bethePressure hβ hd, Real.exp_log hz] at h
  exact h

/-- The hard pressure limit has the manuscript's Bethe expression once the local
vacancy and the small-fugacity Bethe marginals have their stated limits. -/
theorem hard_pressure_formula_of_canonical_bethe_limits {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {β d κ : ℝ} (hβ : 0 < β) (hd : 0 < d) (hκ : 0 < κ) (hμ : SmallCostTail μ κ d)
    (hlocal : ∀ t : ℝ, ∀ᵐ s ∂volume.restrict (Ioi t),
      Tendsto (fun n : ℕ => ∫ C, (assignmentGraph β d κ n C).deficit s / n ∂iidCosts μ)
        atTop (𝓝 (2 * (1 - expectedVacancy β d s))))
    (H : Measure ℝ)
    (hBethe : Tendsto (fun z => bethePressure β d (law.map (lower β d z [])))
      (𝓝[>] (0 : ℝ)) (𝓝 (bethePressure β d H))) :
    (∀ᵐ C ∂iidCosts μ, Tendsto (fun n => pressure β d κ n C) atTop (𝓝 (bethePressure β d H))) ∧
      ((∃ q : ℝ, 0 < q ∧ Integrable (fun c => c ^ q) μ) →
        (∀ᶠ n in atTop, Integrable (pressure β d κ n) (iidCosts μ)) ∧
        Tendsto (fun n => ∫ C, |pressure β d κ n C - bethePressure β d H| ∂iidCosts μ)
          atTop (𝓝 0)) := by
  refine hard_pressure_formula_of_local_deficit_limits hβ hd hκ hμ
    (expectedVacancy β d) hlocal H ?_
  refine hBethe.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [← softBethePressure_eq_integral hβ hd (Real.log z),
    softBethePressure_eq_bethePressure hβ hd, Real.exp_log hz]

end Certificate.CanonicalTree

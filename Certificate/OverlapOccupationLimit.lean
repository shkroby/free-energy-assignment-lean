import Certificate.OverlapOccupation
import Certificate.CanonicalHardBethe

/-! The inserted-edge overlap passes from the positive-fugacity laws to the hard law. -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology BoundedContinuousFunction

namespace Certificate

private noncomputable def clippedSquare (β x : ℝ) (p : ℝ × ℝ) : ℝ :=
  overlapEdgeSquare β x (max p.1 0, max p.2 0)

private theorem clippedSquare_mem (β x : ℝ) (p : ℝ × ℝ) :
    clippedSquare β x p ∈ Icc (0:ℝ) 1 := by
  let w := Real.exp (-β * x) * max p.1 0 * max p.2 0
  have hw : 0 ≤ w := by positivity
  change 0 ≤ (w / (1+w))^2 ∧ (w / (1+w))^2 ≤ 1
  exact ⟨sq_nonneg _, pow_le_one₀ (by positivity)
    ((div_le_one (by positivity)).mpr (le_add_of_nonneg_left zero_le_one))⟩

private theorem continuous_clippedSquare (β x : ℝ) : Continuous (clippedSquare β x) := by
  unfold clippedSquare overlapEdgeSquare edgeOccupation
  have hw : Continuous (fun p : ℝ × ℝ => Real.exp (-β*x) * max p.1 0 * max p.2 0) := by fun_prop
  exact (hw.div (continuous_const.add hw) (fun p =>
    (add_pos_of_pos_of_nonneg zero_lt_one
      (mul_nonneg (mul_nonneg (Real.exp_nonneg _) (le_max_right _ _)) (le_max_right _ _))).ne')).pow 2

private theorem integral_clippedSquare_eq (β x : ℝ) (H : Measure ℝ) [IsProbabilityMeasure H]
    (hH : ∀ᵐ p ∂H, 0 ≤ p) :
    (∫ p, overlapEdgeSquare β x p ∂H.prod H) = ∫ p, clippedSquare β x p ∂H.prod H := by
  have h₁ := (measurePreserving_fst (μ := H) (ν := H)).quasiMeasurePreserving.tendsto_ae.eventually hH
  have h₂ := (measurePreserving_snd (μ := H) (ν := H)).quasiMeasurePreserving.tendsto_ae.eventually hH
  apply integral_congr_ae
  filter_upwards [h₁,h₂] with p hp hq
  simp only [clippedSquare, max_eq_left hp, max_eq_left hq, Prod.eta]

private theorem integral_clippedSquare_le (β x : ℝ) (H : Measure ℝ) [IsProbabilityMeasure H] :
    (∫ p, clippedSquare β x p ∂H.prod H) ≤
      Real.exp (-β*x/2) + 2 * H.real (Ioi (Real.exp (β*(x/4)))) := by
  let τ := Real.exp (β*(x/4))
  let U : Set (ℝ × ℝ) := Prod.fst ⁻¹' Ioi τ ∪ Prod.snd ⁻¹' Ioi τ
  let a := Real.exp (-β*x/2)
  have ht : 0 < τ := Real.exp_pos _
  have hU : MeasurableSet U :=
    (measurable_fst measurableSet_Ioi).union (measurable_snd measurableSet_Ioi)
  let f := clippedSquare β x
  have hF : Integrable f (H.prod H) := Integrable.of_bound (continuous_clippedSquare β x).measurable.aestronglyMeasurable 1
    (Eventually.of_forall fun p => by
      rw [Real.norm_of_nonneg (clippedSquare_mem β x p).1]
      exact (clippedSquare_mem β x p).2)
  have hI : Integrable (U.indicator (fun _ : ℝ × ℝ => (1:ℝ))) (H.prod H) :=
    (integrable_const _).indicator hU
  have hbound (p : ℝ × ℝ) : f p ≤ a + U.indicator (fun _ => (1:ℝ)) p := by
    by_cases hp : p ∈ U
    · rw [indicator_of_mem hp]
      exact (clippedSquare_mem β x p).2.trans (le_add_of_nonneg_left (Real.exp_nonneg _))
    · rw [indicator_of_notMem hp, add_zero]
      change ¬(τ < p.1 ∨ τ < p.2) at hp
      have h₁ : p.1 ≤ τ := le_of_not_gt (fun h => hp (Or.inl h))
      have h₂ : p.2 ≤ τ := le_of_not_gt (fun h => hp (Or.inr h))
      let w := Real.exp (-β * x) * max p.1 0 * max p.2 0
      have hw : 0 ≤ w := by positivity
      have hwa : w ≤ a := by
        calc
          _ ≤ Real.exp (-β*x) * τ * τ :=
            mul_le_mul (mul_le_mul_of_nonneg_left (max_le h₁ ht.le) (Real.exp_nonneg _))
              (max_le h₂ ht.le) (le_max_right _ _) (by positivity)
          _ = _ := by dsimp only [τ, a]; rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      have hw' : 0 ≤ w / (1+w) := by positivity
      have hw'' : w / (1+w) ≤ 1 :=
        (div_le_one (by positivity)).mpr (le_add_of_nonneg_left zero_le_one)
      change (w / (1+w))^2 ≤ a
      refine (show (w / (1+w))^2 ≤ w / (1+w) by nlinarith [mul_nonneg hw' (sub_nonneg.mpr hw'')]).trans ?_
      exact (div_le_self hw (le_add_of_nonneg_right hw)).trans hwa
  calc
    _ ≤ ∫ p, a + U.indicator (fun _ => (1:ℝ)) p ∂H.prod H :=
      integral_mono hF ((integrable_const _).add hI) hbound
    _ = a + (H.prod H).real U := by
      rw [integral_add (integrable_const _) hI, integral_const, probReal_univ, one_smul,
        integral_indicator_const _ hU, smul_eq_mul, mul_one]
    _ ≤ _ := by
      have hp₁ : (H.prod H).real (Prod.fst ⁻¹' Ioi τ) = H.real (Ioi τ) := by
        unfold Measure.real
        rw [← Measure.map_apply measurable_fst measurableSet_Ioi,
          (measurePreserving_fst (μ := H) (ν := H)).map_eq]
      have hp₂ : (H.prod H).real (Prod.snd ⁻¹' Ioi τ) = H.real (Ioi τ) := by
        unfold Measure.real
        rw [← Measure.map_apply measurable_snd measurableSet_Ioi,
          (measurePreserving_snd (μ := H) (ν := H)).map_eq]
      have h := measureReal_union_le (μ := H.prod H) (Prod.fst ⁻¹' Ioi τ) (Prod.snd ⁻¹' Ioi τ)
      rw [hp₁, hp₂, ← two_mul] at h
      exact add_le_add_right h a

/-- Pointwise convergence of the squared occupation integral under weak
convergence of nonnegative message laws. -/
theorem tendsto_integral_overlapEdgeSquare {β x : ℝ} {H : ℕ → ProbabilityMeasure ℝ}
    {H₀ : ProbabilityMeasure ℝ}
    (hLaw : Tendsto H atTop (𝓝 H₀))
    (h : ∀ n, ∀ᵐ r ∂(H n : Measure ℝ), 0 ≤ r)
    (h₀ : ∀ᵐ r ∂(H₀ : Measure ℝ), 0 ≤ r) :
    Tendsto (fun n => ∫ p, overlapEdgeSquare β x p ∂(H n : Measure ℝ).prod (H n : Measure ℝ))
      atTop (𝓝 (∫ p, overlapEdgeSquare β x p ∂(H₀ : Measure ℝ).prod (H₀ : Measure ℝ))) := by
  simp_rw [integral_clippedSquare_eq β x _ (h _)]
  rw [integral_clippedSquare_eq β x _ h₀]
  let test : (ℝ × ℝ) →ᵇ ℝ :=
    BoundedContinuousFunction.mkOfBound ⟨_, continuous_clippedSquare β x⟩ 1
      (fun a b => by
        change dist (clippedSquare β x a) (clippedSquare β x b) ≤ 1
        rw [Real.dist_eq, abs_le]
        have ha := clippedSquare_mem β x a
        have hb := clippedSquare_mem β x b
        exact ⟨by linarith [ha.1,hb.2], by linarith [ha.2,hb.1]⟩)
  have hp : Tendsto (fun n => (H n).prod (H n)) atTop (𝓝 (H₀.prod H₀)) :=
    ProbabilityMeasure.continuous_prod.continuousAt.tendsto.comp (hLaw.prodMk_nhds hLaw)
  exact (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hp) test

namespace CanonicalTree

/-- The squared occupations have a common integrable edge bound along
positive fugacities at most one. -/
theorem tendsto_cavityOverlap_along_sequence {β d : ℝ} (hβ : 0 < β) (hd : 0 < d)
    (z : ℕ → ℝ) (hz₀ : ∀ n, 0 < z n) (hz₁ : ∀ n, z n ≤ 1)
    (H : ProbabilityMeasure ℝ) (hH : IsCavityLaw β d (H : Measure ℝ))
    (hLaw : Tendsto (fun n => softCavityProbability β d (z n)) atTop (𝓝 H)) :
    Tendsto (fun n => cavityOverlap β d (softCavityProbability β d (z n) : Measure ℝ))
      atTop (𝓝 (cavityOverlap β d (H : Measure ℝ))) := by
  let M (n : ℕ) := softCavityProbability β d (z n)
  have hs (n : ℕ) := softCavityProbability_spec hβ hd (hz₀ n)
  have hpos : ∀ᵐ r ∂(H : Measure ℝ), 0 < r :=
    (mem_ae_iff_prob_eq_one (measurableSet_Ioi (a := (0:ℝ)))).mpr hH.2.1
  have h₀ : ∀ᵐ r ∂(H : Measure ℝ), 0 ≤ r := hpos.mono fun _ h => h.le
  have hn (n : ℕ) : ∀ᵐ r ∂(M n : Measure ℝ), 0 ≤ r := (hs n).1.mono fun _ h => h.1.le
  obtain ⟨K,hK,hTail⟩ := exists_uniform_soft_log_tail hβ hd
  let c := 1 / (2 * (8:ℝ)^d)
  have hc : 0 < c := by dsimp [c]; positivity
  have hx : ∀ᵐ x ∂intensity d, 0 ≤ x := by
    unfold intensity
    exact (ae_withDensity_iff (by fun_prop)).mpr <|
      (ae_restrict_mem measurableSet_Ioi).mono (fun _ h _ => le_of_lt h)
  unfold cavityOverlap
  apply tendsto_integral_of_dominated_convergence
    (fun x => Real.exp (-β*x/2) + (2*K)*Real.exp (-c*x^d))
  · intro n
    exact ((measurable_overlapEdgeSquare β).stronglyMeasurable.integral_prod_right').aestronglyMeasurable
  · exact integrable_edge_envelope hd hβ hc
  · intro n
    filter_upwards [hx] with x hx
    have hnonneg : 0 ≤ ∫ p, overlapEdgeSquare β x p ∂(M n : Measure ℝ).prod (M n : Measure ℝ) :=
      integral_nonneg fun _ => sq_nonneg _
    rw [Real.norm_of_nonneg hnonneg, integral_clippedSquare_eq β x _ (hn n)]
    refine (integral_clippedSquare_le β x _).trans ?_
    have ht := hTail (z n) (hz₀ n) (hz₁ n) (M n : Measure ℝ)
      ((hs n).1.mono fun _ hr => ⟨hr.1.le, hr.2⟩) (hs n).2 (x/4) (by positivity)
    have ht' : (M n : Measure ℝ).real (Ioi (Real.exp (β*(x/4)))) ≤
        K * Real.exp (-((x/4/2)^d/2)) := by
      unfold Measure.real
      simpa only [ENNReal.toReal_ofReal (mul_nonneg hK.le (Real.exp_nonneg _))] using
        ENNReal.toReal_mono ENNReal.ofReal_ne_top ht
    have he : (x/4/2)^d/2 = c * x^d := by
      dsimp only [c]
      rw [show x/4/2 = x/8 by ring, Real.div_rpow hx (by norm_num)]
      ring
    rw [he] at ht'
    have ht'' := mul_le_mul_of_nonneg_left ht' (show (0:ℝ) ≤ 2 by norm_num)
    simpa only [neg_mul, mul_assoc] using add_le_add_right ht'' (Real.exp (-β*x/2))
  · exact Eventually.of_forall fun x => tendsto_integral_overlapEdgeSquare (x := x) hLaw hn h₀

/-- As the monomer factor decreases to zero, the soft inserted-edge overlaps
converge to the manuscript's hard overlap. -/
theorem tendsto_cavityOverlap_of_hard_unique {β d : ℝ} (hβ : 0 < β) (hd : 0 < d)
    (H : ProbabilityMeasure ℝ) (hH : IsCavityLaw β d (H : Measure ℝ))
    (hUnique : ∀ ν : Measure ℝ, IsCavityLaw β d ν → ν = (H : Measure ℝ)) :
    Tendsto (fun z => cavityOverlap β d (softCavityProbability β d z : Measure ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 (cavityOverlap β d (H : Measure ℝ))) := by
  have hLaw := tendsto_softCavityProbability_of_hard_unique hβ hd H hUnique
  apply tendsto_of_subseq_tendsto
  intro z hz
  obtain ⟨hzLim, hzPos⟩ := tendsto_nhdsWithin_iff.mp hz
  have hSmall : ∀ᶠ n in atTop, 0 < z n ∧ z n ≤ 1 := by
    filter_upwards [hzPos, hzLim.eventually (Iio_mem_nhds (zero_lt_one : (0:ℝ) < 1))]
      with n hn hlt
    exact ⟨hn, hlt.le⟩
  obtain ⟨N,hN⟩ := eventually_atTop.mp hSmall
  let z' (n : ℕ) := z (n+N)
  exact ⟨fun n => n+N, tendsto_cavityOverlap_along_sequence hβ hd z'
    (fun n => (hN _ (Nat.le_add_left N n)).1) (fun n => (hN _ (Nat.le_add_left N n)).2)
    H hH (hLaw.comp (hz.comp (tendsto_add_atTop_nat N)))⟩

end CanonicalTree
end Certificate

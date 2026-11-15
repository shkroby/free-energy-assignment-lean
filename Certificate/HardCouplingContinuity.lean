import Certificate.CavityFinitePrefix
import Certificate.CavityCouplingCompact
import Certificate.ArrivalHardCoupling
import Certificate.WeakTruncation
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Topology.Sequences

/-!
# Weak continuity of the canonical hard coupling update

The update uses the same spacings for both coordinates. A continuous
finite-prefix approximation converges in probability uniformly over
the coupling set because its two coordinate errors have fixed laws.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

namespace Certificate

/-- The bivariate hard recursion on canonical exponential arrivals. -/
noncomputable def hardCouplingProbability (β d : ℝ)
    (ρ : ProbabilityMeasure (ℝ × ℝ)) : ProbabilityMeasure (ℝ × ℝ) := by
  let P := markedArrivalSequenceLaw (ρ : Measure (ℝ × ℝ))
  let : IsProbabilityMeasure P := isProbabilityMeasure_markedArrivalSequenceLaw _
  exact ⟨P.map (pairedHardRoot β d),
    Measure.isProbabilityMeasure_map (measurable_pairedHardRoot β d).aemeasurable⟩

private theorem map_hardCouplingProbability_coord {β d : ℝ}
    (ρ : ProbabilityMeasure (ℝ × ℝ)) (f : ℝ × ℝ → ℝ)
    (hf : Measurable f)
    (hroot : f ∘ pairedHardRoot β d =
      arrivalSoftOutput β d 0 ∘ (fun ω : PairedArrivalConfiguration => (ω.1, fun i => f (ω.2 i))))
    (h : IsCavityLaw β d ((ρ : Measure (ℝ × ℝ)).map f)) :
    ((hardCouplingProbability β d ρ : ProbabilityMeasure (ℝ × ℝ)) : Measure (ℝ × ℝ)).map f =
      (ρ : Measure (ℝ × ℝ)).map f := by
  change ((markedArrivalSequenceLaw (ρ : Measure (ℝ × ℝ))).map (pairedHardRoot β d)).map f = _
  rw [Measure.map_map hf (measurable_pairedHardRoot β d), hroot,
    ← Measure.map_map (measurable_arrivalSoftOutput β d 0)
      (markedArrival_projection (ρ : Measure (ℝ × ℝ)) f hf).measurable,
    (markedArrival_projection (ρ : Measure (ℝ × ℝ)) f hf).map_eq]
  exact map_arrivalSoftOutput_zero_of_IsCavityLaw h

private theorem pairedHardRoot_fst (β d : ℝ) (ω : PairedArrivalConfiguration) :
    (pairedHardRoot β d ω).1 = arrivalSoftOutput β d 0 (firstArrivalConfiguration ω) := by
  change (arrivalWeightedSum β d (firstArrivalConfiguration ω)).toReal⁻¹ =
    (0 + (arrivalWeightedSum β d (firstArrivalConfiguration ω)).toReal)⁻¹
  rw [zero_add]

private theorem pairedHardRoot_snd (β d : ℝ) (ω : PairedArrivalConfiguration) :
    (pairedHardRoot β d ω).2 = arrivalSoftOutput β d 0 (secondArrivalConfiguration ω) := by
  change (arrivalWeightedSum β d (secondArrivalConfiguration ω)).toReal⁻¹ =
    (0 + (arrivalWeightedSum β d (secondArrivalConfiguration ω)).toReal)⁻¹
  rw [zero_add]

/-- At fixed hard marginal laws the bivariate recursion maps the
coupling set to itself. -/
theorem hardCouplingProbability_mem_couplingLaws {β d : ℝ}
    {μ ν : ProbabilityMeasure ℝ} (hμ : IsCavityLaw β d (μ : Measure ℝ))
    (hν : IsCavityLaw β d (ν : Measure ℝ))
    {ρ : ProbabilityMeasure (ℝ × ℝ)} (hρ : ρ ∈ couplingLaws μ ν) :
    hardCouplingProbability β d ρ ∈ couplingLaws μ ν := by
  have hf : (ρ : Measure (ℝ × ℝ)).map Prod.fst = μ := congrArg Subtype.val hρ.1
  have hs : (ρ : Measure (ℝ × ℝ)).map Prod.snd = ν := congrArg Subtype.val hρ.2
  refine ⟨Subtype.ext ?_, Subtype.ext ?_⟩
  · change ((hardCouplingProbability β d ρ : ProbabilityMeasure (ℝ × ℝ)) : Measure (ℝ × ℝ)).map
      Prod.fst = (μ : Measure ℝ)
    exact (map_hardCouplingProbability_coord ρ Prod.fst measurable_fst
      (funext (pairedHardRoot_fst β d)) (hf ▸ hμ)).trans hf
  · change ((hardCouplingProbability β d ρ : ProbabilityMeasure (ℝ × ℝ)) : Measure (ℝ × ℝ)).map
      Prod.snd = (ν : Measure ℝ)
    exact (map_hardCouplingProbability_coord ρ Prod.snd measurable_snd
      (funext (pairedHardRoot_snd β d)) (hs ▸ hν)).trans hs

private noncomputable def hardPrefixFloor (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)

private theorem hardPrefixFloor_pos (k : ℕ) : 0 < hardPrefixFloor k := by
  unfold hardPrefixFloor
  positivity

private noncomputable def scalarHardPrefixRoot (β d : ℝ) (k : ℕ) (ω : ArrivalConfiguration) : ℝ :=
  (max (hardPrefixFloor k) (cavityPrefixSum β d k ω))⁻¹

private theorem continuous_scalarHardPrefixRoot (β : ℝ) {d : ℝ} (hd : 0 < d) (k : ℕ) :
    Continuous (scalarHardPrefixRoot β d k) := by
  have hSum : Continuous (cavityPrefixSum β d k) := by
    unfold cavityPrefixSum
    apply continuous_finsetSum
    intro i _
    unfold cavityTerm arrivalLength
    apply Continuous.mul
    · apply Real.continuous_exp.comp
      apply continuous_const.mul
      apply (Real.continuous_rpow_const (one_div_nonneg.mpr hd.le)).comp
      exact continuous_finsetSum _ (fun j _ => (continuous_apply j).comp continuous_fst)
    · exact (continuous_apply i).comp continuous_snd
  unfold scalarHardPrefixRoot
  exact (continuous_const.max hSum).inv₀ (fun _ =>
    ((hardPrefixFloor_pos k).trans_le (le_max_left _ _)).ne')

private noncomputable def pairHardPrefixRoot (β d : ℝ) (k : ℕ) (ω : PairedArrivalConfiguration) :
    ℝ × ℝ :=
  (scalarHardPrefixRoot β d k (firstArrivalConfiguration ω),
    scalarHardPrefixRoot β d k (secondArrivalConfiguration ω))

private theorem continuous_pairHardPrefixRoot (β : ℝ) {d : ℝ} (hd : 0 < d) (k : ℕ) :
    Continuous (pairHardPrefixRoot β d k) := by
  have hf : Continuous firstArrivalConfiguration := by
    unfold firstArrivalConfiguration
    exact continuous_fst.prodMk (continuous_pi (fun i =>
      continuous_fst.comp ((continuous_apply i).comp continuous_snd)))
  have hs : Continuous secondArrivalConfiguration := by
    unfold secondArrivalConfiguration
    exact continuous_fst.prodMk (continuous_pi (fun i =>
      continuous_snd.comp ((continuous_apply i).comp continuous_snd)))
  exact ((continuous_scalarHardPrefixRoot β hd k).comp hf).prodMk
    ((continuous_scalarHardPrefixRoot β hd k).comp hs)

private def hardPairPrefixProjection (k : ℕ) (ω : PairedArrivalConfiguration) :
    (Fin k → ℝ) × (Fin k → (ℝ × ℝ)) :=
  Prod.map (fun E i => E i.val) (fun M i => M i.val) ω

private def extendHardPrefix {Y : Type*} [Zero Y] {k : ℕ} (p : Fin k → Y) (i : ℕ) : Y :=
  if h : i < k then p ⟨i, h⟩ else 0

private theorem continuous_extendHardPrefix {Y : Type*} [Zero Y] [TopologicalSpace Y] {k : ℕ} :
    Continuous (extendHardPrefix : (Fin k → Y) → (ℕ → Y)) := by
  apply continuous_pi
  intro i
  by_cases h : i < k
  · simpa only [extendHardPrefix, dif_pos h] using (continuous_apply (⟨i, h⟩ : Fin k))
  · simpa only [extendHardPrefix, dif_neg h] using
      (continuous_const : Continuous (fun _ : Fin k → Y => (0 : Y)))

private theorem scalarHardPrefixRoot_congr (β d : ℝ) (k : ℕ)
    {ω ω' : ArrivalConfiguration}
    (he : ∀ i < k, ω.1 i = ω'.1 i) (hm : ∀ i < k, ω.2 i = ω'.2 i) :
    scalarHardPrefixRoot β d k ω = scalarHardPrefixRoot β d k ω' := by
  unfold scalarHardPrefixRoot
  congr 2
  unfold cavityPrefixSum
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i < k := Finset.mem_range.mp hi
  have hsum : (∑ j ∈ Finset.range (i + 1), ω.1 j) = ∑ j ∈ Finset.range (i + 1), ω'.1 j := by
    apply Finset.sum_congr rfl
    intro j hj
    exact he j ((Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)).trans_lt hik)
  simp only [cavityTerm, arrivalLength, hsum, hm i hik]

private theorem pairHardPrefixRoot_eq_comp (β d : ℝ) (k : ℕ) :
    pairHardPrefixRoot β d k =
      (pairHardPrefixRoot β d k ∘ Prod.map extendHardPrefix extendHardPrefix) ∘
        hardPairPrefixProjection k := by
  funext ω
  apply Prod.ext <;> apply scalarHardPrefixRoot_congr
  all_goals
    intro i hi
    simp only [firstArrivalConfiguration, secondArrivalConfiguration,
      hardPairPrefixProjection, Prod.map_fst, Prod.map_snd, extendHardPrefix, dif_pos hi]

private noncomputable def hardPairPrefixProbability (k : ℕ) (ρ : ProbabilityMeasure (ℝ × ℝ)) :
    ProbabilityMeasure ((Fin k → ℝ) × (Fin k → (ℝ × ℝ))) :=
  (ProbabilityMeasure.pi (fun _ : Fin k =>
    (⟨expMeasure 1, isProbabilityMeasure_expMeasure zero_lt_one⟩ : ProbabilityMeasure ℝ))).prod
    (ProbabilityMeasure.pi (fun _ : Fin k => ρ))

private theorem map_hardPairPrefixProjection (k : ℕ) (ρ : ProbabilityMeasure (ℝ × ℝ)) :
    (markedArrivalSequenceLaw (ρ : Measure (ℝ × ℝ))).map (hardPairPrefixProjection k) =
      (hardPairPrefixProbability k ρ : Measure _) := by
  let : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure zero_lt_one
  have he : Measurable (fun (E : ℕ → ℝ) (i : Fin k) => E i.val) := by fun_prop
  have hm : Measurable (fun (M : ℕ → ℝ × ℝ) (i : Fin k) => M i.val) := by fun_prop
  unfold markedArrivalSequenceLaw exponentialSpacings hardPairPrefixProjection hardPairPrefixProbability
  rw [← Measure.map_prod_map _ _ he hm,
    Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective,
    Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective,
    Measure.infinitePi_eq_pi, Measure.infinitePi_eq_pi]
  rfl

private theorem tendstoInDistribution_pairHardPrefixRoot {β d : ℝ} (hd : 0 < d) (k : ℕ)
    {ρ : ℕ → ProbabilityMeasure (ℝ × ℝ)} {ρ₀ : ProbabilityMeasure (ℝ × ℝ)}
    (h : Tendsto ρ atTop (𝓝 ρ₀)) :
    letI (n : ℕ) : IsProbabilityMeasure (markedArrivalSequenceLaw (ρ n : Measure (ℝ × ℝ))) :=
      isProbabilityMeasure_markedArrivalSequenceLaw _
    letI : IsProbabilityMeasure (markedArrivalSequenceLaw (ρ₀ : Measure (ℝ × ℝ))) :=
      isProbabilityMeasure_markedArrivalSequenceLaw _
    TendstoInDistribution (fun _ : ℕ => pairHardPrefixRoot β d k) atTop (pairHardPrefixRoot β d k)
      (fun n => markedArrivalSequenceLaw (ρ n : Measure (ℝ × ℝ)))
      (markedArrivalSequenceLaw (ρ₀ : Measure (ℝ × ℝ))) := by
  let (n : ℕ) : IsProbabilityMeasure (markedArrivalSequenceLaw (ρ n : Measure (ℝ × ℝ))) :=
    isProbabilityMeasure_markedArrivalSequenceLaw _
  let : IsProbabilityMeasure (markedArrivalSequenceLaw (ρ₀ : Measure (ℝ × ℝ))) :=
    isProbabilityMeasure_markedArrivalSequenceLaw _
  have hcont := continuous_pairHardPrefixRoot β hd k
  let F : ((Fin k → ℝ) × (Fin k → ℝ × ℝ)) → ℝ × ℝ :=
    pairHardPrefixRoot β d k ∘ Prod.map extendHardPrefix extendHardPrefix
  have hF : Continuous F :=
    hcont.comp (continuous_extendHardPrefix.prodMap continuous_extendHardPrefix)
  refine ⟨fun _ => hcont.measurable.aemeasurable, hcont.measurable.aemeasurable, ?_⟩
  have hmap (q : ProbabilityMeasure (ℝ × ℝ)) :
      letI : IsProbabilityMeasure (markedArrivalSequenceLaw (q : Measure (ℝ × ℝ))) :=
        isProbabilityMeasure_markedArrivalSequenceLaw _
      (⟨(markedArrivalSequenceLaw (q : Measure (ℝ × ℝ))).map (pairHardPrefixRoot β d k),
        Measure.isProbabilityMeasure_map hcont.measurable.aemeasurable⟩ :
          ProbabilityMeasure (ℝ × ℝ)) = (hardPairPrefixProbability k q).map hF.measurable.aemeasurable := by
    apply Subtype.ext
    have hproj : Measurable (hardPairPrefixProjection k) := by unfold hardPairPrefixProjection; fun_prop
    change (markedArrivalSequenceLaw (q : Measure (ℝ × ℝ))).map (pairHardPrefixRoot β d k) =
      ((hardPairPrefixProbability k q : Measure _).map F)
    rw [pairHardPrefixRoot_eq_comp, ← Measure.map_map hF.measurable hproj, map_hardPairPrefixProjection]
  simp only [hmap]
  apply ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ _ hF
  have hπ : Tendsto (fun n => ProbabilityMeasure.pi (fun _ : Fin k => ρ n)) atTop
      (𝓝 (ProbabilityMeasure.pi (fun _ : Fin k => ρ₀))) :=
    ProbabilityMeasure.continuous_pi.continuousAt.tendsto.comp (tendsto_pi_nhds.mpr (fun _ => h))
  exact ProbabilityMeasure.continuous_prod.continuousAt.tendsto.comp (tendsto_const_nhds.prodMk_nhds hπ)

private theorem scalarHardPrefixRoot_tendstoInMeasure {β d : ℝ} (hd : 0 < d)
    (μ : ProbabilityMeasure ℝ) (hμ : IsCavityLaw β d (μ : Measure ℝ)) :
    TendstoInMeasure (markedSpacings (μ : Measure ℝ))
      (scalarHardPrefixRoot β d) atTop (arrivalSoftOutput β d 0) := by
  have hp : ∀ᵐ x ∂(μ : Measure ℝ), 0 < x :=
    (mem_ae_iff_prob_eq_one (measurableSet_Ioi (a := (0 : ℝ)))).mpr hμ.2.1
  have hm : ∀ᵐ ω ∂markedSpacings (μ : Measure ℝ), ∀ i, 0 < ω.2 i := by
    apply ae_all_iff.mpr
    intro i
    exact (markedArrival_eval_preserving (μ : Measure ℝ) i).quasiMeasurePreserving.tendsto_ae.eventually hp
  apply tendstoInMeasure_of_tendsto_ae
    (fun k => (continuous_scalarHardPrefixRoot β hd k).measurable.aestronglyMeasurable)
  filter_upwards [hμ.2.2.1, hm] with ω hω hpos
  have hnonneg (i : ℕ) : 0 ≤ cavityTerm β d ω i :=
    mul_nonneg (Real.exp_nonneg _) (hpos i).le
  have hsum : (arrivalWeightedSum β d ω).toReal = ∑' i, cavityTerm β d ω i := by
    unfold arrivalWeightedSum
    rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg hω.1, ENNReal.toReal_ofReal hω.2.le]
  change Tendsto (fun k => (max (hardPrefixFloor k) (cavityPrefixSum β d k ω))⁻¹)
    atTop (𝓝 (0 + (arrivalWeightedSum β d ω).toReal)⁻¹)
  rw [zero_add, hsum]
  have hlim := (tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto hardPrefixFloor atTop (𝓝 0)).max
    (show Tendsto (fun k => cavityPrefixSum β d k ω) atTop (𝓝 (∑' i, cavityTerm β d ω i))
      from hω.1.hasSum.tendsto_sum_nat)
  rw [max_eq_right hω.2.le] at hlim
  exact (continuousAt_inv₀ hω.2.ne').tendsto.comp hlim

/-- The canonical bivariate hard recursion is sequentially continuous on
the set of couplings of two fixed positive hard cavity laws. -/
theorem tendsto_hardCouplingProbability_of_fixed_marginals {β d : ℝ} (hd : 0 < d)
    {μ ν : ProbabilityMeasure ℝ} (hμ : IsCavityLaw β d (μ : Measure ℝ))
    (hν : IsCavityLaw β d (ν : Measure ℝ))
    {ρ : ℕ → ProbabilityMeasure (ℝ × ℝ)} {ρ₀ : ProbabilityMeasure (ℝ × ℝ)}
    (hρ : ∀ n, ρ n ∈ couplingLaws μ ν) (hρ₀ : ρ₀ ∈ couplingLaws μ ν)
    (h : Tendsto ρ atTop (𝓝 ρ₀)) :
    Tendsto (fun n => hardCouplingProbability β d (ρ n)) atTop
      (𝓝 (hardCouplingProbability β d ρ₀)) := by
  let P (q : ProbabilityMeasure (ℝ × ℝ)) := markedArrivalSequenceLaw (q : Measure (ℝ × ℝ))
  let (q : ProbabilityMeasure (ℝ × ℝ)) : IsProbabilityMeasure (P q) :=
    isProbabilityMeasure_markedArrivalSequenceLaw _
  have happrox : TendstoInDistribution (fun _ : ℕ => pairedHardRoot β d) atTop (pairedHardRoot β d)
      (fun n => P (ρ n)) (P ρ₀) := by
    apply tendstoInDistribution_of_uniform_truncations_dist
      (Xcut := fun k _ => pairHardPrefixRoot β d k) (Ycut := pairHardPrefixRoot β d)
      (fun _ => measurable_pairedHardRoot β d) (measurable_pairedHardRoot β d)
      (fun k _ => (continuous_pairHardPrefixRoot β hd k).measurable)
      (fun k => (continuous_pairHardPrefixRoot β hd k).measurable)
      (fun k => tendstoInDistribution_pairHardPrefixRoot (β := β) hd k h)
    intro δ hδ η hη
    let A (k : ℕ) : Set ArrivalConfiguration :=
      {ω | δ ≤ dist (scalarHardPrefixRoot β d k ω) (arrivalSoftOutput β d 0 ω)}
    have hA (k : ℕ) : MeasurableSet (A k) :=
      measurableSet_le measurable_const
        ((continuous_scalarHardPrefixRoot β hd k).measurable.dist
          (measurable_arrivalSoftOutput β d 0))
    have hU := (tendstoInMeasure_iff_measureReal_dist.mp
      (scalarHardPrefixRoot_tendstoInMeasure hd μ hμ) δ hδ).eventually
        (Iio_mem_nhds (half_pos hη))
    have hV := (tendstoInMeasure_iff_measureReal_dist.mp
      (scalarHardPrefixRoot_tendstoInMeasure hd ν hν) δ hδ).eventually
        (Iio_mem_nhds (half_pos hη))
    obtain ⟨k, hk₁, hk₂⟩ := (hU.and hV).exists
    have herr (q : ProbabilityMeasure (ℝ × ℝ)) (hq : q ∈ couplingLaws μ ν) :
        (P q).real {ω | δ ≤ dist (pairHardPrefixRoot β d k ω) (pairedHardRoot β d ω)} ≤ η := by
      have hf : (q : Measure (ℝ × ℝ)).map Prod.fst = μ := congrArg Subtype.val hq.1
      have hs : (q : Measure (ℝ × ℝ)).map Prod.snd = ν := congrArg Subtype.val hq.2
      have hF : (P q).map firstArrivalConfiguration =
          markedSpacings ((q : Measure (ℝ × ℝ)).map Prod.fst) :=
        (markedArrival_projection (q : Measure (ℝ × ℝ)) Prod.fst measurable_fst).map_eq
      have hS : (P q).map secondArrivalConfiguration =
          markedSpacings ((q : Measure (ℝ × ℝ)).map Prod.snd) :=
        (markedArrival_projection (q : Measure (ℝ × ℝ)) Prod.snd measurable_snd).map_eq
      have he₁ : (P q).real (firstArrivalConfiguration ⁻¹' A k) =
          (markedSpacings (μ : Measure ℝ)).real (A k) := by
        rw [measureReal_def, ← Measure.map_apply measurable_firstArrivalConfiguration (hA k)]
        rw [hF, hf]
        rfl
      have he₂ : (P q).real (secondArrivalConfiguration ⁻¹' A k) =
          (markedSpacings (ν : Measure ℝ)).real (A k) := by
        rw [measureReal_def, ← Measure.map_apply measurable_secondArrivalConfiguration (hA k)]
        rw [hS, hs]
        rfl
      refine (measureReal_mono (s₂ := firstArrivalConfiguration ⁻¹' A k ∪
        secondArrivalConfiguration ⁻¹' A k) ?_).trans ((measureReal_union_le _ _).trans ?_)
      · intro ω hω
        change δ ≤ dist (pairHardPrefixRoot β d k ω) (pairedHardRoot β d ω) at hω
        rw [Prod.dist_eq, le_max_iff] at hω
        simp only [pairedHardRoot_fst, pairedHardRoot_snd] at hω
        exact hω
      · rw [he₁, he₂]
        change (markedSpacings (μ : Measure ℝ)).real (A k) < η / 2 at hk₁
        change (markedSpacings (ν : Measure ℝ)).real (A k) < η / 2 at hk₂
        linarith
    exact ⟨k, .of_forall fun n => by simpa only [dist_comm] using herr (ρ n) (hρ n),
      herr ρ₀ hρ₀⟩
  exact happrox.tendsto

/-- The bivariate hard update is continuous for weak convergence of
couplings with fixed hard marginal laws. -/
theorem continuousOn_hardCouplingProbability {β d : ℝ} (hd : 0 < d)
    {μ ν : ProbabilityMeasure ℝ} (hμ : IsCavityLaw β d (μ : Measure ℝ))
    (hν : IsCavityLaw β d (ν : Measure ℝ)) :
    ContinuousOn (hardCouplingProbability β d) (couplingLaws μ ν) := by
  rw [continuousOn_iff_continuous_domRestrict, continuous_iff_continuousAt]
  intro ρ₀
  apply tendsto_nhds_iff_seq_tendsto.mpr
  intro ρ h
  exact tendsto_hardCouplingProbability_of_fixed_marginals hd hμ hν
    (fun n => (ρ n).property) ρ₀.property (continuous_subtype_val.continuousAt.tendsto.comp h)

end Certificate

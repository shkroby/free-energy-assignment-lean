import Certificate.OverlapOccupationLimit
import Mathlib.MeasureTheory.Measure.Portmanteau

/-! At small positive fugacity the first three cavity occupations stay
uniformly away from zero in probability. -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

namespace Certificate

private theorem exists_smallPositiveCutoff_apart_from_zero {ι : Type*} {l : Filter ι}
    [l.NeBot] {P : ι → ProbabilityMeasure ℝ} {H : ProbabilityMeasure ℝ}
    (hLaw : Tendsto P l (𝓝 H)) (hH : ∀ᵐ x ∂(H : Measure ℝ), 0 < x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ i in l, (P i : Measure ℝ) (Iic a) < ENNReal.ofReal ε := by
  let a (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have ha (n : ℕ) : 0 < a n := by dsimp only [a]; positivity
  have h₀ : Tendsto a atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hanti : Antitone a := by
    intro m n h
    exact one_div_le_one_div_of_le (by positivity) (add_le_add_left (Nat.cast_le.mpr h) 1)
  have hI : (⋂ n, Iic (a n)) = Iic (0:ℝ) := by
    ext x
    constructor
    · intro hx
      exact ge_of_tendsto h₀ (Eventually.of_forall fun n => mem_iInter.mp hx n)
    · intro hx
      exact mem_iInter.mpr fun n => show x ≤ a n from (show x ≤ 0 from hx).trans (ha n).le
  have hzero : (H : Measure ℝ) (Iic 0) = 0 :=
    measure_eq_zero_iff_ae_notMem.mpr (hH.mono fun _ h => not_le_of_gt h)
  have hNear : Tendsto (fun n => (H : Measure ℝ) (Iic (a n))) atTop (𝓝 0) := by
    have ht := tendsto_measure_iInter_atTop (μ := (H : Measure ℝ))
      (s := fun n => Iic (a n)) (fun _ => measurableSet_Iic.nullMeasurableSet)
      (fun m n h => Iic_subset_Iic.mpr (hanti h))
      ⟨0, measure_ne_top _ _⟩
    rwa [hI, hzero] at ht
  obtain ⟨n, hn⟩ := (hNear.eventually (Iio_mem_nhds (ENNReal.ofReal_pos.mpr hε))).exists
  refine ⟨a n, ha n, ?_⟩
  have hu := (ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hLaw
    (F := Iic (a n)) isClosed_Iic).trans_lt hn
  exact eventually_lt_of_limsup_lt hu

private def anyLongAmong (d L : ℝ) (E : ℕ → ℝ) : Prop :=
  ∃ i : Fin 3, L < arrivalLength d E i.val

private theorem measurableSet_anyLongAmong (d L : ℝ) :
    MeasurableSet {E | anyLongAmong d L E} := by
  have he : {E | anyLongAmong d L E} = ⋃ i : Fin 3, {E | L < arrivalLength d E i.val} := by
    ext E
    simp [anyLongAmong]
  rw [he]
  exact MeasurableSet.iUnion fun i => measurableSet_lt measurable_const (by unfold arrivalLength; fun_prop)

private theorem exists_lengthBound_firstThree (d : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ L : ℕ, exponentialSpacings {E | anyLongAmong d L E} < ENNReal.ofReal ε := by
  let : IsProbabilityMeasure exponentialSpacings := isProbabilityMeasure_exponentialSpacings
  let A (L : ℕ) : Set (ℕ → ℝ) := {E | anyLongAmong d L E}
  have hm (L : ℕ) : NullMeasurableSet (A L) exponentialSpacings :=
    (measurableSet_anyLongAmong d L).nullMeasurableSet
  have hanti : Antitone A := by
    intro L K h E hE
    obtain ⟨i, hi⟩ := hE
    exact ⟨i, (Nat.cast_le.mpr h).trans_lt hi⟩
  have he : (⋂ L, A L) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro E he
    choose N hN using (fun i : Fin 3 => exists_nat_gt (arrivalLength d E i.val))
    obtain ⟨i, hi⟩ := (mem_iInter.mp he (∑ i : Fin 3, N i) : E ∈ A (∑ i : Fin 3, N i))
    have hsum : N i ≤ ∑ j : Fin 3, N j :=
      Finset.single_le_sum (f := N) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
    exact (not_lt_of_ge ((hN i).le.trans (Nat.cast_le.mpr hsum))) hi
  have hT := tendsto_measure_iInter_atTop hm hanti ⟨0, measure_ne_top _ _⟩
  rw [he, measure_empty] at hT
  exact (hT.eventually (Iio_mem_nhds (ENNReal.ofReal_pos.mpr hε))).exists

namespace CanonicalTree

/-- Uniformly near zero fugacity, the probability that any of the first
three occupations is below a common positive threshold is arbitrarily small. -/
theorem eventually_measure_firstThree_rootOccupation_small {β d : ℝ}
    (hβ : 0 < β) (hd : 0 < d) (H : ProbabilityMeasure ℝ)
    (hH : IsCavityLaw β d (H : Measure ℝ))
    (hUnique : ∀ ν : Measure ℝ, IsCavityLaw β d ν → ν = (H : Measure ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ z in 𝓝[>] (0:ℝ),
      (markedSpacings (softCavityProbability β d z : Measure ℝ))
        {ω | ∃ i : Fin 3, rootOccupation β d z ω i.val ≤ η} ≤ ENNReal.ofReal ε := by
  have hHp : ∀ᵐ x ∂(H : Measure ℝ), 0 < x :=
    (mem_ae_iff_prob_eq_one (measurableSet_Ioi (a := (0:ℝ)))).mpr hH.2.1
  let α := ε / 5
  have hα : 0 < α := by dsimp only [α]; positivity
  obtain ⟨a,ha,hA⟩ := exists_smallPositiveCutoff_apart_from_zero
    (tendsto_softCavityProbability_of_hard_unique hβ hd H hUnique) hHp hα
  obtain ⟨L,hL⟩ := exists_lengthBound_firstThree d hα
  let η := Real.exp (-β*(L:ℝ)) * a^2
  refine ⟨η, by dsimp only [η]; positivity, ?_⟩
  filter_upwards [hA, self_mem_nhdsWithin] with z hz hzpos
  have hz' : 0 < z := hzpos
  let μ : Measure ℝ := softCavityProbability β d z
  let P := markedSpacings μ
  let : IsProbabilityMeasure μ := inferInstanceAs
    (IsProbabilityMeasure (softCavityProbability β d z : Measure ℝ))
  let : IsProbabilityMeasure exponentialSpacings := isProbabilityMeasure_exponentialSpacings
  let : IsProbabilityMeasure P := isProbabilityMeasure_markedArrivalSequenceLaw μ
  let B : Set ArrivalConfiguration := Prod.fst ⁻¹' {E | anyLongAmong d L E}
  let D : Set ArrivalConfiguration := (arrivalSoftOutput β d z) ⁻¹' Iic a
  let M (i : Fin 3) : Set ArrivalConfiguration := {ω | ω.2 i.val ≤ a}
  have hB : P B ≤ ENNReal.ofReal α := by
    have hm := (measurePreserving_fst (μ := exponentialSpacings)
      (ν := Measure.infinitePi (fun _ : ℕ => μ))).map_eq
    unfold B
    rw [← Measure.map_apply measurable_fst (measurableSet_anyLongAmong d L)]
    exact (congrArg (fun m => m {E | anyLongAmong d L E}) hm).trans_le hL.le
  have hD : P D ≤ ENNReal.ofReal α := by
    unfold D
    rw [← Measure.map_apply (measurable_arrivalSoftOutput β d z) measurableSet_Iic,
      (softCavityProbability_spec hβ hd hz').2]
    exact hz.le
  have hM (i : Fin 3) : P (M i) ≤ ENNReal.ofReal α := by
    have hm := markedArrival_eval_preserving μ i.val
    change P ((fun ω : ArrivalConfiguration => ω.2 i.val) ⁻¹' Iic a) ≤ _
    rw [← Measure.map_apply hm.measurable measurableSet_Iic]
    change (markedArrivalSequenceLaw μ).map (fun ω => ω.2 i.val) (Iic a) ≤ _
    rw [hm.map_eq]
    exact hz.le
  have hsub : {ω | ∃ i : Fin 3, rootOccupation β d z ω i.val ≤ η} ⊆
      B ∪ D ∪ ⋃ i, M i := by
    intro ω hω
    obtain ⟨i,hω⟩ := hω
    by_contra hmem
    have h₁ : arrivalLength d ω.1 i.val ≤ L := le_of_not_gt
      (fun h => hmem (Or.inl (Or.inl ⟨i,h⟩)))
    have h₂ : a < ω.2 i.val := lt_of_not_ge
      (fun h => hmem (Or.inr (mem_iUnion.mpr ⟨i,h⟩)))
    have h₃ : a < arrivalSoftOutput β d z ω := lt_of_not_ge <|
      fun h => hmem (Or.inl (Or.inr h))
    have hW : Real.exp (-β*(L:ℝ)) ≤ Real.exp (-β * arrivalLength d ω.1 i.val) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left h₁ (neg_nonpos.mpr hβ.le))
    have hprod : a*a < ω.2 i.val * arrivalSoftOutput β d z ω :=
      mul_lt_mul h₂ h₃.le ha (ha.trans h₂).le
    apply (not_lt_of_ge hω)
    unfold rootOccupation cavityTerm
    calc
      η = Real.exp (-β*(L:ℝ)) * (a*a) := by simp [η,pow_two]
      _ < Real.exp (-β*(L:ℝ)) * (ω.2 i.val * arrivalSoftOutput β d z ω) :=
        mul_lt_mul_of_pos_left hprod (Real.exp_pos _)
      _ ≤ _ := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right hW (mul_nonneg (ha.trans h₂).le (ha.trans h₃).le)
  have hsum : P (⋃ i, M i) ≤ 3 * ENNReal.ofReal α := by
    calc
      _ ≤ ∑' i, P (M i) := measure_iUnion_le M
      _ ≤ ∑' _ : Fin 3, ENNReal.ofReal α := ENNReal.tsum_le_tsum hM
      _ = _ := by simp [tsum_fintype, nsmul_eq_mul]
  calc
    _ ≤ P (B ∪ D ∪ ⋃ i, M i) := measure_mono hsub
    _ ≤ P B + P D + P (⋃ i, M i) :=
      (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ ENNReal.ofReal α + ENNReal.ofReal α + 3 * ENNReal.ofReal α :=
      add_le_add (add_le_add hB hD) hsum
    _ = _ := by
      rw [show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by norm_num, ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 3),
        ← ENNReal.ofReal_add hα.le hα.le, ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      dsimp only [α]
      ring

end CanonicalTree
end Certificate

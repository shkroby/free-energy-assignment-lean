import Certificate.RootEdgeMarks
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.InfinitePi

/-! Fresh entries after conditioning on a fixed exploration history. -/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

namespace Certificate.LocalExploration

/-- Observe the array at a collection of distinct entries. -/
def observedCosts {I : Type*} (index : I ↪ ℕ × ℕ) (C : CostArray) (i : I) : ℝ :=
  C (index i)

theorem measurable_observedCosts {I : Type*} (index : I ↪ ℕ × ℕ) :
    Measurable (observedCosts index) :=
  measurable_pi_iff.mpr (fun i => measurable_pi_apply (index i))

theorem observedCosts_law {I : Type*} (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (index : I ↪ ℕ × ℕ) :
    (iidCosts μ).map (observedCosts index) = Measure.infinitePi (fun _ : I => μ) :=
  Measure.map_infinitePi_infinitePi_of_inj index.injective

/-- Two disjoint finite blocks of the actual iid array have the product joint law. -/
theorem observedCosts_jointLaw {I J : Type*} [Fintype I] [Fintype J]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (old : I ↪ ℕ × ℕ) (fresh : J ↪ ℕ × ℕ)
    (hdis : ∀ i j, old i ≠ fresh j) :
    (iidCosts μ).map (fun C => (observedCosts old C, observedCosts fresh C)) =
      (Measure.infinitePi (fun _ : I => μ)).prod (Measure.infinitePi (fun _ : J => μ)) := by
  let idx : I ⊕ J → ℕ × ℕ := Sum.elim old fresh
  have hidx : Function.Injective idx := by
    intro a b hab
    rcases a with i | j <;> rcases b with i' | j'
    · exact congrArg Sum.inl (old.injective hab)
    · exact (hdis i j' hab).elim
    · exact (hdis i' j hab.symm).elim
    · exact congrArg Sum.inr (fresh.injective hab)
  let combined (C : CostArray) (i : I ⊕ J) := C (idx i)
  have hm : Measurable combined := measurable_pi_iff.mpr (fun i => measurable_pi_apply (idx i))
  have hmap : (iidCosts μ).map combined = Measure.infinitePi (fun _ : I ⊕ J => μ) :=
    Measure.map_infinitePi_infinitePi_of_inj hidx
  let split : (I ⊕ J → ℝ) ≃ᵐ (I → ℝ) × (J → ℝ) :=
    MeasurableEquiv.sumPiEquivProdPi (fun _ : I ⊕ J => ℝ)
  change (iidCosts μ).map (split ∘ combined) = _
  rw [← Measure.map_map split.measurable hm, hmap]
  simpa only [Measure.infinitePi_eq_pi] using
    (measurePreserving_sumPiEquivProdPi (fun _ : I ⊕ J => μ)).map_eq

/-- Any measurable event determined by the old entries factors exactly
against a test on the fresh entries, even when the history event is null. -/
theorem measure_history_inter_fresh {I J : Type*} [Fintype I] [Fintype J]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (old : I ↪ ℕ × ℕ) (fresh : J ↪ ℕ × ℕ)
    (hdis : ∀ i j, old i ≠ fresh j) {A : Set (I → ℝ)} {B : Set (J → ℝ)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (iidCosts μ) ((observedCosts old ⁻¹' A) ∩ (observedCosts fresh ⁻¹' B)) =
      (iidCosts μ) (observedCosts old ⁻¹' A) * (Measure.infinitePi (fun _ : J => μ)) B := by
  have h := congrArg (fun (m : Measure ((I → ℝ) × (J → ℝ))) => m (A ×ˢ B))
    (observedCosts_jointLaw μ old fresh hdis)
  change ((iidCosts μ).map (fun C => (observedCosts old C, observedCosts fresh C))) (A ×ˢ B) =
    ((Measure.infinitePi (fun _ : I => μ)).prod (Measure.infinitePi (fun _ : J => μ))) (A ×ˢ B) at h
  rw [Measure.map_apply ((measurable_observedCosts old).prodMk (measurable_observedCosts fresh))
    (hA.prod hB), Measure.prod_prod, ← observedCosts_law μ old,
    Measure.map_apply (measurable_observedCosts old) hA] at h
  exact h

/-- Exact probability of a finite history cylinder and a fresh cylinder,
including constraints for both retained and rejected tested edges. -/
theorem measure_history_inter_fresh_cylinders {I J : Type*} [Fintype I] [Fintype J]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (old : I ↪ ℕ × ℕ) (fresh : J ↪ ℕ × ℕ)
    (hdis : ∀ i j, old i ≠ fresh j) (A : I → Set ℝ) (B : J → Set ℝ)
    (hA : ∀ i, MeasurableSet (A i)) (hB : ∀ j, MeasurableSet (B j)) :
    (iidCosts μ) ((observedCosts old ⁻¹' univ.pi A) ∩ (observedCosts fresh ⁻¹' univ.pi B)) =
      (∏ i, μ (A i)) * ∏ j, μ (B j) := by
  rw [measure_history_inter_fresh μ old fresh hdis (MeasurableSet.univ_pi hA)
    (MeasurableSet.univ_pi hB), ← Measure.map_apply (measurable_observedCosts old)
    (MeasurableSet.univ_pi hA), observedCosts_law, Measure.infinitePi_pi_univ _ hA,
    Measure.infinitePi_pi_univ _ hB, tprod_fintype, tprod_fintype]

/-- Fresh entries retain their entire iid law upon conditioning on a
positive-probability event determined by the old entries. -/
theorem observedCosts_conditionalLaw {I J : Type*} [Fintype I] [Fintype J]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (old : I ↪ ℕ × ℕ) (fresh : J ↪ ℕ × ℕ)
    (hdis : ∀ i j, old i ≠ fresh j) {A : Set (I → ℝ)} (hA : MeasurableSet A)
    (hpos : (iidCosts μ) (observedCosts old ⁻¹' A) ≠ 0) :
    (ProbabilityTheory.cond (iidCosts μ) (observedCosts old ⁻¹' A)).map (observedCosts fresh) =
      Measure.infinitePi (fun _ : J => μ) := by
  let : IsProbabilityMeasure (iidCosts μ) := by unfold iidCosts; infer_instance
  have hfin := measure_ne_top (iidCosts μ) (observedCosts old ⁻¹' A)
  ext B hB
  rw [Measure.map_apply (measurable_observedCosts fresh) hB,
    ProbabilityTheory.cond_apply (hA.preimage (measurable_observedCosts old)),
    measure_history_inter_fresh μ old fresh hdis hA hB, ← mul_assoc,
    ENNReal.inv_mul_cancel hpos hfin, one_mul]

/-- The next block queried by a rule that depends on previously observed costs. -/
def adaptiveFreshCosts {I J : Type*} (old : I ↪ ℕ × ℕ)
    (choose : (I → ℝ) → J ↪ ℕ × ℕ) (C : CostArray) : J → ℝ :=
  observedCosts (choose (observedCosts old C)) C

/-- On a fixed history event where the adaptive rule selects a given disjoint
block, the entries it actually reads have their original iid law. -/
theorem adaptiveFreshCosts_conditionalLaw {I J : Type*} [Fintype I] [Fintype J]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (old : I ↪ ℕ × ℕ)
    (choose : (I → ℝ) → J ↪ ℕ × ℕ) (fresh : J ↪ ℕ × ℕ) (hdis : ∀ i j, old i ≠ fresh j)
    {A : Set (I → ℝ)} (hA : MeasurableSet A)
    (hfixed : ∀ x ∈ A, choose x = fresh)
    (hpos : (iidCosts μ) (observedCosts old ⁻¹' A) ≠ 0) :
    (ProbabilityTheory.cond (iidCosts μ) (observedCosts old ⁻¹' A)).map
        (adaptiveFreshCosts old choose) =
      Measure.infinitePi (fun _ : J => μ) := by
  rw [← observedCosts_conditionalLaw μ old fresh hdis hA hpos]
  apply Measure.map_congr
  apply ae_cond_of_forall_mem (hA.preimage (measurable_observedCosts old))
  intro C hC
  unfold adaptiveFreshCosts
  rw [hfixed (observedCosts old C) hC]

/-- Each candidate collision requires two genuinely distinct retained
entries. A union bound gives the number of candidates times the squared
one-entry retention probability. -/
theorem measure_exists_both_retained_le {J : Type*} [Fintype J]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (left right : J → ℕ × ℕ)
    (hdis : ∀ j, left j ≠ right j) {A : Set ℝ} (hA : MeasurableSet A) :
    (iidCosts μ) {C | ∃ j, C (left j) ∈ A ∧ C (right j) ∈ A} ≤
      (Fintype.card J : ℝ≥0∞) * (μ A)^2 := by
  let B (j : J) : Set CostArray := (fun C => (C (left j), C (right j))) ⁻¹' (A ×ˢ A)
  have hset : {C : CostArray | ∃ j, C (left j) ∈ A ∧ C (right j) ∈ A} = ⋃ j, B j := by
    ext C
    simp [B]
  have hB (j : J) : (iidCosts μ) (B j) = (μ A)^2 := by
    have hlaw : (iidCosts μ).map (fun C => (C (left j), C (right j))) = μ.prod μ :=
      Measure.infinitePi_map_eval_prod (hdis j)
    let f : CostArray → ℝ × ℝ := fun C => (C (left j), C (right j))
    have hf : Measurable f := (measurable_pi_apply (left j)).prodMk (measurable_pi_apply (right j))
    change (iidCosts μ) (f ⁻¹' (A ×ˢ A)) = _
    rw [← Measure.map_apply hf (hA.prod hA), hlaw, Measure.prod_prod, pow_two]
  rw [hset]
  refine (measure_iUnion_le B).trans_eq ?_
  simp only [hB, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Two distinct rows have a common retained neighbor in a prescribed
column set with probability at most the column count times the squared
one-edge retention probability. -/
theorem measure_exists_common_retained_neighbor_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {r s : ℕ} (hrs : r ≠ s) (cols : Finset ℕ) {A : Set ℝ} (hA : MeasurableSet A) :
    (iidCosts μ) {C | ∃ j ∈ cols, C (r, j) ∈ A ∧ C (s, j) ∈ A} ≤
      (cols.card : ℝ≥0∞) * (μ A)^2 := by
  have h := measure_exists_both_retained_le μ (fun j : cols => (r, j.val))
    (fun j : cols => (s, j.val)) (fun _ hj => hrs (congrArg Prod.fst hj)) hA
  simpa only [Fintype.card_coe, Subtype.exists, exists_prop] using h

/-- The probability that two specified distinct rows share any retained
neighbor in the size-`n` cutoff graph vanishes as the size grows. -/
theorem tendsto_measure_common_retained_neighbor_scaled {μ : Measure ℝ}
    [IsProbabilityMeasure μ] {d κ R : ℝ} (hd : 0 < d) (hκ : 0 < κ) (hR : 0 < R)
    (h : SmallCostTail μ κ d) {r s : ℕ} (hrs : r ≠ s) :
    Tendsto (fun n : ℕ => (iidCosts μ) {C | ∃ j < n,
      lengthScale d κ n * C (r, j) ≤ R ∧ lengthScale d κ n * C (s, j) ≤ R})
      atTop (𝓝 0) := by
  let p := shortEdgeProbability μ d κ R
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hnp : Tendsto (fun n : ℕ => (n : ℝ) * p n) atTop (𝓝 (R^d)) :=
    tendsto_scaled_shortEdgeProbability hd hκ hR h
  have hp : Tendsto p atTop (𝓝 0) := by
    refine (hnp.div_atTop hn).congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn₀
    exact mul_div_cancel_left₀ (p n) (Nat.cast_ne_zero.mpr hn₀.ne')
  have hnp₂ : Tendsto (fun n : ℕ => ENNReal.ofReal ((n : ℝ) * p n * p n)) atTop (𝓝 0) := by
    simpa only [mul_zero, ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal (hnp.mul hp)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hnp₂
    (Eventually.of_forall (fun _ => zero_le)) ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn₀
  let A := (fun c : ℝ => lengthScale d κ n * c) ⁻¹' Iic R
  have hA : MeasurableSet A := measurableSet_Iic.preimage (by fun_prop)
  have hprob : μ A = ENNReal.ofReal (p n) := by
    rw [← Measure.map_apply (by fun_prop : Measurable (fun c : ℝ => lengthScale d κ n * c))
      measurableSet_Iic]
    exact scaledLengthLaw_Iic hκ hn₀ R
  have hb := measure_exists_common_retained_neighbor_le μ hrs (Finset.range n) hA
  simp only [Finset.mem_range, Finset.card_range, hprob] at hb
  have hp₀ : 0 ≤ p n := cdf_nonneg μ _
  rw [ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg _) hp₀),
    ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, mul_assoc, ← pow_two]
  exact hb

end Certificate.LocalExploration

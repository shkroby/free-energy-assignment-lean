import Certificate.LocalExplorationHistory
import Certificate.LocalExplorationMarks
import Certificate.LocalExplorationPattern
import Certificate.LocalExplorationLimits
import Mathlib.Data.Finset.Sort

/-! The retained marks of an exposed vertex, indexed in increasing label order. -/

open Filter Function MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

namespace Certificate.LocalExploration

section OrderedMarks

variable {I : Type*} [Fintype I] [LinearOrder I]

/-- Read the marks at a fixed set of labels, in increasing label order. -/
noncomputable def orderedMarksAt (S : Finset I) {k : ℕ} (hS : S.card = k)
    (x : I → ℝ) (j : Fin k) : ℝ :=
  x (S.orderIsoOfFin hS j : I)

omit [Fintype I] in
theorem measurable_orderedMarksAt (S : Finset I) {k : ℕ} (hS : S.card = k) :
    Measurable (orderedMarksAt S hS) :=
  measurable_pi_iff.mpr fun j => measurable_pi_apply (S.orderIsoOfFin hS j : I)

/-- Read the retained marks in increasing label order on the event that
the count is `k`, with the zero vector as a value elsewhere. -/
noncomputable def orderedRetainedMarks (A : Set ℝ) (k : ℕ) (x : I → ℝ) : Fin k → ℝ :=
  if h : (retainedLabels A x).card = k then orderedMarksAt (retainedLabels A x) h x else 0

theorem orderedRetainedMarks_eq_of_labels {A : Set ℝ} {k : ℕ} {x : I → ℝ}
    {S : Finset I} (hS : S.card = k) (hx : retainedLabels A x = S) :
    orderedRetainedMarks A k x = orderedMarksAt S hS x := by
  subst S
  simp only [orderedRetainedMarks, dif_pos hS]

private abbrev LabelSetOfCard (I : Type*) (k : ℕ) := {S : Finset I // S.card = k}

theorem measurable_orderedRetainedMarks {A : Set ℝ} (hA : MeasurableSet A) (k : ℕ) :
    Measurable (orderedRetainedMarks (I := I) A k) := by
  intro B hB
  have he : orderedRetainedMarks A k ⁻¹' B =
      ({x : I → ℝ | retainedCount A x ≠ k} ∩ (fun _ : I → ℝ => (0 : Fin k → ℝ)) ⁻¹' B) ∪
        ⋃ S : LabelSetOfCard I k, {x : I → ℝ | retainedLabels A x = S.val} ∩
          orderedMarksAt S.val S.property ⁻¹' B := by
    ext x
    simp only [mem_preimage, mem_union, mem_inter_iff, mem_ofPred_eq, mem_iUnion]
    by_cases hk : retainedCount A x = k
    · have hk' : (retainedLabels A x).card = k := hk
      constructor
      · intro hx
        exact Or.inr ⟨⟨retainedLabels A x, hk'⟩, rfl, by
          simpa only [orderedRetainedMarks, dif_pos hk'] using hx⟩
      · rintro (⟨h, _⟩ | ⟨S, hx, hm⟩)
        · exact (h hk).elim
        · simpa only [orderedRetainedMarks_eq_of_labels S.property hx] using hm
    · have hk' : ¬ (retainedLabels A x).card = k := hk
      constructor
      · intro hx
        exact Or.inl ⟨hk, by simpa only [orderedRetainedMarks, dif_neg hk'] using hx⟩
      · rintro (⟨_, h⟩ | ⟨S, hx, _⟩)
        · simpa only [orderedRetainedMarks, dif_neg hk'] using h
        · exact (hk' (congrArg Finset.card hx |>.trans S.property)).elim
  rw [he]
  exact (((measurable_retainedCount hA) (measurableSet_singleton k)).compl.inter
    (measurable_const hB)).union
    (MeasurableSet.iUnion (fun S => (measurableSet_retainedLabels_eq hA S.val).inter
      ((measurable_orderedMarksAt S.val S.property) hB)))

private theorem isProbabilityMeasure_conditionalRetainedLaw (ν : Measure ℝ)
    [IsProbabilityMeasure ν] {A : Set ℝ} (hA₀ : ν A ≠ 0) :
    IsProbabilityMeasure (conditionalRetainedLaw ν A) :=
  ProbabilityTheory.cond_isProbabilityMeasure hA₀

/-- Conditional on a retained label set of positive probability, the
ordered marks have the full iid product of the normalized retained law. -/
theorem orderedMarksAt_conditionalLaw (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {A : Set ℝ} (hA : MeasurableSet A) (hA₀ : ν A ≠ 0)
    {S : Finset I} {k : ℕ} (hS : S.card = k)
    (hH₀ : (Measure.infinitePi (fun _ : I => ν)) {x | retainedLabels A x = S} ≠ 0) :
    (ProbabilityTheory.cond (Measure.infinitePi (fun _ : I => ν))
      {x | retainedLabels A x = S}).map (orderedMarksAt S hS) =
      Measure.infinitePi (fun _ : Fin k => conditionalRetainedLaw ν A) := by
  classical
  let P := Measure.infinitePi (fun _ : I => ν)
  let H : Set (I → ℝ) := {x | retainedLabels A x = S}
  let V := conditionalRetainedLaw ν A
  let : IsProbabilityMeasure V := isProbabilityMeasure_conditionalRetainedLaw ν hA₀
  change (ProbabilityTheory.cond P H).map (orderedMarksAt S hS) =
    Measure.infinitePi (fun _ : Fin k => V)
  rw [Measure.infinitePi_eq_pi]
  symm
  apply Measure.pi_eq
  intro T hT
  let e := S.orderIsoOfFin hS
  let U (i : I) : Set ℝ := if hi : i ∈ S then T (e.symm ⟨i, hi⟩) else univ
  have hU (i : I) (hi : i ∈ S) : MeasurableSet (U i) := by
    simpa only [U, dif_pos hi] using hT (e.symm ⟨i, hi⟩)
  have hevent : H ∩ (orderedMarksAt S hS ⁻¹' univ.pi T) = markedPattern A S U := by
    ext x
    simp only [H, mem_inter_iff, mem_preimage, mem_ofPred_eq, markedPattern, mem_univ_pi]
    constructor
    · rintro ⟨hLabel, hx⟩
      refine ⟨hLabel, fun i hi => ?_⟩
      have hh := hx (e.symm ⟨i, hi⟩)
      simpa only [U, dif_pos hi, orderedMarksAt, ← show e = S.orderIsoOfFin hS from rfl,
        OrderIso.apply_symm_apply] using hh
    · rintro ⟨hLabel, hx⟩
      refine ⟨hLabel, fun j => ?_⟩
      have hh := hx (e j : I) (e j).property
      have hej : (⟨(e j : I), (e j).property⟩ : ↥S) = e j := Subtype.ext rfl
      simp only [U, dif_pos (e j).property] at hh
      rw [hej, OrderIso.symm_apply_apply] at hh
      exact hh
  have hprod : (∏ i ∈ S, V (U i)) = ∏ j, V (T j) := by
    let f := (S.orderEmbOfFin hS).toEmbedding
    have hf : Finset.univ.map f = S := Finset.map_orderEmbOfFin_univ S hS
    calc
      _ = ∏ i ∈ Finset.univ.map f, V (U i) := by rw [hf]
      _ = ∏ j, V (U (f j)) := Finset.prod_map _ _ _
      _ = _ := by
        apply Finset.prod_congr rfl
        intro j _
        change V (U (e j : I)) = V (T j)
        simp only [U, dif_pos (e j).property, Subtype.eta, OrderIso.symm_apply_apply]
  rw [Measure.map_apply (measurable_orderedMarksAt S hS) (MeasurableSet.univ_pi hT),
    ProbabilityTheory.cond_apply (measurableSet_retainedLabels_eq hA S), hevent,
    measure_markedPattern_factorizes ν hA hA₀ S hU]
  change (P H)⁻¹ * (P H * ∏ i ∈ S, V (U i)) = _
  rw [← mul_assoc, ENNReal.inv_mul_cancel hH₀ (measure_ne_top P H), one_mul, hprod]

/-- The ordered retained marks have the same iid law when only the
retained count is specified. Stated as an unnormalized factorization, the
identity also holds if that count has probability zero. -/
theorem measure_count_and_orderedRetainedMarks (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {A : Set ℝ} (hA : MeasurableSet A) (hA₀ : ν A ≠ 0)
    (k : ℕ) {B : Set (Fin k → ℝ)} (hB : MeasurableSet B) :
    (Measure.infinitePi (fun _ : I => ν))
        {x | retainedCount A x = k ∧ orderedRetainedMarks A k x ∈ B} =
      (Measure.infinitePi (fun _ : I => ν)) {x | retainedCount A x = k} *
        (Measure.infinitePi (fun _ : Fin k => conditionalRetainedLaw ν A)) B := by
  let P := Measure.infinitePi (fun _ : I => ν)
  let V := Measure.infinitePi (fun _ : Fin k => conditionalRetainedLaw ν A)
  let H (S : LabelSetOfCard I k) : Set (I → ℝ) := {x | retainedLabels A x = S.val}
  let E : Set (I → ℝ) := orderedRetainedMarks A k ⁻¹' B
  have hUnion : {x : I → ℝ | retainedCount A x = k} = ⋃ S, H S := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion, H]
    exact ⟨fun hx => ⟨⟨retainedLabels A x, hx⟩, rfl⟩,
      fun ⟨S, hx⟩ => (congrArg Finset.card hx).trans S.property⟩
  have hH (S : LabelSetOfCard I k) : MeasurableSet (H S) :=
    measurableSet_retainedLabels_eq hA S.val
  have hHdis : Pairwise (Disjoint on H) := by
    intro S T hST
    exact Set.disjoint_left.mpr fun _ hx hy => hST (Subtype.ext (hx.symm.trans hy))
  have hE : MeasurableSet E := (measurable_orderedRetainedMarks hA k) hB
  have hEach (S : LabelSetOfCard I k) : P (H S ∩ E) = P (H S) * V B := by
    by_cases hS₀ : P (H S) = 0
    · rw [measure_inter_null_of_null_left _ hS₀, hS₀, zero_mul]
    have hcond : (ProbabilityTheory.cond P (H S)).map (orderedMarksAt S.val S.property) = V :=
      orderedMarksAt_conditionalLaw ν hA hA₀ S.property hS₀
    have heq : (ProbabilityTheory.cond P (H S)).map (orderedRetainedMarks A k) = V := by
      rw [← hcond]
      exact Measure.map_congr (ae_cond_of_forall_mem (hH S)
        (fun _ hx => orderedRetainedMarks_eq_of_labels S.property hx))
    have hm := congrArg (fun (m : Measure (Fin k → ℝ)) => m B) heq
    change ((ProbabilityTheory.cond P (H S)).map (orderedRetainedMarks A k)) B = V B at hm
    rw [Measure.map_apply (measurable_orderedRetainedMarks hA k) hB] at hm
    rw [← ProbabilityTheory.cond_mul_eq_inter (hH S) E P, hm, mul_comm]
  change P ({x : I → ℝ | retainedCount A x = k} ∩ E) = _
  rw [hUnion, iUnion_inter, measure_iUnion (hHdis.mono fun _ _ hd =>
    hd.mono inter_subset_left inter_subset_left) (fun S => (hH S).inter hE),
    measure_iUnion hHdis hH]
  simp_rw [hEach, ENNReal.tsum_mul_right]
  rfl

/-- In particular the mark vector conditional on a positive-probability
count has its iid retained product law. -/
theorem orderedRetainedMarks_conditionalLaw_count (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {A : Set ℝ} (hA : MeasurableSet A) (hA₀ : ν A ≠ 0) (k : ℕ)
    (hk : (Measure.infinitePi (fun _ : I => ν)) {x | retainedCount A x = k} ≠ 0) :
    (ProbabilityTheory.cond (Measure.infinitePi (fun _ : I => ν))
      {x | retainedCount A x = k}).map (orderedRetainedMarks A k) =
      Measure.infinitePi (fun _ : Fin k => conditionalRetainedLaw ν A) := by
  let P := Measure.infinitePi (fun _ : I => ν)
  let H : Set (I → ℝ) := {x | retainedCount A x = k}
  have hH : MeasurableSet H := (measurable_retainedCount hA) (measurableSet_singleton k)
  ext B hB
  rw [Measure.map_apply (measurable_orderedRetainedMarks hA k) hB,
    ProbabilityTheory.cond_apply hH]
  change (P H)⁻¹ * P {x | retainedCount A x = k ∧ orderedRetainedMarks A k x ∈ B} = _
  rw [measure_count_and_orderedRetainedMarks ν hA hA₀ k hB, ← mul_assoc,
    ENNReal.inv_mul_cancel hk (measure_ne_top P H), one_mul]

end OrderedMarks

/-- The ordered list of eligible opposite labels determines distinct
entries even if some labels of the opposite class have been excluded. -/
def oneRootEntryEmbedding {I : Type*} (v : Vertex) (labels : I ↪ ℕ) : I ↪ ℕ × ℕ where
  toFun i := rootEntry v (labels i)
  inj' := by
    intro i j h
    apply labels.injective
    cases v with
    | inl r => exact congrArg Prod.snd h
    | inr c => exact congrArg Prod.fst h

/-- Scaled lengths to a prescribed set of eligible neighbors of one vertex. -/
noncomputable def oneRootLengths {I : Type*} (v : Vertex) (labels : I ↪ ℕ)
    (d κ : ℝ) (n : ℕ) (C : CostArray) (i : I) : ℝ :=
  lengthScale d κ n * C (rootEntry v (labels i))

theorem measurable_oneRootLengths {I : Type*} (v : Vertex) (labels : I ↪ ℕ)
    (d κ : ℝ) (n : ℕ) : Measurable (oneRootLengths v labels d κ n) := by
  unfold oneRootLengths
  fun_prop

theorem oneRootLengths_law {I : Type*} (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (v : Vertex) (labels : I ↪ ℕ) (d κ : ℝ) (n : ℕ) :
    (iidCosts μ).map (oneRootLengths v labels d κ n) =
      Measure.infinitePi (fun _ : I => scaledLengthLaw μ d κ n) := by
  let scale (x : I → ℝ) (i : I) := lengthScale d κ n * x i
  change (iidCosts μ).map (scale ∘ observedCosts (oneRootEntryEmbedding v labels)) = _
  rw [← Measure.map_map (by unfold scale; fun_prop)
    (measurable_observedCosts (oneRootEntryEmbedding v labels)), observedCosts_law]
  exact Measure.infinitePi_map_pi (fun _ : I => μ) (fun _ => by fun_prop)

/-- Event specifying both the number of retained neighbors and a test of
their length vector in the given order of eligible labels. -/
def oneRootMarkCountEvent {I : Type*} [Fintype I] [LinearOrder I] (v : Vertex) (labels : I ↪ ℕ)
    (d κ R : ℝ) (n k : ℕ) (B : Set (Fin k → ℝ)) : Set CostArray :=
  (oneRootLengths v labels d κ n) ⁻¹' {x | retainedCount (Iic R) x = k ∧
    orderedRetainedMarks (Iic R) k x ∈ B}

/-- The actual one-root event factors into its binomial count mass and a
test of iid lengths from the normalized truncated law. -/
theorem measure_oneRootMarkCountEvent {I : Type*} [Fintype I] [LinearOrder I]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (v : Vertex) (labels : I ↪ ℕ)
    {d κ R : ℝ} {n : ℕ} (k : ℕ) (hκ : 0 < κ) (hR : 0 < R) (h : SmallCostTail μ κ d)
    (hn : 0 < n) {B : Set (Fin k → ℝ)} (hB : MeasurableSet B) :
    iidCosts μ (oneRootMarkCountEvent v labels d κ R n k B) =
      ENNReal.ofReal (((Fintype.card I).choose k : ℝ) * (shortEdgeProbability μ d κ R n)^k *
        (1 - shortEdgeProbability μ d κ R n)^(Fintype.card I - k)) *
      (Measure.infinitePi (fun _ : Fin k => retainedLengthLaw μ d κ R n)) B := by
  let ν := scaledLengthLaw μ d κ n
  let : IsProbabilityMeasure ν := isProbabilityMeasure_scaledLengthLaw μ d κ n
  let p := shortEdgeProbability μ d κ R n
  have hp₀ : 0 ≤ p := cdf_nonneg μ _
  have hp₁ : p ≤ 1 := cdf_le_one μ _
  have hret : ν (Iic R) = ENNReal.ofReal p := scaledLengthLaw_Iic hκ hn R
  have hpos : ν (Iic R) ≠ 0 := by
    have hscale : 0 < lengthScale d κ n :=
      Real.rpow_pos_of_pos (mul_pos hκ (Nat.cast_pos.mpr hn)) _
    rw [hret]
    exact ENNReal.ofReal_ne_zero_iff.mpr (cdf_pos_of_smallCostTail hκ h (div_pos hR hscale))
  have habs : ν ((Iic R)ᶜ) = ENNReal.ofReal (1 - p) := by
    rw [prob_compl_eq_one_sub measurableSet_Iic, hret,
      ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hp₀]
  have hE : MeasurableSet {x : I → ℝ | retainedCount (Iic R) x = k ∧
      orderedRetainedMarks (Iic R) k x ∈ B} :=
    ((measurable_retainedCount measurableSet_Iic) (measurableSet_singleton k)).inter
      ((measurable_orderedRetainedMarks measurableSet_Iic k) hB)
  rw [oneRootMarkCountEvent, ← Measure.map_apply (measurable_oneRootLengths v labels d κ n) hE,
    oneRootLengths_law, measure_count_and_orderedRetainedMarks ν measurableSet_Iic hpos k hB,
    measure_retainedCount_eq ν measurableSet_Iic k, hret, habs]
  change _ = ENNReal.ofReal (((Fintype.card I).choose k : ℝ) * p^k *
    (1-p)^(Fintype.card I-k)) * _
  rw [ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp₀ _)),
    ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_pow hp₀,
    ENNReal.ofReal_pow (sub_nonneg.mpr hp₁), ENNReal.ofReal_natCast]
  rfl

/-- One generation from the actual array converges jointly on every fixed
count and continuity set of the ordered marks, with any fixed number of
excluded labels. The limiting marks are independent with the normalized
intensity, and the count mass is Poisson. -/
theorem tendsto_oneRootMarkCountEvent_of_null_frontier {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {d κ R : ℝ} (hd : 0 < d) (hκ : 0 < κ) (hR : 0 < R) (h : SmallCostTail μ κ d)
    (v : Vertex) (skip k : ℕ) (labels : ∀ n, Fin (n-skip) ↪ ℕ)
    {B : Set (Fin k → ℝ)} (hB : MeasurableSet B)
    (hfront : (finiteMarkProduct (fun _ : Fin k => limitingMarkProbability hd hR) :
      Measure (Fin k → ℝ)) (frontier B) = 0) :
    Tendsto (fun n : ℕ => iidCosts μ (oneRootMarkCountEvent v (labels (n+1)) d κ R (n+1) k B))
      atTop (𝓝 (ENNReal.ofReal (Real.exp (-(R^d)) * (R^d)^k / k.factorial) *
        (finiteMarkProduct (fun _ : Fin k => limitingMarkProbability hd hR) : Measure (Fin k → ℝ)) B)) := by
  have hc := ENNReal.tendsto_ofReal
    ((tendsto_shortEdge_binomial_mass_with_exclusions k skip hd hκ hR h).comp
      (tendsto_add_atTop_nat 1))
  have hm := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    (tendsto_retainedMarkProduct hd hκ hR h (Fin k)) hfront
  refine (ENNReal.Tendsto.mul hc (Or.inr (measure_ne_top _ _)) hm
    (Or.inr ENNReal.ofReal_ne_top)).congr' (Eventually.of_forall fun n => ?_)
  change ENNReal.ofReal (((n + 1 - skip).choose k : ℝ) *
    (shortEdgeProbability μ d κ R (n+1))^k *
    (1 - shortEdgeProbability μ d κ R (n+1))^(n+1-skip-k)) *
    (Measure.infinitePi (fun _ : Fin k => retainedLengthLaw μ d κ R (n+1))) B =
    iidCosts μ (oneRootMarkCountEvent v (labels (n+1)) d κ R (n+1) k B)
  simpa only [Fintype.card_fin] using
    (measure_oneRootMarkCountEvent μ v (labels (n+1)) k hκ hR h (Nat.zero_lt_succ n) hB).symm

end Certificate.LocalExploration

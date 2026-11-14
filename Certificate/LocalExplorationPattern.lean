import Mathlib.Probability.ProductMeasure
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset

/-!
# A marked binomial exposure

For independent entries indexed by a finite set, this file computes the
joint probability of the retained-label pattern and the length tests on
the retained entries. It also connects the actual retained-edge count to
the binomial formula.
-/

open Finset MeasureTheory
open scoped BigOperators ENNReal

namespace Certificate.LocalExploration

variable {ι Ω : Type*} [Fintype ι]

/-- Labels retained by a single exploration step. -/
noncomputable def retainedLabels (A : Set Ω) (x : ι → Ω) : Finset ι :=
  open Classical in univ.filter (fun i => x i ∈ A)

@[simp] theorem mem_retainedLabels (A : Set Ω) (x : ι → Ω) (i : ι) :
    i ∈ retainedLabels A x ↔ x i ∈ A := by
  classical
  simp [retainedLabels]

/-- Number of entries that are retained. -/
noncomputable def retainedCount (A : Set Ω) (x : ι → Ω) : ℕ :=
  (retainedLabels A x).card

/-- A prescribed set of retained labels, with extra tests for their marks. -/
def markedPattern (A : Set Ω) (S : Finset ι) (B : ι → Set Ω) : Set (ι → Ω) :=
  {x | retainedLabels A x = S ∧ ∀ i ∈ S, x i ∈ B i}

private theorem markedPattern_eq_pi (A : Set Ω) (S : Finset ι) (B : ι → Set Ω) :
    markedPattern A S B = Set.univ.pi (fun i => by classical exact if i ∈ S then A ∩ B i else Aᶜ) := by
  classical
  ext x
  simp only [Set.mem_pi, Set.mem_univ, true_implies, markedPattern, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hS, hB⟩ i
    by_cases hi : i ∈ S
    · rw [if_pos hi]
      exact ⟨(mem_retainedLabels A x i).1 (hS.symm ▸ hi), hB i hi⟩
    · rw [if_neg hi]
      intro hx
      exact hi (hS ▸ (mem_retainedLabels A x i).2 hx)
  · intro hx
    constructor
    · ext i
      rw [mem_retainedLabels]
      by_cases hi : i ∈ S
      · simpa only [hi, iff_true] using (show x i ∈ A from (by
          have h := hx i
          rw [if_pos hi] at h
          exact h.1))
      · have hn := hx i
        rw [if_neg hi] at hn
        exact iff_of_false hn hi
    · intro i hi
      have h := hx i
      rw [if_pos hi] at h
      exact h.2

variable [MeasurableSpace Ω]

theorem measurableSet_markedPattern {A : Set Ω} (hA : MeasurableSet A)
    (S : Finset ι) {B : ι → Set Ω} (hB : ∀ i ∈ S, MeasurableSet (B i)) :
    MeasurableSet (markedPattern A S B) := by
  classical
  rw [markedPattern_eq_pi]
  apply MeasurableSet.univ_pi
  intro i
  by_cases hi : i ∈ S
  · simpa only [if_pos hi] using hA.inter (hB i hi)
  · simpa only [if_neg hi] using hA.compl

/-- The marked-label exposure probability, including both chosen and rejected edges. -/
theorem measure_markedPattern (ν : Measure Ω) [IsProbabilityMeasure ν] {A : Set Ω}
    (hA : MeasurableSet A) (S : Finset ι) {B : ι → Set Ω}
    (hB : ∀ i ∈ S, MeasurableSet (B i)) :
    (Measure.infinitePi (fun _ : ι => ν)) (markedPattern A S B) =
      (∏ i ∈ S, ν (A ∩ B i)) * ν (Aᶜ) ^ (Fintype.card ι - S.card) := by
  classical
  rw [markedPattern_eq_pi, ← Finset.coe_univ]
  rw [Measure.infinitePi_pi]
  · simp_rw [apply_ite ν]
    rw [Finset.prod_ite, Finset.filter_mem_eq_inter, Finset.univ_inter,
      ← Finset.sdiff_eq_filter, Finset.prod_const, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ]
  · intro i _
    by_cases hi : i ∈ S
    · simpa only [if_pos hi] using hA.inter (hB i hi)
    · simpa only [if_neg hi] using hA.compl

theorem measurableSet_retainedLabels_eq {A : Set Ω} (hA : MeasurableSet A) (S : Finset ι) :
    MeasurableSet {x : ι → Ω | retainedLabels A x = S} := by
  simpa [markedPattern] using
    (measurableSet_markedPattern hA S (B := fun _ => Set.univ) (fun _ _ => MeasurableSet.univ))

theorem measure_retainedLabels_eq (ν : Measure Ω) [IsProbabilityMeasure ν] {A : Set Ω}
    (hA : MeasurableSet A) (S : Finset ι) :
    (Measure.infinitePi (fun _ : ι => ν)) {x : ι → Ω | retainedLabels A x = S} =
      ν A ^ S.card * ν (Aᶜ) ^ (Fintype.card ι - S.card) := by
  simpa [markedPattern] using
    (measure_markedPattern ν hA S (B := fun _ => Set.univ) (fun _ _ => MeasurableSet.univ))

private abbrev SizedLabelSet (ι : Type*) [Fintype ι] (k : ℕ) :=
  ↥((univ : Finset ι).powersetCard k)

omit [MeasurableSpace Ω] in
private theorem retainedCount_eq_union {A : Set Ω} (k : ℕ) :
    {x : ι → Ω | retainedCount A x = k} =
      ⋃ S : SizedLabelSet ι k, {x : ι → Ω | retainedLabels A x = S.val} := by
  classical
  ext x
  rw [Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · intro hx
    exact ⟨⟨retainedLabels A x, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hx⟩⟩, rfl⟩
  · rintro ⟨S, hS⟩
    unfold retainedCount
    exact congrArg Finset.card hS |>.trans (Finset.mem_powersetCard.mp S.property).2

theorem measurable_retainedCount {A : Set Ω} (hA : MeasurableSet A) :
    Measurable (retainedCount A : (ι → Ω) → ℕ) := by
  apply measurable_to_countable'
  intro k
  change MeasurableSet {x : ι → Ω | retainedCount A x = k}
  rw [retainedCount_eq_union]
  exact MeasurableSet.iUnion (fun S => measurableSet_retainedLabels_eq hA S.val)

/-- The number of retained entries among independent entries has exact binomial mass. -/
theorem measure_retainedCount_eq (ν : Measure Ω) [IsProbabilityMeasure ν] {A : Set Ω}
    (hA : MeasurableSet A) (k : ℕ) :
    (Measure.infinitePi (fun _ : ι => ν)) {x : ι → Ω | retainedCount A x = k} =
      ((Fintype.card ι).choose k : ℝ≥0∞) * ν A ^ k * ν (Aᶜ) ^ (Fintype.card ι - k) := by
  classical
  rw [retainedCount_eq_union, measure_iUnion, tsum_fintype]
  · suffices he : ∀ S : SizedLabelSet ι k,
        (Measure.infinitePi (fun _ : ι => ν)) {x : ι → Ω | retainedLabels A x = S.val} =
          ν A ^ k * ν (Aᶜ) ^ (Fintype.card ι - k) by
      simp [he, nsmul_eq_mul, mul_assoc]
    intro S
    rw [measure_retainedLabels_eq ν hA, (Finset.mem_powersetCard.mp S.property).2]
  · intro S T hST
    apply Set.disjoint_left.mpr
    intro x hS hT
    exact hST (Subtype.ext (hS.symm.trans hT))
  · intro S
    exact measurableSet_retainedLabels_eq hA S.val

/-- Distribution of one entry after retaining it. -/
noncomputable def conditionalRetainedLaw (ν : Measure Ω) (A : Set Ω) : Measure Ω :=
  (ν A)⁻¹ • ν.restrict A

/-- Conditional on the labels retained, tests on their marks have the product
of the normalized restricted laws. Written as a probability factorization so
it also applies to patterns of probability zero. -/
theorem measure_markedPattern_factorizes (ν : Measure Ω) [IsProbabilityMeasure ν]
    {A : Set Ω} (hA : MeasurableSet A) (hA₀ : ν A ≠ 0)
    (S : Finset ι) {B : ι → Set Ω} (hB : ∀ i ∈ S, MeasurableSet (B i)) :
    (Measure.infinitePi (fun _ : ι => ν)) (markedPattern A S B) =
      (Measure.infinitePi (fun _ : ι => ν)) {x : ι → Ω | retainedLabels A x = S} *
        ∏ i ∈ S, conditionalRetainedLaw ν A (B i) := by
  classical
  rw [measure_markedPattern ν hA S hB, measure_retainedLabels_eq ν hA]
  have he (i : ι) (hi : i ∈ S) : ν (A ∩ B i) = ν A * conditionalRetainedLaw ν A (B i) := by
    rw [conditionalRetainedLaw, Measure.smul_apply, Measure.restrict_apply (hB i hi),
      Set.inter_comm (B i) A, smul_eq_mul, ← mul_assoc, mul_comm (ν A),
      ENNReal.inv_mul_cancel hA₀ (measure_ne_top _ _), one_mul]
  calc
    ((∏ i ∈ S, ν (A ∩ B i)) * ν (Aᶜ) ^ (Fintype.card ι - S.card)) =
        (∏ i ∈ S, ν A * conditionalRetainedLaw ν A (B i)) * ν (Aᶜ) ^ (Fintype.card ι - S.card) := by
      rw [Finset.prod_congr rfl he]
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const, mul_right_comm]

end Certificate.LocalExploration

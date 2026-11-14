import Certificate.PoissonShift
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Marked Poisson processes built from independent finite batches

A countable family of finite intensity Poisson batches represents the points
in disjoint pieces of an intensity measure. This file works with the batches
and the countable product of their laws.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace Certificate

variable {X : Type*} [MeasurableSpace X]

/-- One finite batch of marks, with its realised count. -/
abbrev PoissonBatch (X : Type*) := Σ n : ℕ, Fin n → X

theorem measurable_poissonBatch_mk (n : ℕ) :
    Measurable (fun xs : Fin n → X => (⟨n, xs⟩ : PoissonBatch X)) := by
  rw [measurable_iff_le_map]
  exact iInf_le _ n

theorem measurable_on_poissonBatch {Y : Type*} [MeasurableSpace Y]
    {f : PoissonBatch X → Y} (hf : ∀ n, Measurable (f ∘ Sigma.mk n)) :
    Measurable f := by
  rw [measurable_iff_comap_le]
  apply le_iInf
  intro n
  rw [← MeasurableSpace.comap_le_iff_le_map, MeasurableSpace.comap_comp]
  exact (hf n).comap_le

/-- Conditional on the Poisson count, a batch consists of iid marks. -/
noncomputable def poissonBatchLaw (r : ℝ≥0) (μ : Measure X) : Measure (PoissonBatch X) :=
  Measure.sum (fun n => poissonMeasure r {n} •
    (Measure.pi (fun _ : Fin n => μ)).map (Sigma.mk n))

theorem lintegral_poissonBatchLaw (r : ℝ≥0) (μ : Measure X)
    {f : PoissonBatch X → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ b, f b ∂poissonBatchLaw r μ) =
      ∫⁻ n, (∫⁻ xs, f ⟨n, xs⟩ ∂Measure.pi (fun _ : Fin n => μ)) ∂poissonMeasure r := by
  rw [poissonBatchLaw, lintegral_sum_measure, lintegral_countable']
  apply tsum_congr
  intro n
  rw [lintegral_smul_measure, lintegral_map hf (measurable_poissonBatch_mk n)]
  exact mul_comm _ _

instance poissonBatchLaw_isProbabilityMeasure (r : ℝ≥0) (μ : Measure X)
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (poissonBatchLaw r μ) where
  measure_univ := by
    have h := lintegral_poissonBatchLaw r μ (f := fun _ => 1) measurable_const
    simpa only [lintegral_const, measure_univ, mul_one, one_mul] using h

section Refresh

variable {I Y : Type*} [MeasurableSpace Y] [DecidableEq I]

private theorem measurable_refresh (j : I) :
    Measurable (fun p : (I → Y) × Y => Function.update p.1 j p.2) := by
  apply measurable_pi_lambda
  intro i
  by_cases h : i = j
  · subst i
    simpa only [Function.update_self] using
      (measurable_snd : Measurable (Prod.snd : (I → Y) × Y → Y))
  · simpa only [Function.update_of_ne h, Function.comp_def] using
      ((measurable_pi_apply i).comp measurable_fst :
        Measurable (fun p : (I → Y) × Y => p.1 i))

omit [MeasurableSpace Y] in
private theorem refresh_preimage_of_mem (j : I) {s : Finset I} (hj : j ∈ s)
    (t : I → Set Y) :
    (fun p : (I → Y) × Y => Function.update p.1 j p.2) ⁻¹' Set.pi (↑s : Set I) t =
      (Set.pi (↑(s.erase j) : Set I) t) ×ˢ t j := by
  ext p
  change (∀ i, i ∈ s → Function.update p.1 j p.2 i ∈ t i) ↔
    (∀ i, i ∈ s.erase j → p.1 i ∈ t i) ∧ p.2 ∈ t j
  constructor
  · intro h
    refine ⟨?_, by simpa only [Function.update_self] using h j hj⟩
    intro i hi
    obtain ⟨hij, his⟩ := Finset.mem_erase.mp hi
    simpa only [Function.update_of_ne hij] using h i his
  · intro h i hi
    by_cases hij : i = j
    · subst i
      simpa only [Function.update_self] using h.2
    · simpa only [Function.update_of_ne hij] using h.1 i (Finset.mem_erase.mpr ⟨hij, hi⟩)

omit [MeasurableSpace Y] in
private theorem refresh_preimage_of_not_mem (j : I) {s : Finset I} (hj : j ∉ s)
    (t : I → Set Y) :
    (fun p : (I → Y) × Y => Function.update p.1 j p.2) ⁻¹' Set.pi (↑s : Set I) t =
      (Set.pi (↑s : Set I) t) ×ˢ (Set.univ : Set Y) := by
  ext p
  change (∀ i, i ∈ s → Function.update p.1 j p.2 i ∈ t i) ↔
    (∀ i, i ∈ s → p.1 i ∈ t i) ∧ p.2 ∈ Set.univ
  have hne (i : I) (hi : i ∈ s) : i ≠ j := fun H => hj (H ▸ hi)
  constructor
  · intro h
    exact ⟨fun i hi => by simpa only [Function.update_of_ne (hne i hi)] using h i hi,
      Set.mem_univ _⟩
  · intro h i hi
    simpa only [Function.update_of_ne (hne i hi)] using h.1 i hi

/-- Replacing one coordinate by an independent draw from its own law preserves
the product law. The product law and the refresh operation are explicit. -/
theorem infinitePi_refresh (ν : I → Measure Y) [∀ j, IsProbabilityMeasure (ν j)] (j : I) :
    MeasurePreserving (fun p : (I → Y) × Y => Function.update p.1 j p.2)
      ((Measure.infinitePi ν).prod (ν j)) (Measure.infinitePi ν) where
  measurable := measurable_refresh j
  map_eq := by
    apply Measure.eq_infinitePi ν
    intro s t ht
    rw [Measure.map_apply (measurable_refresh j)
      (MeasurableSet.pi s.countable_toSet (fun i _ => ht i))]
    by_cases hj : j ∈ s
    · rw [refresh_preimage_of_mem j hj, Measure.prod_prod,
        Measure.infinitePi_pi _ (fun i _ => ht i), Finset.prod_erase_mul _ _ hj]
    · rw [refresh_preimage_of_not_mem j hj, Measure.prod_prod, measure_univ, mul_one,
        Measure.infinitePi_pi _ (fun i _ => ht i)]

end Refresh

private theorem measurable_batch_count : Measurable (Sigma.fst : PoissonBatch X → ℕ) :=
  measurable_on_poissonBatch fun n => measurable_const (a := n)

private def batchMark (fallback : X) (i : ℕ) (b : PoissonBatch X) : X :=
  if hi : i < b.1 then b.2 ⟨i, hi⟩ else fallback

private theorem measurable_batchMark (fallback : X) (i : ℕ) :
    Measurable (batchMark fallback i) := by
  apply measurable_on_poissonBatch
  intro n
  by_cases hi : i < n
  · simpa only [Function.comp_def, batchMark, dif_pos hi] using
      (measurable_pi_apply (⟨i, hi⟩ : Fin n) : Measurable (fun xs : Fin n → X => xs ⟨i, hi⟩))
  · simpa only [Function.comp_def, batchMark, dif_neg hi] using
      (measurable_const (a := fallback) : Measurable (fun _ : Fin n → X => fallback))

/-- Delete the mark with index `i` when it is present. -/
def erasePoissonMark (i : ℕ) : PoissonBatch X → PoissonBatch X
  | ⟨0, xs⟩ => ⟨0, xs⟩
  | ⟨n+1, xs⟩ =>
    if hi : i < n+1 then ⟨n, fun j => xs ((⟨i,hi⟩ : Fin (n+1)).succAbove j)⟩
    else ⟨n+1, xs⟩

private theorem measurable_erasePoissonMark (i : ℕ) :
    Measurable (erasePoissonMark i : PoissonBatch X → PoissonBatch X) := by
  apply measurable_on_poissonBatch
  intro n
  cases n with
  | zero => exact measurable_poissonBatch_mk 0
  | succ n =>
    by_cases hi : i < n+1
    · simp only [Function.comp_def, erasePoissonMark, dif_pos hi]
      exact (measurable_poissonBatch_mk n).comp (measurable_pi_lambda _ fun j => measurable_pi_apply _)
    · simp only [Function.comp_def, erasePoissonMark, dif_neg hi]
      exact measurable_poissonBatch_mk (n+1)

/-- Sum a nonnegative test over the marks, with each chosen mark removed from
the batch before the test is evaluated. -/
noncomputable def poissonBatchDeletionSum (fallback : X)
    (f : X × PoissonBatch X → ℝ≥0∞) (b : PoissonBatch X) : ℝ≥0∞ :=
  ∑' i : ℕ, if i < b.1 then f (batchMark fallback i b, erasePoissonMark i b) else 0

private theorem measurable_poissonBatchDeletionSum {Ω : Type*} [MeasurableSpace Ω]
    (fallback : X) {b : Ω → PoissonBatch X} (hb : Measurable b)
    {f : Ω × (X × PoissonBatch X) → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun ω => poissonBatchDeletionSum fallback (fun z => f (ω,z)) (b ω)) := by
  apply Measurable.tsum
  intro i
  have hc : Measurable (fun ω => (b ω).1) := measurable_batch_count.comp hb
  have hp : MeasurableSet {ω | i < (b ω).1} :=
    hc ((Set.to_countable (Ioi i)).measurableSet)
  exact Measurable.ite hp (hf.comp (measurable_id.prodMk
    (((measurable_batchMark fallback i).comp hb).prodMk
      ((measurable_erasePoissonMark i).comp hb)))) measurable_const

private theorem batchDeletion_eq_conditional (fallback : X) (μ : Measure X)
    (f : X × PoissonBatch X → ℝ≥0∞) (n : ℕ) :
    (∫⁻ xs, poissonBatchDeletionSum fallback f ⟨n,xs⟩ ∂Measure.pi (fun _ : Fin n => μ)) =
      conditionalDeletion μ (fun k p => f (p.1, ⟨k,p.2⟩)) n := by
  have hsum (n : ℕ) (xs : Fin n → X) :
      poissonBatchDeletionSum fallback f ⟨n,xs⟩ =
        ∑ i : Fin n, if (i : ℕ) < n then
          f (batchMark fallback i ⟨n,xs⟩, erasePoissonMark i ⟨n,xs⟩) else 0 := by
    unfold poissonBatchDeletionSum
    rw [tsum_eq_sum (s := Finset.range n), ← Fin.sum_univ_eq_sum_range]
    intro i hi
    rw [Finset.mem_range] at hi
    simp [hi]
  cases n with
  | zero => simp [hsum, conditionalDeletion]
  | succ n =>
    unfold conditionalDeletion
    apply lintegral_congr
    intro xs
    rw [hsum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Fin.is_lt, if_true, batchMark, dif_pos, erasePoissonMark]
    rfl

/-- Insertion for a single batch, with the original and remaining numbers of
marks encoded in the batch. -/
theorem poissonBatch_insertion (fallback : X) (r : ℝ≥0)
    (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X × PoissonBatch X → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ b, poissonBatchDeletionSum fallback f b ∂poissonBatchLaw r μ) =
      (r : ℝ≥0∞) * ∫⁻ z, f z ∂μ.prod (poissonBatchLaw r μ) := by
  let F (n : ℕ) (p : X × (Fin n → X)) := f (p.1, ⟨n,p.2⟩)
  have hF (n : ℕ) : Measurable (F n) :=
    hf.comp (measurable_fst.prodMk ((measurable_poissonBatch_mk n).comp measurable_snd))
  have hm : Measurable (poissonBatchDeletionSum fallback f) := by
    apply measurable_poissonBatchDeletionSum fallback measurable_id (hf.comp measurable_snd)
  rw [lintegral_poissonBatchLaw r μ hm]
  simp_rw [batchDeletion_eq_conditional]
  rw [finite_marked_poisson_insertion r μ F hF]
  congr 1
  rw [lintegral_countable', poissonBatchLaw, Measure.prod_sum_right, lintegral_sum_measure]
  apply tsum_congr
  intro n
  let ν := Measure.pi (fun _ : Fin n => μ)
  let mk : (Fin n → X) → PoissonBatch X := fun xs => ⟨n,xs⟩
  have hmk : Measurable mk := measurable_poissonBatch_mk n
  have hmap : μ.prod (ν.map mk) =
      (μ.prod ν).map (Prod.map id mk) := by
    simpa only [Measure.map_id] using Measure.map_prod_map μ ν measurable_id hmk
  have hsymm : μ.prod (poissonMeasure r {n} • ν.map mk) =
      poissonMeasure r {n} • μ.prod (ν.map mk) := by
    exact Measure.prod_smul_right _
  rw [hsymm, lintegral_smul_measure, hmap, lintegral_map hf (measurable_id.prodMap hmk)]
  exact mul_comm _ _

section Countable

variable {I : Type*} [DecidableEq I]

/-- The law of independent Poisson batches in the pieces indexed by `I`. -/
noncomputable def poissonProcessLaw (rate : I → ℝ≥0) (μ : I → Measure X) :
    Measure (I → PoissonBatch X) :=
  Measure.infinitePi (fun i => poissonBatchLaw (rate i) (μ i))

instance poissonProcessLaw_isProbabilityMeasure
    (rate : I → ℝ≥0) (μ : I → Measure X) [∀ i, IsProbabilityMeasure (μ i)] :
    IsProbabilityMeasure (poissonProcessLaw rate μ) :=
  inferInstanceAs (IsProbabilityMeasure
    (Measure.infinitePi (fun i => poissonBatchLaw (rate i) (μ i))))

private theorem integral_insertion_refresh
    {Y : Type*} [MeasurableSpace Y] (ν : I → Measure Y)
    [∀ j, IsProbabilityMeasure (ν j)] (j : I)
    (μ : Measure X) [IsProbabilityMeasure μ]
    {g : X × (I → Y) → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ ω, ∫⁻ z, g (z.1, Function.update ω j z.2) ∂μ.prod (ν j) ∂Measure.infinitePi ν) =
      ∫⁻ z, g z ∂μ.prod (Measure.infinitePi ν) := by
  let P := Measure.infinitePi ν
  let F := fun (x : X) (p : (I → Y) × Y) => g (x, Function.update p.1 j p.2)
  have hF (x : X) : Measurable (F x) :=
    hg.comp (measurable_const.prodMk (measurable_refresh j))
  have hF' (ω : I → Y) : Measurable (fun z : X × Y => F z.1 (ω,z.2)) :=
    hg.comp (measurable_fst.prodMk
      ((measurable_refresh j).comp (measurable_const.prodMk measurable_snd)))
  let A (p : (I → Y) × X) : ℝ≥0∞ := ∫⁻ b, F p.2 (p.1,b) ∂ν j
  have hM : Measurable (fun p : ((I → Y) × X) × Y => F p.1.2 (p.1.1,p.2)) :=
    hg.comp ((measurable_snd.comp measurable_fst).prodMk
      ((measurable_refresh j).comp
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd)))
  have hA : Measurable A := hM.lintegral_prod_right' (ν := ν j)
  change (∫⁻ ω, ∫⁻ z, F z.1 (ω,z.2) ∂μ.prod (ν j) ∂P) = _
  calc
    _ = ∫⁻ ω, ∫⁻ x, A (ω,x) ∂μ ∂P :=
      lintegral_congr (fun ω => lintegral_prod _ (hF' ω).aemeasurable)
    _ = ∫⁻ x, ∫⁻ ω, A (ω,x) ∂P ∂μ := lintegral_lintegral_swap hA.aemeasurable
    _ = ∫⁻ x, ∫⁻ p, F x p ∂P.prod (ν j) ∂μ :=
      lintegral_congr (fun x => (lintegral_prod _ (hF x).aemeasurable).symm)
    _ = ∫⁻ x, ∫⁻ ω, g (x,ω) ∂P ∂μ :=
      lintegral_congr (fun x => (infinitePi_refresh ν j).lintegral_comp
        (hg.comp (measurable_const.prodMk measurable_id)))
    _ = ∫⁻ z, g z ∂μ.prod P := (lintegral_prod _ hg.aemeasurable).symm

/-- Nonnegative marked insertion for countably many independent finite intensity
pieces. The test may depend on the distinguished mark, its piece, and all
remaining batches. No finite-window restriction on the test is required. -/
theorem countable_marked_poisson_insertion [Countable I]
    (fallback : X) (rate : I → ℝ≥0) (μ : I → Measure X)
    [∀ j, IsProbabilityMeasure (μ j)]
    (g : I → X × (I → PoissonBatch X) → ℝ≥0∞) (hg : ∀ j, Measurable (g j)) :
    (∫⁻ ω, ∑' j, poissonBatchDeletionSum fallback
        (fun z => g j (z.1, Function.update ω j z.2)) (ω j)
      ∂poissonProcessLaw rate μ) =
      ∑' j, (rate j : ℝ≥0∞) *
        ∫⁻ z, g j z ∂(μ j).prod (poissonProcessLaw rate μ) := by
  let ν := fun j => poissonBatchLaw (rate j) (μ j)
  let P := poissonProcessLaw rate μ
  let F (j : I) (ω : I → PoissonBatch X) :=
    poissonBatchDeletionSum fallback (fun z => g j (z.1, Function.update ω j z.2)) (ω j)
  have hF (j : I) : Measurable (F j) :=
    measurable_poissonBatchDeletionSum fallback (measurable_pi_apply j)
      ((hg j).comp ((measurable_fst.comp measurable_snd).prodMk
        ((measurable_refresh j).comp (measurable_fst.prodMk
          (measurable_snd.comp measurable_snd)))))
  change (∫⁻ ω, ∑' j, F j ω ∂P) = _
  rw [lintegral_tsum (fun j => (hF j).aemeasurable)]
  apply tsum_congr
  intro j
  have htuple (ω : I → PoissonBatch X) :
      Measurable (fun z : X × PoissonBatch X => g j (z.1, Function.update ω j z.2)) :=
    (hg j).comp (measurable_fst.prodMk
      ((measurable_refresh j).comp (measurable_const.prodMk measurable_snd)))
  have hrefresh := infinitePi_refresh ν j
  calc
    _ = ∫⁻ p, F j (Function.update p.1 j p.2) ∂P.prod (ν j) :=
      (hrefresh.lintegral_comp (hF j)).symm
    _ = ∫⁻ ω, ∫⁻ b, poissonBatchDeletionSum fallback
          (fun z => g j (z.1, Function.update ω j z.2)) b ∂ν j ∂P := by
      have hM : Measurable (fun p : (I → PoissonBatch X) × PoissonBatch X =>
          F j (Function.update p.1 j p.2)) :=
        (hF j).comp (measurable_refresh j)
      rw [lintegral_prod _ hM.aemeasurable]
      simp only [F, Function.update_self, Function.update_idem]
    _ = ∫⁻ ω, (rate j : ℝ≥0∞) *
          ∫⁻ z, g j (z.1, Function.update ω j z.2) ∂(μ j).prod (ν j) ∂P :=
      lintegral_congr (fun ω => poissonBatch_insertion fallback (rate j) (μ j) _ (htuple ω))
    _ = (rate j : ℝ≥0∞) *
          ∫⁻ ω, ∫⁻ z, g j (z.1, Function.update ω j z.2) ∂(μ j).prod (ν j) ∂P := by
      rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top]
    _ = (rate j : ℝ≥0∞) * ∫⁻ z, g j z ∂(μ j).prod P :=
      congrArg (fun t : ℝ≥0∞ => (rate j : ℝ≥0∞) * t)
        (integral_insertion_refresh ν j (μ j) (hg j))

/-- The superposition intensity of the batches. -/
noncomputable def poissonIntensity (rate : I → ℝ≥0) (μ : I → Measure X) : Measure X :=
  Measure.sum (fun i => (rate i : ℝ≥0∞) • μ i)

/-- Marked insertion with the superposition intensity as one measure. -/
theorem poisson_insertion [Countable I]
    (fallback : X) (rate : I → ℝ≥0) (μ : I → Measure X)
    [∀ j, IsProbabilityMeasure (μ j)]
    (g : X × (I → PoissonBatch X) → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ ω, ∑' j, poissonBatchDeletionSum fallback
        (fun z => g (z.1, Function.update ω j z.2)) (ω j)
      ∂poissonProcessLaw rate μ) =
      ∫⁻ z, g z ∂(poissonIntensity rate μ).prod (poissonProcessLaw rate μ) := by
  rw [countable_marked_poisson_insertion fallback rate μ (fun _ => g) (fun _ => hg)]
  rw [poissonIntensity, Measure.prod_sum_left, lintegral_sum_measure]
  simp_rw [Measure.prod_smul_left, lintegral_smul_measure, smul_eq_mul]

/-- The sum of a function over the marks in one batch. -/
noncomputable def poissonBatchSum (fallback : X)
    (f : X → ℝ≥0∞) (b : PoissonBatch X) : ℝ≥0∞ :=
  poissonBatchDeletionSum fallback (fun z => f z.1) b

omit [MeasurableSpace X] in
/-- Express the marked deletion sum as a finite sum over all actual marks. -/
theorem poissonBatchDeletionSum_eq_sum (fallback : X) (f : X × PoissonBatch X → ℝ≥0∞)
    (b : PoissonBatch X) :
    poissonBatchDeletionSum fallback f b =
      ∑ i : Fin b.1, f (b.2 i, erasePoissonMark i.val b) := by
  obtain ⟨n, xs⟩ := b
  unfold poissonBatchDeletionSum
  rw [tsum_eq_sum (s := Finset.range n), ← Fin.sum_univ_eq_sum_range]
  · apply Finset.sum_congr rfl
    intro i _
    simp [batchMark, i.isLt]
  · intro i hi
    rw [Finset.mem_range] at hi
    simp [hi]

omit [MeasurableSpace X] in
/-- Express the batch sum as an ordinary finite sum of its actual marks. -/
theorem poissonBatchSum_eq_sum (fallback : X) (f : X → ℝ≥0∞) (b : PoissonBatch X) :
    poissonBatchSum fallback f b = ∑ i : Fin b.1, f (b.2 i) :=
  poissonBatchDeletionSum_eq_sum fallback (fun p => f p.1) b

theorem measurable_poissonBatchSum (fallback : X)
    (f : X → ℝ≥0∞) (hf : Measurable f) :
    Measurable (poissonBatchSum fallback f) :=
  measurable_poissonBatchDeletionSum fallback measurable_id
    (hf.comp (measurable_fst.comp measurable_snd))

/-- Campbell's first-moment formula for the marked process. -/
theorem poisson_campbell [Countable I]
    (fallback : X) (rate : I → ℝ≥0) (μ : I → Measure X)
    [∀ j, IsProbabilityMeasure (μ j)]
    (f : X → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, ∑' j, poissonBatchSum fallback f (ω j) ∂poissonProcessLaw rate μ) =
      ∫⁻ x, f x ∂poissonIntensity rate μ := by
  have H := poisson_insertion fallback rate μ (fun z => f z.1) (hf.comp measurable_fst)
  rw [lintegral_prod (fun z : X × (I → PoissonBatch X) => f z.1)
    (hf.comp measurable_fst).aemeasurable] at H
  simpa only [poissonBatchSum, lintegral_const, measure_univ, mul_one] using H

end Countable

section SigmaFinite

variable (τ : Measure X) [SigmaFinite τ]

private theorem poisson_piece_lt_top (n : ℕ) :
    τ (disjointed (spanningSets τ) n) < ∞ :=
  (measure_mono (disjointed_subset _ _)).trans_lt (measure_spanningSets_lt_top τ n)

/-- The finite mass of each piece in a disjoint σ-finite exhaustion. -/
noncomputable def sigmaFinitePoissonRate (n : ℕ) : ℝ≥0 :=
  (τ (disjointed (spanningSets τ) n)).toNNReal

/-- Restriction to an exhaustion piece, normalized to mass one. At zero rate
the choice of mark law has no effect on the process. -/
noncomputable def sigmaFinitePoissonMarks (fallback : X) (n : ℕ) : Measure X :=
  let s := disjointed (spanningSets τ) n
  if τ s = 0 then Measure.dirac fallback else (τ s)⁻¹ • τ.restrict s

instance sigmaFinitePoissonMarks_isProbabilityMeasure (fallback : X) (n : ℕ) :
    IsProbabilityMeasure (sigmaFinitePoissonMarks τ fallback n) := by
  unfold sigmaFinitePoissonMarks
  dsimp only
  split_ifs with h
  · infer_instance
  · constructor
    rw [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul,
      ENNReal.inv_mul_cancel h (poisson_piece_lt_top τ n).ne]

/-- Summing the normalized exhaustion pieces with their rates recovers the
original σ-finite measure. -/
theorem sigmaFinite_poissonIntensity (fallback : X) :
    poissonIntensity (sigmaFinitePoissonRate τ) (sigmaFinitePoissonMarks τ fallback) = τ := by
  unfold poissonIntensity
  trans Measure.sum (fun n ↦ τ.restrict (disjointed (spanningSets τ) n))
  · congr 1
    funext n
    rw [sigmaFinitePoissonRate, ENNReal.coe_toNNReal (poisson_piece_lt_top τ n).ne]
    unfold sigmaFinitePoissonMarks
    dsimp only
    split_ifs with h
    · rw [h, zero_smul, Measure.restrict_eq_zero.mpr h]
    · rw [smul_smul, ENNReal.mul_inv_cancel h (poisson_piece_lt_top τ n).ne, one_smul]
  · exact sum_restrict_disjointed_spanningSets τ τ

/-- A concrete canonical batch process at any σ-finite intensity. -/
noncomputable def sigmaFinitePoissonLaw (fallback : X) : Measure (ℕ → PoissonBatch X) :=
  poissonProcessLaw (sigmaFinitePoissonRate τ) (sigmaFinitePoissonMarks τ fallback)

instance sigmaFinitePoissonLaw_isProbabilityMeasure (fallback : X) :
    IsProbabilityMeasure (sigmaFinitePoissonLaw τ fallback) :=
  inferInstanceAs (IsProbabilityMeasure
    (poissonProcessLaw (sigmaFinitePoissonRate τ) (sigmaFinitePoissonMarks τ fallback)))

/-- Mecke's deletion identity for the canonical countable batch representation
of a σ-finite intensity. -/
theorem sigmaFinite_poisson_insertion (fallback : X)
    (g : X × (ℕ → PoissonBatch X) → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ ω, ∑' j, poissonBatchDeletionSum fallback
        (fun z => g (z.1, Function.update ω j z.2)) (ω j)
      ∂sigmaFinitePoissonLaw τ fallback) =
      ∫⁻ z, g z ∂τ.prod (sigmaFinitePoissonLaw τ fallback) := by
  unfold sigmaFinitePoissonLaw
  rw [poisson_insertion fallback _ _ g hg, sigmaFinite_poissonIntensity]

/-- Campbell's expectation at an arbitrary σ-finite intensity. -/
theorem sigmaFinite_poisson_campbell (fallback : X)
    (f : X → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, ∑' j, poissonBatchSum fallback f (ω j)
      ∂sigmaFinitePoissonLaw τ fallback) = ∫⁻ x, f x ∂τ := by
  unfold sigmaFinitePoissonLaw
  rw [poisson_campbell fallback _ _ f hf, sigmaFinite_poissonIntensity]

end SigmaFinite

end Certificate

import Certificate.CanonicalWindowMarks
import Certificate.CanonicalShapeCounts
import Certificate.CanonicalTreeKernel
import Certificate.PoissonFull

/-! The finite-depth cutoff bracket recursion with Poisson and iid inputs. -/

open Finset Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Certificate.CanonicalTree

abbrev Bracket := ℝ × ℝ
abbrev ChildMark := ℝ × Bracket

/-- Apply both cavity updates to a finite batch of marked child brackets. -/
noncomputable def cutoffBracketUpdate (β z : ℝ) (b : PoissonBatch ChildMark) : Bracket :=
  let sum (p : Bracket → ℝ) := ∑ i : Fin b.1, Real.exp (-β * (b.2 i).1) * p (b.2 i).2
  ((z + sum Prod.snd)⁻¹, (z + sum Prod.fst)⁻¹)

theorem measurable_cutoffBracketUpdate (β z : ℝ) : Measurable (cutoffBracketUpdate β z) := by
  apply measurable_on_poissonBatch
  intro n
  have hsum (p : Bracket → ℝ) (hp : Measurable p) :
      Measurable (fun b : Fin n → ChildMark => ∑ i : Fin n, Real.exp (-β * (b i).1) * p (b i).2) := by
    refine Finset.measurable_fun_sum _ fun i _ => ?_
    have h : Measurable (fun b : Fin n → ChildMark => b i) := measurable_pi_apply i
    exact (Real.measurable_exp.comp (h.fst.const_mul (-β))).mul (hp.comp h.snd)
  exact ((measurable_const.add (hsum Prod.snd measurable_snd)).inv).prodMk
    ((measurable_const.add (hsum Prod.fst measurable_fst)).inv)

theorem cutoffBracketUpdate_perm (β z : ℝ) {n : ℕ}
    (x : Fin n → ChildMark) (σ : Equiv.Perm (Fin n)) :
    cutoffBracketUpdate β z ⟨n, x ∘ σ⟩ = cutoffBracketUpdate β z ⟨n, x⟩ := by
  have hsum (p : Bracket → ℝ) :
      (∑ i : Fin n, Real.exp (-β * (x (σ i)).1) * p (x (σ i)).2) =
        ∑ i : Fin n, Real.exp (-β * (x i).1) * p (x i).2 :=
    Fintype.sum_equiv σ _ _ (fun _ => rfl)
  change ((z + ∑ i : Fin n, Real.exp (-β * (x (σ i)).1) * (x (σ i)).2.2)⁻¹,
      (z + ∑ i : Fin n, Real.exp (-β * (x (σ i)).1) * (x (σ i)).2.1)⁻¹) = _
  rw [hsum Prod.snd, hsum Prod.fst]
  rfl

/-- One child input has a normalized retained length and an independent bracket
at depth k. -/
noncomputable def cutoffBracketMarkLaw (β d R z : ℝ) (k : ℕ) : Measure ChildMark :=
  (((ENNReal.ofReal (R ^ d))⁻¹ • (intensity d).restrict (Set.Ioc 0 R)).prod
    (law.map (depthFor (cutoffKernel β R) d z k [])))

def rootCutoffCountEvent (d R : ℝ) (n : ℕ) : Set Environment :=
  {ω | cutoffOffspring d R (ω []) = (n : ℝ≥0∞)}

private theorem measurableSet_rootCutoffCountEvent (d R : ℝ) (n : ℕ) :
    MeasurableSet (rootCutoffCountEvent d R n) :=
  measurableSet_eq_fun ((measurable_cutoffOffspring d R).comp (measurable_pi_apply [])) measurable_const

private theorem depthFor_branch_eq (K : ℝ → ℝ) (d z : ℝ) (k : ℕ)
    (v : Vertex) (ω : Environment) (i : ℕ) :
    depthFor K d z k v (branch i ω) = depthFor K d z k (i :: v) ω := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih =>
    simp only [depthFor, TreeBoundary.bounds] at ih ⊢
    have hc (j : ℕ) : i :: child v j = child (i :: v) j := rfl
    have hw : weightFor K d (branch i ω) v = weightFor K d ω (i :: v) := rfl
    simp only [ih, hc, hw]

private noncomputable def rootBracketData (β d R z : ℝ) (k : ℕ) (ω : Environment) :
    Spacings × (ℕ → Bracket) :=
  (ω [], fun i => depthFor (cutoffKernel β R) d z k [] (branch i ω))

private theorem measurable_rootBracketData (β d R z : ℝ) (k : ℕ) :
    Measurable (rootBracketData β d R z k) :=
  (measurable_pi_apply []).prodMk (measurable_pi_iff.mpr fun i =>
    (measurable_depthFor (measurable_cutoffKernel β R) d z k []).comp (measurable_branch i))

private theorem map_rootBracketData (β d R z : ℝ) (k : ℕ) :
    law.map (rootBracketData β d R z k) =
      markedArrivalSequenceLaw (law.map (depthFor (cutoffKernel β R) d z k [])) :=
  map_root_marks (measurable_depthFor (measurable_cutoffKernel β R) d z k [])

private theorem windowEvent_rootBracketData_iff (β d R z : ℝ) (k n : ℕ) (ω : Environment) :
    rootBracketData β d R z k ω ∈ arrivalWindowCountEvent d R n ↔ ω ∈ rootCutoffCountEvent d R n := by
  change markedArrivalCount d (arrivalWindow R) (rootBracketData β d R z k ω) = (n : ℝ≥0∞) ↔
    cutoffOffspring d R (ω []) = (n : ℝ≥0∞)
  have h : markedArrivalCount d (arrivalWindow R) (rootBracketData β d R z k ω) =
      cutoffOffspring d R (ω []) := by
    unfold markedArrivalCount cutoffOffspring
    apply tsum_congr
    intro j
    let x := arrivalLength d (ω []) j
    let y := depthFor (cutoffKernel β R) d z k [] (branch j ω)
    change (Ioc 0 R ×ˢ (Set.univ : Set Bracket)).indicator (fun _ => (1 : ℝ≥0∞)) (x, y) =
      (Ioc 0 R ×ˢ (Set.univ : Set Unit)).indicator (fun _ => (1 : ℝ≥0∞)) (x, ())
    by_cases h : x ∈ Ioc 0 R <;> simp [h]
  rw [h]

private theorem ae_root_spacing_pos : ∀ᵐ ω ∂law, ∀ i, 0 < ω [] i := by
  let : IsProbabilityMeasure exponentialSpacings := isProbabilityMeasure_exponentialSpacings
  have h := measurePreserving_eval_infinitePi (fun _ : Vertex => exponentialSpacings) []
  exact h.quasiMeasurePreserving.tendsto_ae.eventually ae_expSpacing_pos

private theorem depthFor_cutoff_eq_windowUpdate {β d R z : ℝ} (hd : 0 < d)
    (k n : ℕ) (ω : Environment) (hpos : ∀ i, 0 < ω [] i)
    (hn : ω ∈ rootCutoffCountEvent d R n) :
    depthFor (cutoffKernel β R) d z (k+1) [] ω =
      cutoffBracketUpdate β z ⟨n, firstMarkedArrivals d n (rootBracketData β d R z k ω)⟩ := by
  let K := cutoffKernel β R
  let D := rootBracketData β d R z k ω
  have hD : D ∈ arrivalWindowCountEvent d R n := (windowEvent_rootBracketData_iff β d R z k n ω).2 hn
  have hw (i : ℕ) : arrivalLength d (ω []) i ∈ Ioc 0 R ↔ i < n := by
    have h := markedArrivalPoint_mem_window_iff_of_count (i := i) hd hpos hD
    simpa only [D, arrivalWindow, markedArrivalPoint, rootBracketData, Set.mem_prod, Set.mem_univ,
      and_true] using h
  have hlen (i : ℕ) : 0 < arrivalLength d (ω []) i := by
    unfold arrivalLength
    exact Real.rpow_pos_of_pos (Finset.sum_pos (fun j _ => hpos j) Finset.nonempty_range_add_one) _
  have hsum (p : Bracket → ℝ) :
      (∑' i, weightFor K d ω [] i * p (depthFor K d z k (child [] i) ω)) =
        ∑ i : Fin n, Real.exp (-β * (firstMarkedArrivals d n D i).1) *
          p (firstMarkedArrivals d n D i).2 := by
    let f (i : ℕ) := weightFor K d ω [] i * p (depthFor K d z k (child [] i) ω)
    have hs (i : ℕ) (hi : i ∉ Finset.range n) : f i = 0 := by
      have hn' : ¬ arrivalLength d (ω []) i ≤ R := fun hi' => hi
        (Finset.mem_range.mpr ((hw i).mp ⟨hlen i, hi'⟩))
      dsimp only [f, weightFor, K, cutoffKernel]
      rw [if_neg hn', zero_mul]
    have ht : (∑' i, f i) = ∑ i ∈ Finset.range n, f i := tsum_eq_sum hs
    change (∑' i, f i) = _
    rw [ht, ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    have hh := (hw i).mpr i.isLt
    have hchild : depthFor K d z k [] (branch i ω) = depthFor K d z k (child [] i) ω :=
      depthFor_branch_eq K d z k [] ω i
    change cutoffKernel β R (arrivalLength d (ω []) i) * p (depthFor K d z k (child [] i) ω) =
      Real.exp (-β * arrivalLength d (ω []) i) * p (depthFor K d z k [] (branch i ω))
    rw [hchild, cutoffKernel, if_pos hh.2]
  change ((z + ∑' i, weightFor K d ω [] i * (depthFor K d z k (child [] i) ω).2)⁻¹,
    (z + ∑' i, weightFor K d ω [] i * (depthFor K d z k (child [] i) ω).1)⁻¹) = _
  rw [hsum Prod.snd, hsum Prod.fst]
  rfl

/-- At a prescribed root count, the next-depth bracket is the symmetric
finite update of iid marked children, weighted by the exact Poisson mass. -/
theorem lintegral_cutoffDepth_succ_on_count {β d R z : ℝ} (hd : 0 < d) (hR : 0 < R)
    (k n : ℕ) (f : Bracket → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω in rootCutoffCountEvent d R n, f (depthFor (cutoffKernel β R) d z (k+1) [] ω) ∂law) =
      poissonMeasure (ENNReal.ofReal (R ^ d)).toNNReal {n} *
        ∫⁻ xs, f (cutoffBracketUpdate β z ⟨n, xs⟩)
          ∂Measure.pi (fun _ : Fin n => cutoffBracketMarkLaw β d R z k) := by
  let K := cutoffKernel β R
  let μ := law.map (depthFor K d z k [])
  let D := rootBracketData β d R z k
  let P := markedArrivalSequenceLaw μ
  let a := arrivalWindowCountEvent (Y := Bracket) d R n
  let b := rootCutoffCountEvent d R n
  let F (xs : Fin n → ChildMark) := f (cutoffBracketUpdate β z ⟨n, xs⟩)
  let : IsProbabilityMeasure law := isProbabilityMeasure_law
  let : IsProbabilityMeasure μ :=
    Measure.isProbabilityMeasure_map (measurable_depthFor (measurable_cutoffKernel β R) d z k []).aemeasurable
  have hD : Measurable D := measurable_rootBracketData β d R z k
  have hF : Measurable F := hf.comp ((measurable_cutoffBracketUpdate β z).comp (measurable_poissonBatch_mk n))
  have hA : MeasurableSet (arrivalWindow (Y := Bracket) R) := measurableSet_Ioc.prod MeasurableSet.univ
  have ha : MeasurableSet a :=
    measurableSet_eq_fun (measurable_markedArrivalCount d hA) measurable_const
  have hb : MeasurableSet b := measurableSet_rootCutoffCountEvent d R n
  have ht : Measurable (fun ω : Spacings × (ℕ → Bracket) => firstMarkedArrivals d n ω) := by
    apply measurable_pi_iff.mpr
    intro i
    unfold firstMarkedArrivals markedArrivalPoint arrivalLength
    fun_prop
  have hlaw : law.map D = P := map_rootBracketData β d R z k
  calc
    _ = ∫⁻ ω in b, F (firstMarkedArrivals d n (D ω)) ∂law := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hb, ae_mono (Measure.restrict_le_self) ae_root_spacing_pos] with ω hω hpos
      exact congrArg f (depthFor_cutoff_eq_windowUpdate hd k n ω hpos hω)
    _ = ∫⁻ v in a, F (firstMarkedArrivals d n v) ∂P := by
      rw [← hlaw, ← lintegral_indicator ha, ← lintegral_indicator hb]
      have hg : Measurable (fun v : Spacings × (ℕ → Bracket) => F (firstMarkedArrivals d n v)) :=
        hF.comp ht
      rw [lintegral_map (hg.indicator ha) hD]
      refine lintegral_congr fun ω => ?_
      have hiff : D ω ∈ a ↔ ω ∈ b := windowEvent_rootBracketData_iff β d R z k n ω
      by_cases hp : ω ∈ b
      · rw [indicator_of_mem hp, indicator_of_mem (hiff.mpr hp)]
      · rw [indicator_of_notMem hp, indicator_of_notMem (mt hiff.mp hp)]
    _ = _ := by
      have hmass : ((intensity d).prod μ) (arrivalWindow R) = ENNReal.ofReal (R ^ d) := by
        unfold arrivalWindow
        rw [Measure.prod_prod, intensity_Ioc_zero hd hR.le, measure_univ, mul_one]
      have hfin : ((intensity d).prod μ) (arrivalWindow R) ≠ ∞ := by
        rw [hmass]
        exact ENNReal.ofReal_ne_top
      have hc := canonical_iid_marked_count_probability hd μ hA hfin n
      change P a = _ at hc
      rw [hmass] at hc
      rw [lintegral_canonical_window_marks hd hR μ n F hF
        (fun xs σ => congrArg f (cutoffBracketUpdate_perm β z xs σ)), hc,
        conditionalWindowMarkLaw_eq_prod hd hR μ]
      rfl

theorem measure_rootCutoffCountEvent {d R : ℝ} (hd : 0 < d) (hR : 0 ≤ R) (n : ℕ) :
    law (rootCutoffCountEvent d R n) = poissonMeasure (ENNReal.ofReal (R ^ d)).toNNReal {n} := by
  let : IsProbabilityMeasure exponentialSpacings := isProbabilityMeasure_exponentialSpacings
  let e : Set Spacings := {E | cutoffOffspring d R E = (n : ℝ≥0∞)}
  have he : MeasurableSet e := measurableSet_eq_fun (measurable_cutoffOffspring d R) measurable_const
  have h := (measurePreserving_eval_infinitePi (fun _ : Vertex => exponentialSpacings) [])
  calc
    _ = exponentialSpacings e := by
      change law ((fun ω : Environment => ω []) ⁻¹' e) = _
      rw [← h.map_eq, Measure.map_apply h.measurable he]
      rfl
    _ = _ := measure_cutoffOffspring_eq hd hR n

/-- Integrating the depth successor is the same as drawing a Poisson batch
of independent child inputs and applying the finite update. -/
theorem lintegral_cutoffDepth_succ_eq_poissonBatch {β d R z : ℝ} (hd : 0 < d) (hR : 0 < R)
    (k : ℕ) (f : Bracket → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, f (depthFor (cutoffKernel β R) d z (k+1) [] ω) ∂law) =
      ∫⁻ b, f (cutoffBracketUpdate β z b)
        ∂poissonBatchLaw (ENNReal.ofReal (R ^ d)).toNNReal (cutoffBracketMarkLaw β d R z k) := by
  let : IsProbabilityMeasure law := isProbabilityMeasure_law
  let p := poissonMeasure (ENNReal.ofReal (R ^ d)).toNNReal
  let e := rootCutoffCountEvent d R
  have he (n : ℕ) : MeasurableSet (e n) := measurableSet_rootCutoffCountEvent d R n
  have hdj : Pairwise (fun i j : ℕ => Disjoint (e i) (e j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro ω hi hj
    change cutoffOffspring d R (ω []) = (i : ℝ≥0∞) at hi
    change cutoffOffspring d R (ω []) = (j : ℝ≥0∞) at hj
    have h : (i : ℝ≥0∞) = j := hi.symm.trans hj
    exact hij (by exact_mod_cast h)
  have hmass : law (⋃ n, e n) = 1 := by
    rw [measure_iUnion hdj he]
    calc
      _ = ∑' n, p {n} := tsum_congr fun n => measure_rootCutoffCountEvent hd hR.le n
      _ = _ := by
        have h := lintegral_countable' (μ := p) (fun _ : ℕ => 1)
        simpa only [lintegral_const, measure_univ, one_mul] using h.symm
  have hcover : ∀ᵐ ω ∂law, ω ∈ ⋃ n, e n := by
    apply ae_iff.mpr
    change law (⋃ n, e n)ᶜ = 0
    rw [measure_compl (MeasurableSet.iUnion he) (measure_ne_top _ _), measure_univ, hmass, tsub_self]
  calc
    _ = ∫⁻ ω in ⋃ n, e n, f (depthFor (cutoffKernel β R) d z (k+1) [] ω) ∂law := by
      rw [Measure.restrict_eq_self_of_ae_mem hcover]
    _ = ∑' n, ∫⁻ ω in e n, f (depthFor (cutoffKernel β R) d z (k+1) [] ω) ∂law :=
      lintegral_iUnion he hdj _
    _ = _ := by
      have hm : Measurable (fun b => f (cutoffBracketUpdate β z b)) :=
        hf.comp (measurable_cutoffBracketUpdate β z)
      rw [lintegral_poissonBatchLaw _ _ hm, lintegral_countable']
      exact tsum_congr fun n => (lintegral_cutoffDepth_succ_on_count hd hR k n f hf).trans (mul_comm _ _)

/-- The exact law of the next-depth cutoff bracket is the Poisson-batch
pushforward of the normalized retained lengths and iid child brackets. -/
theorem map_cutoffDepth_succ_eq_poissonBatch {β d R z : ℝ} (hd : 0 < d) (hR : 0 < R) (k : ℕ) :
    law.map (depthFor (cutoffKernel β R) d z (k+1) []) =
      (poissonBatchLaw (ENNReal.ofReal (R ^ d)).toNNReal (cutoffBracketMarkLaw β d R z k)).map
        (cutoffBracketUpdate β z) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (measurable_depthFor (measurable_cutoffKernel β R) d z (k+1) []),
    lintegral_map hf (measurable_cutoffBracketUpdate β z)]
  exact lintegral_cutoffDepth_succ_eq_poissonBatch hd hR k f hf

/-- The bracket laws obtained by iterating the Poisson-batch recursion. -/
noncomputable def cutoffBracketDistribution (β d R z : ℝ) : ℕ → Measure Bracket
  | 0 => Measure.dirac (0, z⁻¹)
  | k+1 =>
    let ν := (ENNReal.ofReal (R ^ d))⁻¹ • (intensity d).restrict (Set.Ioc 0 R)
    let μ := ν.prod (cutoffBracketDistribution β d R z k)
    (poissonBatchLaw (ENNReal.ofReal (R ^ d)).toNNReal μ).map (cutoffBracketUpdate β z)

/-- At every depth, the annealed bracket law can be computed by the recursion
starting from the deterministic terminal bracket. -/
theorem map_cutoffDepth_eq_distribution {β d R z : ℝ} (hd : 0 < d) (hR : 0 < R) (k : ℕ) :
    law.map (depthFor (cutoffKernel β R) d z k []) = cutoffBracketDistribution β d R z k := by
  let : IsProbabilityMeasure law := isProbabilityMeasure_law
  induction k with
  | zero =>
    change law.map (fun _ => (0, z⁻¹)) = Measure.dirac (0, z⁻¹)
    rw [Measure.map_const, measure_univ, one_smul]
  | succ k ih =>
    rw [map_cutoffDepth_succ_eq_poissonBatch hd hR k, cutoffBracketDistribution, ← ih]
    rfl

end Certificate.CanonicalTree

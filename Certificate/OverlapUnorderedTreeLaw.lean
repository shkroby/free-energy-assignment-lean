import Certificate.OverlapUnorderedTree
import Certificate.CanonicalShapePartition
import Certificate.IndependentCutoffBrackets

/-! The exact law of the unordered finite marked Poisson neighborhood. -/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Certificate.CanonicalTree

open UnorderedTree LocalExploration

private theorem measurable_cutoffOffspringNat (d R : ℝ) : Measurable (cutoffOffspringNat d R) :=
  measurable_to_countable' (measurableSet_cutoffOffspringNat_eq d R)

private theorem cutoffOffspringNat_eq_of_count {d R : ℝ} {E : Spacings} {n : ℕ}
    (hn : cutoffOffspring d R E = (n : ℝ≥0∞)) : cutoffOffspringNat d R E = n := by
  have h : ∃ k : ℕ, cutoffOffspring d R E = (k : ℝ≥0∞) := ⟨n,hn⟩
  rw [cutoffOffspringNat, dif_pos h]
  have he : (h.choose : ℝ≥0∞) = (n : ℝ≥0∞) := h.choose_spec.symm.trans hn
  exact_mod_cast he

private theorem map_cutoffOffspringNat {d R : ℝ} (hd : 0 < d) (hR : 0 ≤ R) :
    exponentialSpacings.map (cutoffOffspringNat d R) =
      poissonMeasure (ENNReal.ofReal (R ^ d)).toNNReal := by
  apply Measure.ext_of_singleton
  intro n
  rw [Measure.map_apply (measurable_cutoffOffspringNat d R) (measurableSet_singleton n),
    ← measure_cutoffOffspring_eq hd hR n]
  apply measure_congr
  filter_upwards [ae_cutoffOffspring_eq_nat hd hR] with E hE
  obtain ⟨m,hm⟩ := hE
  apply propext
  change cutoffOffspringNat d R E = n ↔ cutoffOffspring d R E = (n : ℝ≥0∞)
  rw [cutoffOffspringNat_eq_of_count hm, hm]
  exact ⟨fun h => by exact_mod_cast h, fun h => by exact_mod_cast h⟩

private noncomputable def windowNode (d R : ℝ) (k : ℕ) (p : Spacings × (ℕ → Depth k)) :
    Depth (k+1) :=
  let n := cutoffOffspringNat d R p.1
  node n (firstMarkedArrivals d n p)

private theorem measurable_markedArrivals {Y : Type*} [MeasurableSpace Y] (d : ℝ) (i : ℕ) :
    Measurable (markedArrivalPoint (Y := Y) d i) := by
  unfold markedArrivalPoint arrivalLength
  fun_prop

private theorem measurable_windowNode (d R : ℝ) (k : ℕ) : Measurable (windowNode d R k) :=
  (measurable_ofBatch k).comp (measurable_batchOfCount
    ((measurable_cutoffOffspringNat d R).comp measurable_fst)
    (measurable_markedArrivals d))

private theorem windowEvent_iff_cutoffOffspring {Y : Type*} (d R : ℝ) (n : ℕ)
    (p : Spacings × (ℕ → Y)) :
    p ∈ arrivalWindowCountEvent d R n ↔ cutoffOffspring d R p.1 = (n : ℝ≥0∞) := by
  change markedArrivalCount d (arrivalWindow R) p = (n : ℝ≥0∞) ↔ _
  have h : markedArrivalCount d (arrivalWindow R) p = cutoffOffspring d R p.1 := by
    unfold markedArrivalCount cutoffOffspring
    apply tsum_congr
    intro j
    let x := arrivalLength d p.1 j
    change (Ioc 0 R ×ˢ (Set.univ : Set Y)).indicator (fun _ => (1 : ℝ≥0∞)) (x, p.2 j) =
      (Ioc 0 R ×ˢ (Set.univ : Set Unit)).indicator (fun _ => (1 : ℝ≥0∞)) (x, ())
    by_cases h : x ∈ Ioc 0 R <;> simp [h]
  rw [h]

private theorem map_windowNode {d R : ℝ} (hd : 0 < d) (hR : 0 < R)
    (k : ℕ) (μ : Measure (Depth k)) [IsProbabilityMeasure μ] :
    (markedArrivalSequenceLaw μ).map (windowNode d R k) =
      (poissonBatchLaw (ENNReal.ofReal (R ^ d)).toNNReal ((truncatedIntensity d R).prod μ)).map
        (ofBatch k) := by
  let P := markedArrivalSequenceLaw μ
  let e (n : ℕ) := arrivalWindowCountEvent (Y := Depth k) d R n
  have hA : MeasurableSet (arrivalWindow R : Set (ℝ × Depth k)) :=
    measurableSet_Ioc.prod MeasurableSet.univ
  have he (n : ℕ) : MeasurableSet (e n) :=
    measurableSet_eq_fun (measurable_markedArrivalCount d hA) measurable_const
  have hdisj : Pairwise (fun i j : ℕ => Disjoint (e i) (e j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro p hi hj
    have h := ((windowEvent_iff_cutoffOffspring d R i p).mp hi).symm.trans
      ((windowEvent_iff_cutoffOffspring d R j p).mp hj)
    exact hij (by exact_mod_cast h)
  have hcover : ∀ᵐ p ∂P, p ∈ ⋃ n, e n := by
    let : IsProbabilityMeasure exponentialSpacings := isProbabilityMeasure_exponentialSpacings
    have hpres : MeasurePreserving Prod.fst P exponentialSpacings :=
      measurePreserving_fst (μ := exponentialSpacings)
        (ν := Measure.infinitePi (fun _ : ℕ => μ))
    filter_upwards [hpres.quasiMeasurePreserving.tendsto_ae.eventually
      (ae_cutoffOffspring_eq_nat hd hR.le)] with p hp
    obtain ⟨n,hn⟩ := hp
    exact mem_iUnion.mpr ⟨n,(windowEvent_iff_cutoffOffspring d R n p).mpr hn⟩
  have hmass : ((intensity d).prod μ) (arrivalWindow R) = ENNReal.ofReal (R ^ d) := by
    unfold arrivalWindow
    rw [Measure.prod_prod, intensity_Ioc_zero hd hR.le, measure_univ, mul_one]
  have hfin : ((intensity d).prod μ) (arrivalWindow R) ≠ ∞ := hmass ▸ ENNReal.ofReal_ne_top
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (measurable_windowNode d R k), lintegral_map hf (measurable_ofBatch k),
    lintegral_poissonBatchLaw _ _ (f := fun b => f (ofBatch k b)) (hf.comp (measurable_ofBatch k)),
    lintegral_countable' (μ := poissonMeasure (ENNReal.ofReal (R ^ d)).toNNReal)]
  change (∫⁻ p, f (windowNode d R k p) ∂P) = _
  rw [← Measure.restrict_eq_self_of_ae_mem hcover, lintegral_iUnion he hdisj]
  apply tsum_congr
  intro n
  let F (xs : Fin n → ℝ × Depth k) := f (node n xs)
  have hF : Measurable F := hf.comp (measurable_node k n)
  have hcanonical := lintegral_canonical_window_marks hd hR μ n F hF
    (fun xs σ => congrArg f (node_perm xs σ))
  have hc := canonical_iid_marked_count_probability hd μ hA hfin n
  change P (e n) = _ at hc
  rw [hmass] at hc
  calc
    _ = ∫⁻ p in e n, F (firstMarkedArrivals d n p) ∂P := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem (he n)] with p h
      have hs := cutoffOffspringNat_eq_of_count ((windowEvent_iff_cutoffOffspring d R n p).mp h)
      exact congrArg (fun m => f (node m (firstMarkedArrivals d m p))) hs
    _ = _ := by
      rw [hcanonical, hc, conditionalWindowMarkLaw_eq_prod hd hR μ, mul_comm]
      rfl

/-- The actual cutoff neighborhood read from chronologically sorted arrivals. -/
noncomputable def canonicalUnorderedTree (d R : ℝ) (k : ℕ) (ω : Environment) (v : Vertex) : Depth k :=
  ofChildren (fun a => cutoffOffspringNat d R (ω a)) (fun a i => arrivalLength d (ω a) i) k v

theorem measurable_canonicalUnorderedTree (d R : ℝ) (k : ℕ) (v : Vertex) :
    Measurable (fun ω => canonicalUnorderedTree d R k ω v) := by
  apply measurable_ofChildren
  · exact fun v => (measurable_cutoffOffspringNat d R).comp (measurable_pi_apply v)
  · intro v i
    unfold arrivalLength
    fun_prop

private theorem canonicalUnorderedTree_branch (d R : ℝ) (k : ℕ) (ω : Environment) (i : ℕ) (v : Vertex) :
    canonicalUnorderedTree d R k (branch i ω) v = canonicalUnorderedTree d R k ω (i::v) := by
  simpa only [canonicalUnorderedTree, branch] using
    ofChildren_shift (fun a => cutoffOffspringNat d R (ω a)) (fun a j => arrivalLength d (ω a) j) i k v

theorem map_canonicalUnorderedTree_succ {d R : ℝ} (hd : 0 < d) (hR : 0 < R) (k : ℕ) :
    law.map (fun ω => canonicalUnorderedTree d R (k+1) ω []) =
      (poissonBatchLaw (ENNReal.ofReal (R ^ d)).toNNReal ((truncatedIntensity d R).prod
        (law.map (fun ω => canonicalUnorderedTree d R k ω [])))).map (ofBatch k) := by
  let g (ω : Environment) := canonicalUnorderedTree d R k ω []
  let D (ω : Environment) := (ω [], fun i => g (branch i ω))
  have hg : Measurable g := measurable_canonicalUnorderedTree d R k []
  let : IsProbabilityMeasure law := isProbabilityMeasure_law
  let : IsProbabilityMeasure (law.map g) := Measure.isProbabilityMeasure_map hg.aemeasurable
  have hD : Measurable D := (measurable_pi_apply []).prodMk
    (measurable_pi_iff.mpr fun i => hg.comp (measurable_branch i))
  have hel : (fun ω => canonicalUnorderedTree d R (k+1) ω []) = windowNode d R k ∘ D := by
    funext ω
    simp only [canonicalUnorderedTree, ofChildren, windowNode, D, Function.comp_apply]
    congr 1
    funext i
    exact congrArg (fun x => (arrivalLength d (ω []) i, x))
      (canonicalUnorderedTree_branch d R k ω i []).symm
  rw [hel, ← Measure.map_map (measurable_windowNode d R k) hD, show law.map D = _ from map_root_marks hg]
  exact map_windowNode hd hR k (law.map g)

/-- The independent mark tree uses the same Poisson counts and unsorted iid
retained lengths. -/
noncomputable def independentUnorderedTree (d R : ℝ) (k : ℕ)
    (ω : IndependentMarkEnvironment) (v : Vertex) : Depth k :=
  ofChildren (fun a => cutoffOffspringNat d R (ω a).1) (fun a i => (ω a).2 i) k v

theorem measurable_independentUnorderedTree (d R : ℝ) (k : ℕ) (v : Vertex) :
    Measurable (fun ω => independentUnorderedTree d R k ω v) := by
  apply measurable_ofChildren
  · exact fun v => (measurable_cutoffOffspringNat d R).comp (measurable_pi_apply v).fst
  · exact fun v i => (measurable_pi_apply i).comp (measurable_pi_apply v).snd

private def cutBranch (i : ℕ) (ω : IndependentMarkEnvironment) : IndependentMarkEnvironment :=
  fun v => ω (i::v)

private theorem measurable_cutBranch (i : ℕ) : Measurable (cutBranch i) :=
  measurable_pi_iff.mpr fun v => measurable_pi_apply (i::v)

private theorem independentUnorderedTree_branch (d R : ℝ) (k : ℕ) (ω : IndependentMarkEnvironment)
    (i : ℕ) (v : Vertex) :
    independentUnorderedTree d R k (cutBranch i ω) v = independentUnorderedTree d R k ω (i::v) := by
  simpa only [independentUnorderedTree, cutBranch] using
    ofChildren_shift (fun a => cutoffOffspringNat d R (ω a).1) (fun a j => (ω a).2 j) i k v

private theorem map_independent_root_markedBranches {Y : Type*} [MeasurableSpace Y] {d R : ℝ}
    (hd : 0 < d) (hR : 0 < R) {g : IndependentMarkEnvironment → Y} (hg : Measurable g) :
    (independentMarkTreeLaw d R).map (fun ω => ((ω []).1, fun i => ((ω []).2 i, g (cutBranch i ω)))) =
      exponentialSpacings.prod (Measure.infinitePi (fun _ : ℕ => (truncatedIntensity d R).prod
        ((independentMarkTreeLaw d R).map g))) := by
  let ν := truncatedIntensity d R
  let Q := independentLengthSequence d R
  let P := exponentialSpacings.prod Q
  let U := independentMarkTreeLaw d R
  let M := Measure.infinitePi (fun _ : ℕ => U.map g)
  let : IsProbabilityMeasure exponentialSpacings := isProbabilityMeasure_exponentialSpacings
  let : IsProbabilityMeasure ν := isProbabilityMeasure_truncatedIntensity hd hR
  let : IsProbabilityMeasure Q := isProbabilityMeasure_independentLengthSequence hd hR
  let : IsProbabilityMeasure U := isProbabilityMeasure_independentMarkTreeLaw hd hR
  let : IsProbabilityMeasure P := inferInstance
  let : IsProbabilityMeasure (U.map g) := Measure.isProbabilityMeasure_map hg.aemeasurable
  let A (ω : IndependentMarkEnvironment) := (ω [], fun i => cutBranch i ω)
  let F (x : ℕ → IndependentMarkEnvironment) := fun i => g (x i)
  have hA : Measurable A := (measurable_pi_apply []).prodMk (measurable_pi_iff.mpr measurable_cutBranch)
  have hF : Measurable F := measurable_pi_iff.mpr fun i => hg.comp (measurable_pi_apply i)
  have hAmap : U.map A = P.prod (Measure.infinitePi (fun _ : ℕ => U)) := map_annotated_root_branches P
  have hFmap : (Measure.infinitePi (fun _ : ℕ => U)).map F = M :=
    Measure.infinitePi_map_pi _ (fun _ => hg)
  let B := Prod.map (id : Spacings × Spacings → Spacings × Spacings) F
  have hB : Measurable B := measurable_id.prodMap hF
  have hBmap : U.map (B ∘ A) = P.prod M := by
    rw [← Measure.map_map hB hA, hAmap, ← Measure.map_prod_map _ _ measurable_id hF, Measure.map_id, hFmap]
  let C := MeasurableEquiv.prodAssoc (α := Spacings) (β := Spacings) (γ := ℕ → Y)
  have hC : (P.prod M).map C = exponentialSpacings.prod (Q.prod M) :=
    (measurePreserving_prodAssoc exponentialSpacings Q M).map_eq
  let Z (p : Spacings × (ℕ → Y)) (i : ℕ) := (p.1 i,p.2 i)
  have hZ : Measurable Z := measurable_pi_iff.mpr fun i =>
    ((measurable_pi_apply i).comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp measurable_snd)
  have hZmap : (Q.prod M).map Z = Measure.infinitePi (fun _ : ℕ => ν.prod (U.map g)) :=
    map_zip_infinitePi _ _
  change U.map (Prod.map id Z ∘ C ∘ (B ∘ A)) = _
  rw [← Measure.map_map (measurable_id.prodMap hZ) (C.measurable.comp (hB.comp hA)),
    ← Measure.map_map C.measurable (hB.comp hA), hBmap, hC,
    ← Measure.map_prod_map _ _ measurable_id hZ, Measure.map_id, hZmap]

private noncomputable def prefixNode (d R : ℝ) (k : ℕ) (p : Spacings × (ℕ → ℝ × Depth k)) :
    Depth (k+1) := node (cutoffOffspringNat d R p.1) (fun i => p.2 i)

private theorem measurable_prefixNode (d R : ℝ) (k : ℕ) : Measurable (prefixNode d R k) :=
  (measurable_ofBatch k).comp (measurable_batchOfCount
    ((measurable_cutoffOffspringNat d R).comp measurable_fst)
    (fun i => (measurable_pi_apply i).comp measurable_snd))

private theorem map_prefixNode {d R : ℝ} (hd : 0 < d) (hR : 0 < R)
    (k : ℕ) (μ : Measure (ℝ × Depth k)) [IsProbabilityMeasure μ] :
    (exponentialSpacings.prod (Measure.infinitePi (fun _ : ℕ => μ))).map (prefixNode d R k) =
      (poissonBatchLaw (ENNReal.ofReal (R ^ d)).toNNReal μ).map (ofBatch k) := by
  let Q := Measure.infinitePi (fun _ : ℕ => μ)
  let : IsProbabilityMeasure exponentialSpacings := isProbabilityMeasure_exponentialSpacings
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (measurable_prefixNode d R k), lintegral_map hf (measurable_ofBatch k),
    lintegral_poissonBatchLaw _ _ (f := fun b => f (ofBatch k b)) (hf.comp (measurable_ofBatch k)),
    lintegral_prod (fun p => f (prefixNode d R k p))
      (hf.comp (measurable_prefixNode d R k)).aemeasurable]
  let J (n : ℕ) := ∫⁻ x, f (node n x) ∂Measure.pi (fun _ : Fin n => μ)
  have hj (E : Spacings) :
      (∫⁻ y : ℕ → ℝ × Depth k, f (prefixNode d R k (E,y)) ∂Q) = J (cutoffOffspringNat d R E) := by
    let n := cutoffOffspringNat d R E
    let p (y : ℕ → ℝ × Depth k) : Fin n → ℝ × Depth k := fun i => y i
    have hp : Measurable p := measurable_pi_iff.mpr fun i => measurable_pi_apply (i : ℕ)
    have hpm : Q.map p = Measure.pi (fun _ : Fin n => μ) := by
      rw [← Measure.infinitePi_eq_pi]
      exact Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ => μ)
        (f := fun i : Fin n => (i : ℕ)) Fin.val_injective
    change _ = ∫⁻ x, f (node n x) ∂Measure.pi (fun _ : Fin n => μ)
    rw [← hpm, lintegral_map (f := fun x => f (node n x)) (hf.comp (measurable_node k n)) hp]
    rfl
  change (∫⁻ E, ∫⁻ y, f (prefixNode d R k (E,y)) ∂Q ∂exponentialSpacings) =
    ∫⁻ n, J n ∂poissonMeasure (ENNReal.ofReal (R ^ d)).toNNReal
  rw [lintegral_congr hj, ← map_cutoffOffspringNat hd hR.le,
    lintegral_map (measurable_of_countable J) (measurable_cutoffOffspringNat d R)]

theorem map_independentUnorderedTree_succ {d R : ℝ} (hd : 0 < d) (hR : 0 < R) (k : ℕ) :
    (independentMarkTreeLaw d R).map (fun ω => independentUnorderedTree d R (k+1) ω []) =
      (poissonBatchLaw (ENNReal.ofReal (R ^ d)).toNNReal ((truncatedIntensity d R).prod
        ((independentMarkTreeLaw d R).map (fun ω => independentUnorderedTree d R k ω [])))).map
        (ofBatch k) := by
  let U := independentMarkTreeLaw d R
  let g (ω : IndependentMarkEnvironment) := independentUnorderedTree d R k ω []
  let D (ω : IndependentMarkEnvironment) := ((ω []).1, fun i => ((ω []).2 i, g (cutBranch i ω)))
  have hg : Measurable g := measurable_independentUnorderedTree d R k []
  let : IsProbabilityMeasure U := isProbabilityMeasure_independentMarkTreeLaw hd hR
  let : IsProbabilityMeasure (U.map g) := Measure.isProbabilityMeasure_map hg.aemeasurable
  let : IsProbabilityMeasure (truncatedIntensity d R) := isProbabilityMeasure_truncatedIntensity hd hR
  have hroot : Measurable (fun ω : IndependentMarkEnvironment => ω []) := measurable_pi_apply []
  have hD : Measurable D := hroot.fst.prodMk
    (measurable_pi_iff.mpr fun i => ((measurable_pi_apply i).comp hroot.snd).prodMk
      (hg.comp (measurable_cutBranch i)))
  have hel : (fun ω => independentUnorderedTree d R (k+1) ω []) = prefixNode d R k ∘ D := by
    funext ω
    simp only [independentUnorderedTree, ofChildren, prefixNode, D, Function.comp_apply]
    congr 1
    funext i
    exact congrArg (fun x => ((ω []).2 i, x)) (independentUnorderedTree_branch d R k ω i []).symm
  rw [hel, ← Measure.map_map (measurable_prefixNode d R k) hD,
    show U.map D = _ from map_independent_root_markedBranches hd hR hg]
  exact map_prefixNode hd hR k ((truncatedIntensity d R).prod (U.map g))

/-- The chronological and iid constructions agree in law at every depth
after the ordering of siblings has been forgotten. -/
theorem map_independentUnorderedTree_eq {d R : ℝ} (hd : 0 < d) (hR : 0 < R) (k : ℕ) :
    (independentMarkTreeLaw d R).map (fun ω => independentUnorderedTree d R k ω []) =
      law.map (fun ω => canonicalUnorderedTree d R k ω []) := by
  let : IsProbabilityMeasure (independentMarkTreeLaw d R) := isProbabilityMeasure_independentMarkTreeLaw hd hR
  let : IsProbabilityMeasure law := isProbabilityMeasure_law
  induction k with
  | zero =>
    change (independentMarkTreeLaw d R).map (fun _ => PUnit.unit) =
      law.map (fun _ => PUnit.unit)
    rw [Measure.map_const, Measure.map_const, measure_univ, measure_univ, one_smul]
  | succ k ih =>
    rw [map_independentUnorderedTree_succ hd hR, map_canonicalUnorderedTree_succ hd hR, ih]

end Certificate.CanonicalTree

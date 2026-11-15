import Certificate.CanonicalCutoffBracketLaw
import Certificate.CanonicalPlaneShapeLaw
import Certificate.LocalExplorationMarks
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration

/-! Independent outgoing marks give the same bracket law as the ordered arrivals. -/

open Finset Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Certificate

/-- Zipping two independent product arrays gives the product of the coordinate
pair laws. -/
theorem map_zip_infinitePi {I A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) [IsProbabilityMeasure μ] (ν : Measure B) [IsProbabilityMeasure ν] :
    ((Measure.infinitePi fun _ : I => μ).prod (Measure.infinitePi fun _ : I => ν)).map
      (fun ab i => (ab.1 i, ab.2 i)) = Measure.infinitePi (fun _ : I => μ.prod ν) := by
  classical
  let P := Measure.infinitePi fun _ : I => μ
  let Q := Measure.infinitePi fun _ : I => ν
  let f (ab : (I → A) × (I → B)) (i : I) := (ab.1 i, ab.2 i)
  have hf : Measurable f := measurable_pi_iff.mpr fun i =>
    ((measurable_pi_apply i).comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp measurable_snd)
  apply Measure.eq_infinitePi
  intro S t ht
  have hs : MeasurableSet (Set.pi (↑S : Set I) t) := MeasurableSet.pi S.countable_toSet (fun i _ => ht i)
  rw [Measure.map_apply hf hs, Measure.prod_apply (hf hs)]
  let g (i : I) (a : A) := ν ((fun b : B => (a,b)) ⁻¹' t i)
  have hg (i : I) : Measurable (g i) := measurable_measure_prodMk_left (ht i)
  have hx (a : I → A) :
      (fun b : I → B => (a,b)) ⁻¹' (f ⁻¹' Set.pi (↑S : Set I) t) =
        Set.pi (↑S : Set I) (fun i => (fun b : B => (a i,b)) ⁻¹' t i) := rfl
  have hy (a : I → A) :
      Q ((fun b : I → B => (a,b)) ⁻¹' (f ⁻¹' Set.pi (↑S : Set I) t)) = ∏ i ∈ S, g i (a i) := by
    rw [hx]
    exact Measure.infinitePi_pi _ (fun i _ => measurable_prodMk_left (ht i))
  change (∫⁻ a, Q ((fun b : I → B => (a,b)) ⁻¹' (f ⁻¹' Set.pi (↑S : Set I) t)) ∂P) = _
  rw [show (∫⁻ a, Q ((fun b : I → B => (a,b)) ⁻¹' (f ⁻¹' Set.pi (↑S : Set I) t)) ∂P) =
    ∫⁻ a, ∏ i ∈ S, g i (a i) ∂P from lintegral_congr hy]
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun _ _ (iIndepFun_infinitePi hg)
    (fun i => (hg i).comp (measurable_pi_apply i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hm := Measure.infinitePi_map_eval (fun _ : I => μ) i
  calc
    _ = ∫⁻ u, g i u ∂P.map (fun a : I → A => a i) :=
      (lintegral_map (hg i) (measurable_pi_apply i)).symm
    _ = ∫⁻ u, g i u ∂μ := by rw [hm]
    _ = _ := (Measure.prod_apply (ht i)).symm

namespace CanonicalTree

open LocalExploration

/-- A spacing array for offspring counts and a separate array of outgoing
lengths at each vertex. -/
abbrev IndependentMarkEnvironment := Vertex → Spacings × Spacings

noncomputable def independentLengthSequence (d R : ℝ) : Measure Spacings :=
  Measure.infinitePi (fun _ : ℕ => truncatedIntensity d R)

/-- The auxiliary tree has the original count law and independent iid lengths. -/
noncomputable def independentMarkTreeLaw (d R : ℝ) : Measure IndependentMarkEnvironment :=
  Measure.infinitePi fun _ : Vertex => exponentialSpacings.prod (independentLengthSequence d R)

theorem isProbabilityMeasure_independentLengthSequence {d R : ℝ} (hd : 0 < d) (hR : 0 < R) :
    IsProbabilityMeasure (independentLengthSequence d R) := by
  let : IsProbabilityMeasure (truncatedIntensity d R) := isProbabilityMeasure_truncatedIntensity hd hR
  unfold independentLengthSequence
  infer_instance

theorem isProbabilityMeasure_independentMarkTreeLaw {d R : ℝ} (hd : 0 < d) (hR : 0 < R) :
    IsProbabilityMeasure (independentMarkTreeLaw d R) := by
  let : IsProbabilityMeasure exponentialSpacings := isProbabilityMeasure_exponentialSpacings
  let : IsProbabilityMeasure (independentLengthSequence d R) := isProbabilityMeasure_independentLengthSequence hd hR
  unfold independentMarkTreeLaw
  infer_instance

def splitIndependentMarks (ω : IndependentMarkEnvironment) : Environment × Environment :=
  (fun v => (ω v).1, fun v => (ω v).2)

theorem measurable_splitIndependentMarks : Measurable splitIndependentMarks :=
  (measurable_pi_iff.mpr fun v => (measurable_pi_apply v).fst).prodMk
    (measurable_pi_iff.mpr fun v => (measurable_pi_apply v).snd)

theorem map_splitIndependentMarks {d R : ℝ} (hd : 0 < d) (hR : 0 < R) :
    (independentMarkTreeLaw d R).map splitIndependentMarks =
      law.prod (Measure.infinitePi (fun _ : Vertex => independentLengthSequence d R)) := by
  let : IsProbabilityMeasure exponentialSpacings := isProbabilityMeasure_exponentialSpacings
  let : IsProbabilityMeasure (independentLengthSequence d R) := isProbabilityMeasure_independentLengthSequence hd hR
  let Z (p : Environment × Environment) (v : Vertex) := (p.1 v,p.2 v)
  have hZ : Measurable Z := measurable_pi_iff.mpr fun v =>
    ((measurable_pi_apply v).comp measurable_fst).prodMk
      ((measurable_pi_apply v).comp measurable_snd)
  have hm : (law.prod (Measure.infinitePi (fun _ : Vertex => independentLengthSequence d R))).map Z =
      independentMarkTreeLaw d R := map_zip_infinitePi _ _
  rw [← hm, Measure.map_map measurable_splitIndependentMarks hZ]
  exact Measure.map_id

private def independentBranch (i : ℕ) (ω : IndependentMarkEnvironment) : IndependentMarkEnvironment :=
  fun v => ω (i :: v)

private theorem measurable_independentBranch (i : ℕ) : Measurable (independentBranch i) :=
  measurable_pi_iff.mpr fun v => measurable_pi_apply (i :: v)

/-- Edge lengths are sampled independently of the spacings used to choose
the offspring count. -/
noncomputable def independentCutoffWeight (β d R : ℝ) (ω : IndependentMarkEnvironment)
    (v : Vertex) (i : ℕ) : ℝ :=
  if (i : ℝ≥0∞) < cutoffOffspring d R (ω v).1 then Real.exp (-β * (ω v).2 i) else 0

private theorem measurable_independentCutoffWeight (β d R : ℝ) (v : Vertex) (i : ℕ) :
    Measurable (fun ω => independentCutoffWeight β d R ω v i) := by
  have hm : Measurable (fun ω : IndependentMarkEnvironment => (ω v).2 i) :=
    (measurable_pi_apply i).comp (measurable_pi_apply v).snd
  exact Measurable.ite (measurableSet_lt measurable_const
    ((measurable_cutoffOffspring d R).comp (measurable_pi_apply v).fst))
    (Real.measurable_exp.comp (hm.const_mul (-β))) measurable_const

noncomputable def independentCutoffDepth (β d R z : ℝ) (k : ℕ)
    (v : Vertex) (ω : IndependentMarkEnvironment) : Bracket :=
  TreeBoundary.bounds z child (independentCutoffWeight β d R ω) k v

theorem measurable_independentCutoffDepth (β d R z : ℝ) (k : ℕ) (v : Vertex) :
    Measurable (independentCutoffDepth β d R z k v) := by
  induction k generalizing v with
  | zero => exact measurable_const
  | succ k ih =>
    unfold independentCutoffDepth
    simp only [TreeBoundary.bounds]
    exact ((measurable_const.add (Measurable.tsum fun i =>
      (measurable_independentCutoffWeight β d R v i).mul (ih (child v i)).snd)).inv).prodMk
      ((measurable_const.add (Measurable.tsum fun i =>
        (measurable_independentCutoffWeight β d R v i).mul (ih (child v i)).fst)).inv)

private theorem independentCutoffDepth_branch (β d R z : ℝ) (k : ℕ)
    (v : Vertex) (ω : IndependentMarkEnvironment) (i : ℕ) :
    independentCutoffDepth β d R z k v (independentBranch i ω) =
      independentCutoffDepth β d R z k (i :: v) ω := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih =>
    simp only [independentCutoffDepth, TreeBoundary.bounds] at ih ⊢
    have hc (j : ℕ) : i :: child v j = child (i :: v) j := rfl
    have hw : independentCutoffWeight β d R (independentBranch i ω) v =
        independentCutoffWeight β d R ω (i :: v) := rfl
    simp only [ih, hc, hw]

private noncomputable def independentRootData (β d R z : ℝ) (k : ℕ) (ω : IndependentMarkEnvironment) :
    Spacings × (ℕ → ChildMark) :=
  ((ω []).1, fun i => ((ω []).2 i, independentCutoffDepth β d R z k [] (independentBranch i ω)))

private theorem measurable_independentRootData (β d R z : ℝ) (k : ℕ) :
    Measurable (independentRootData β d R z k) := by
  have hm : Measurable (fun ω : IndependentMarkEnvironment => ω []) := measurable_pi_apply []
  have h (i : ℕ) : Measurable (fun ω : IndependentMarkEnvironment => (ω []).2 i) :=
    (measurable_pi_apply i).comp hm.snd
  exact hm.fst.prodMk (measurable_pi_iff.mpr fun i =>
    (h i).prodMk ((measurable_independentCutoffDepth β d R z k []).comp
      (measurable_independentBranch i)))

private theorem map_independentRootData {β d R z : ℝ} (hd : 0 < d) (hR : 0 < R) (k : ℕ) :
    (independentMarkTreeLaw d R).map (independentRootData β d R z k) =
      exponentialSpacings.prod (Measure.infinitePi (fun _ : ℕ =>
        (truncatedIntensity d R).prod ((independentMarkTreeLaw d R).map
          (independentCutoffDepth β d R z k [])))) := by
  let ν := truncatedIntensity d R
  let Q := independentLengthSequence d R
  let P := exponentialSpacings.prod Q
  let U := independentMarkTreeLaw d R
  let g := independentCutoffDepth β d R z k []
  let M := Measure.infinitePi (fun _ : ℕ => U.map g)
  let : IsProbabilityMeasure exponentialSpacings := isProbabilityMeasure_exponentialSpacings
  let : IsProbabilityMeasure ν := isProbabilityMeasure_truncatedIntensity hd hR
  let : IsProbabilityMeasure Q := isProbabilityMeasure_independentLengthSequence hd hR
  let : IsProbabilityMeasure U := isProbabilityMeasure_independentMarkTreeLaw hd hR
  let : IsProbabilityMeasure P := inferInstance
  have hg : Measurable g := measurable_independentCutoffDepth β d R z k []
  let : IsProbabilityMeasure (U.map g) := Measure.isProbabilityMeasure_map hg.aemeasurable
  let A (ω : IndependentMarkEnvironment) := (ω [], fun i => independentBranch i ω)
  let F (x : ℕ → IndependentMarkEnvironment) := fun i => g (x i)
  have hA : Measurable A := (measurable_pi_apply []).prodMk (measurable_pi_iff.mpr measurable_independentBranch)
  have hF : Measurable F := measurable_pi_iff.mpr fun i => hg.comp (measurable_pi_apply i)
  have hAmap : U.map A = P.prod (Measure.infinitePi (fun _ : ℕ => U)) := map_annotated_root_branches P
  have hFmap : (Measure.infinitePi (fun _ : ℕ => U)).map F = M :=
    Measure.infinitePi_map_pi _ (fun _ => hg)
  let B := Prod.map (id : Spacings × Spacings → Spacings × Spacings) F
  have hB : Measurable B := measurable_id.prodMap hF
  have hBmap : U.map (B ∘ A) = P.prod M := by
    rw [← Measure.map_map hB hA, hAmap, ← Measure.map_prod_map _ _ measurable_id hF, Measure.map_id, hFmap]
  let C := MeasurableEquiv.prodAssoc (α := Spacings) (β := Spacings) (γ := ℕ → Bracket)
  have hC : (P.prod M).map C = exponentialSpacings.prod (Q.prod M) :=
    (measurePreserving_prodAssoc exponentialSpacings Q M).map_eq
  let Z (p : Spacings × (ℕ → Bracket)) (i : ℕ) := (p.1 i,p.2 i)
  have hZ : Measurable Z := measurable_pi_iff.mpr fun i =>
    ((measurable_pi_apply i).comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp measurable_snd)
  have hZmap : (Q.prod M).map Z = Measure.infinitePi (fun _ : ℕ => ν.prod (U.map g)) :=
    map_zip_infinitePi _ _
  change U.map (Prod.map id Z ∘ C ∘ (B ∘ A)) = _
  rw [← Measure.map_map (measurable_id.prodMap hZ) (C.measurable.comp (hB.comp hA)),
    ← Measure.map_map C.measurable (hB.comp hA), hBmap, hC,
    ← Measure.map_prod_map _ _ measurable_id hZ, Measure.map_id, hZmap]

private def prefixMarks {X : Type*} (n : ℕ) (m : ℕ → X) : Fin n → X := fun i => m i

private theorem measurable_prefixMarks {X : Type*} [MeasurableSpace X] (n : ℕ) :
    Measurable (prefixMarks (X := X) n) :=
  measurable_pi_iff.mpr fun i => measurable_pi_apply (i : ℕ)

private theorem map_prefixMarks {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (n : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => P)).map (prefixMarks n) =
      Measure.pi (fun _ : Fin n => P) := by
  rw [← Measure.infinitePi_eq_pi]
  exact Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ => P)
    (f := fun i : Fin n => (i : ℕ)) Fin.val_injective

private theorem independentCutoffDepth_succ_on_count {β d R z : ℝ} (k n : ℕ)
    (ω : IndependentMarkEnvironment) (hn : cutoffOffspring d R (ω []).1 = (n : ℝ≥0∞)) :
    independentCutoffDepth β d R z (k+1) [] ω =
      cutoffBracketUpdate β z ⟨n, prefixMarks n (independentRootData β d R z k ω).2⟩ := by
  have hsum (p : Bracket → ℝ) :
      (∑' i, independentCutoffWeight β d R ω [] i *
        p (independentCutoffDepth β d R z k (child [] i) ω)) =
      ∑ i : Fin n, Real.exp (-β * (ω []).2 i) *
        p (independentCutoffDepth β d R z k [] (independentBranch i ω)) := by
    let f (i : ℕ) := independentCutoffWeight β d R ω [] i *
      p (independentCutoffDepth β d R z k (child [] i) ω)
    have hs (i : ℕ) (hi : i ∉ Finset.range n) : f i = 0 := by
      simp only [f, independentCutoffWeight, hn, Nat.cast_lt,
        if_neg (fun h => hi (Finset.mem_range.mpr h)), zero_mul]
    have hts : (∑' i, f i) = ∑ i ∈ Finset.range n, f i := tsum_eq_sum hs
    change (∑' i, f i) = _
    rw [hts, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    have heq : child [] i = i.val :: [] := rfl
    simp only [f, independentCutoffWeight, hn, Nat.cast_lt, if_pos i.isLt, heq,
      independentCutoffDepth_branch]
  change ((z + ∑' i, independentCutoffWeight β d R ω [] i *
      (independentCutoffDepth β d R z k (child [] i) ω).2)⁻¹,
    (z + ∑' i, independentCutoffWeight β d R ω [] i *
      (independentCutoffDepth β d R z k (child [] i) ω).1)⁻¹) = _
  rw [hsum Prod.snd, hsum Prod.fst]
  rfl

private theorem lintegral_independentCutoffDepth_succ {β d R z : ℝ}
    (hd : 0 < d) (hR : 0 < R) (k : ℕ) (f : Bracket → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, f (independentCutoffDepth β d R z (k+1) [] ω) ∂independentMarkTreeLaw d R) =
      ∫⁻ b, f (cutoffBracketUpdate β z b)
        ∂poissonBatchLaw (ENNReal.ofReal (R ^ d)).toNNReal
          ((truncatedIntensity d R).prod
            ((independentMarkTreeLaw d R).map (independentCutoffDepth β d R z k []))) := by
  let U := independentMarkTreeLaw d R
  let M := (truncatedIntensity d R).prod (U.map (independentCutoffDepth β d R z k []))
  let Q := Measure.infinitePi (fun _ : ℕ => M)
  let D := independentRootData β d R z k
  have hD : Measurable D := measurable_independentRootData β d R z k
  have hmap : U.map D = exponentialSpacings.prod Q := map_independentRootData hd hR k
  let : IsProbabilityMeasure U := isProbabilityMeasure_independentMarkTreeLaw hd hR
  let : IsProbabilityMeasure exponentialSpacings := isProbabilityMeasure_exponentialSpacings
  let : IsProbabilityMeasure (truncatedIntensity d R) := isProbabilityMeasure_truncatedIntensity hd hR
  let : IsProbabilityMeasure (U.map (independentCutoffDepth β d R z k [])) :=
    Measure.isProbabilityMeasure_map (measurable_independentCutoffDepth β d R z k []).aemeasurable
  let : IsProbabilityMeasure M := inferInstance
  let p := poissonMeasure (ENNReal.ofReal (R ^ d)).toNNReal
  let a (n : ℕ) : Set Spacings := {E | cutoffOffspring d R E = (n : ℝ≥0∞)}
  let e (n : ℕ) : Set IndependentMarkEnvironment := D ⁻¹' (a n ×ˢ Set.univ)
  have ha (n : ℕ) : MeasurableSet (a n) :=
    measurableSet_eq_fun (measurable_cutoffOffspring d R) measurable_const
  have hProd (n : ℕ) : MeasurableSet (a n ×ˢ (Set.univ : Set (ℕ → ChildMark))) :=
    (ha n).prod MeasurableSet.univ
  have he (n : ℕ) : MeasurableSet (e n) := hD (hProd n)
  have hcover : ∀ᵐ ω ∂U, ω ∈ ⋃ n, e n := by
    have hp : MeasurePreserving (fun ω : IndependentMarkEnvironment => (D ω).1) U exponentialSpacings := by
      refine ⟨hD.fst, ?_⟩
      change U.map (Prod.fst ∘ D) = _
      rw [← Measure.map_map measurable_fst hD, hmap, Measure.map_fst_prod, measure_univ, one_smul]
    filter_upwards [hp.quasiMeasurePreserving.tendsto_ae.eventually (ae_cutoffOffspring_eq_nat hd hR.le)] with ω hω
    obtain ⟨n, hn⟩ := hω
    exact mem_iUnion.mpr ⟨n, ⟨hn, Set.mem_univ _⟩⟩
  have hdj : Pairwise (fun i j : ℕ => Disjoint (e i) (e j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro ω hi hj
    have h : (i : ℝ≥0∞) = j := hi.1.symm.trans hj.1
    exact hij (by exact_mod_cast h)
  have hterms (n : ℕ) :
      (∫⁻ ω in e n, f (independentCutoffDepth β d R z (k+1) [] ω) ∂U) =
      p {n} * ∫⁻ x, f (cutoffBracketUpdate β z ⟨n,x⟩) ∂Measure.pi (fun _ : Fin n => M) := by
    let F (x : Fin n → ChildMark) := f (cutoffBracketUpdate β z ⟨n,x⟩)
    have hF : Measurable F := hf.comp ((measurable_cutoffBracketUpdate β z).comp (measurable_poissonBatch_mk n))
    let G (b : Spacings × (ℕ → ChildMark)) := F (prefixMarks n b.2)
    have hG : Measurable G := hF.comp ((measurable_prefixMarks n).comp measurable_snd)
    calc
      _ = ∫⁻ ω in e n, G (D ω) ∂U := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem (he n)] with ω hω
        exact congrArg f (independentCutoffDepth_succ_on_count k n ω hω.1)
      _ = ∫⁻ b in a n ×ˢ Set.univ, G b ∂exponentialSpacings.prod Q := by
        rw [← hmap, Measure.restrict_map hD (hProd n), lintegral_map hG hD]
      _ = (exponentialSpacings (a n)) * ∫⁻ m, F (prefixMarks n m) ∂Q := by
        rw [← Measure.prod_restrict, Measure.restrict_univ, lintegral_prod G hG.aemeasurable]
        change (∫⁻ _ in a n, (∫⁻ m, F (prefixMarks n m) ∂Q) ∂exponentialSpacings) = _
        rw [lintegral_const, Measure.restrict_apply_univ, mul_comm]
      _ = _ := by
        have hm : exponentialSpacings (a n) = p {n} := measure_cutoffOffspring_eq hd hR.le n
        change _ = p {n} * ∫⁻ x, F x ∂Measure.pi (fun _ : Fin n => M)
        rw [hm, ← map_prefixMarks M n, lintegral_map hF (measurable_prefixMarks n)]
  calc
    _ = ∫⁻ ω in ⋃ n, e n, f (independentCutoffDepth β d R z (k+1) [] ω) ∂U := by
      rw [Measure.restrict_eq_self_of_ae_mem hcover]
    _ = ∑' n, ∫⁻ ω in e n, f (independentCutoffDepth β d R z (k+1) [] ω) ∂U :=
      lintegral_iUnion he hdj _
    _ = _ := by
      have hTest : Measurable (fun b => f (cutoffBracketUpdate β z b)) :=
        hf.comp (measurable_cutoffBracketUpdate β z)
      rw [lintegral_poissonBatchLaw _ _ hTest, lintegral_countable']
      exact tsum_congr fun n => (hterms n).trans (mul_comm _ _)

/-- The iid-mark auxiliary tree and the actual canonical cutoff tree have the
same bracket law at every depth. -/
theorem map_independentCutoffDepth_eq {β d R z : ℝ} (hd : 0 < d) (hR : 0 < R) (k : ℕ) :
    (independentMarkTreeLaw d R).map (independentCutoffDepth β d R z k []) =
      law.map (depthFor (cutoffKernel β R) d z k []) := by
  let : IsProbabilityMeasure (independentMarkTreeLaw d R) := isProbabilityMeasure_independentMarkTreeLaw hd hR
  let : IsProbabilityMeasure law := isProbabilityMeasure_law
  induction k with
  | zero =>
    change (independentMarkTreeLaw d R).map (fun _ => (0,z⁻¹)) = law.map (fun _ => (0,z⁻¹))
    rw [Measure.map_const, Measure.map_const, measure_univ, measure_univ]
  | succ k ih =>
    apply Measure.ext_of_lintegral
    intro f hf
    rw [lintegral_map hf (measurable_independentCutoffDepth β d R z (k+1) []),
      lintegral_map hf (measurable_depthFor (measurable_cutoffKernel β R) d z (k+1) []),
      lintegral_independentCutoffDepth_succ hd hR k f hf,
      lintegral_cutoffDepth_succ_eq_poissonBatch hd hR k f hf, ih]
    rfl

/-- The auxiliary bracket expectation can be evaluated by integrating its
length arrays independently of its count arrays. -/
theorem lintegral_independentCutoffDepth_eq_split {β d R z : ℝ} (hd : 0 < d) (hR : 0 < R)
    (k : ℕ) (f : Bracket → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, f (independentCutoffDepth β d R z k [] ω) ∂independentMarkTreeLaw d R) =
      ∫⁻ E, ∫⁻ T : Environment,
        f (independentCutoffDepth β d R z k [] (fun v => (E v,T v)))
        ∂Measure.infinitePi (fun _ : Vertex => Measure.infinitePi (fun _ : ℕ => truncatedIntensity d R))
        ∂law := by
  let : IsProbabilityMeasure exponentialSpacings := isProbabilityMeasure_exponentialSpacings
  let : IsProbabilityMeasure (truncatedIntensity d R) := isProbabilityMeasure_truncatedIntensity hd hR
  let Q := Measure.infinitePi (fun _ : ℕ => truncatedIntensity d R)
  let P := Measure.infinitePi (fun _ : Vertex => Q)
  let Z (p : Environment × Environment) (v : Vertex) := (p.1 v,p.2 v)
  have hZ : Measurable Z := measurable_pi_iff.mpr fun v =>
    ((measurable_pi_apply v).comp measurable_fst).prodMk
      ((measurable_pi_apply v).comp measurable_snd)
  have hmap : (law.prod P).map Z = independentMarkTreeLaw d R := map_zip_infinitePi _ _
  have h : Measurable (fun ω : IndependentMarkEnvironment =>
      f (independentCutoffDepth β d R z k [] ω)) :=
    hf.comp (measurable_independentCutoffDepth β d R z k [])
  rw [← hmap, lintegral_map h hZ]
  exact lintegral_prod _ (h.comp hZ).aemeasurable

end CanonicalTree
end Certificate

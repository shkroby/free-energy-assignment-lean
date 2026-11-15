import Certificate.OverlapCanonicalSquareLimit
import Certificate.OverlapSoftOccupations
import Certificate.OverlapThreeOccupations
import Certificate.OverlapRowTests
import Certificate.CanonicalBetheVertex

/-! Occupation tests on the common tree and their cutoff limits. -/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace Certificate.CanonicalTree

open Overlap

/-- The root spacings and the soft messages from its independent branches. -/
noncomputable def rootSoftMarks (β d z : ℝ) (ω : Environment) : ArrivalConfiguration :=
  (ω [], fun i => lower β d z [] (branch i ω))

theorem measurable_rootSoftMarks (β d z : ℝ) : Measurable (rootSoftMarks β d z) :=
  (measurable_pi_apply []).prodMk
    (measurable_pi_iff.mpr fun i => (measurable_lower β d z []).comp (measurable_branch i))

theorem map_rootSoftMarks (β d z : ℝ) :
    law.map (rootSoftMarks β d z) = markedSpacings (softCavityProbability β d z : Measure ℝ) :=
  map_root_marks (measurable_lower β d z [])

theorem ae_fullRootOccupation_eq {β d z : ℝ} (hβ : 0 < β) (hd : 0 < d) (hz : 0 < z) :
    ∀ᵐ ω ∂law, ∀ i, fullRootOccupation β d z ω i = rootOccupation β d z (rootSoftMarks β d z ω) i := by
  filter_upwards [ae_lower_logFugacity_recursion hβ hd, ae_summable_weight hβ hd] with ω hrec hw
  have hb (v : Vertex) := hrec (Real.log z) v
  simp only [Real.exp_log hz] at hb
  have hc (i : ℕ) : cavityTerm β d (rootSoftMarks β d z ω) i =
      weight β d ω [] i * lower β d z (child [] i) ω := by
    simp [cavityTerm, rootSoftMarks, weight, child, lower_branch]
  have hp (i : ℕ) : 0 ≤ cavityTerm β d (rootSoftMarks β d z ω) i := by
    rw [hc]
    exact mul_nonneg (weight_nonneg β d ω [] i) (hb _).1.le
  have hs : Summable (cavityTerm β d (rootSoftMarks β d z ω)) :=
    ((hw []).mul_right z⁻¹).of_nonneg_of_le hp (fun i => by
      rw [hc]
      exact mul_le_mul_of_nonneg_left (hb _).2.1 (weight_nonneg β d ω [] i))
  have hroot : arrivalSoftOutput β d z (rootSoftMarks β d z ω) = lower β d z [] ω := by
    unfold arrivalSoftOutput arrivalWeightedSum
    rw [← ENNReal.ofReal_tsum_of_nonneg hp hs, ENNReal.toReal_ofReal (tsum_nonneg hp),
      (hb []).2.2, TreeBoundary.update]
    simp only [hc]
  intro i
  rw [rootOccupation, hc, hroot, fullRootOccupation]
  ring

theorem measurable_fullRootOccupation (β d z : ℝ) (i : ℕ) :
    Measurable (fun ω => fullRootOccupation β d z ω i) :=
  ((measurable_weight β d [] i).mul (measurable_lower β d z [])).mul
    (measurable_lower β d z (child [] i))

/-- The clipped square test agrees in expectation with the soft overlap. -/
theorem integral_fullRootSquare_eq_cavityOverlap {β d z : ℝ}
    (hβ : 0 < β) (hd : 0 < d) (hz : 0 < z) :
    (∫ ω, min 1 (∑' i, (fullRootOccupation β d z ω i)^2) ∂law) =
      cavityOverlap β d (softCavityProbability β d z : Measure ℝ) := by
  let P := markedSpacings (softCavityProbability β d z : Measure ℝ)
  let I (ω : ArrivalConfiguration) := min 1 (∑' i, (rootOccupation β d z ω i)^2)
  have hI : Measurable I := measurable_const.min (Measurable.tsum fun i =>
    (measurable_rootOccupation β d z i).pow_const 2)
  calc
    _ = ∫ ω, I (rootSoftMarks β d z ω) ∂law := by
      apply integral_congr_ae
      filter_upwards [ae_fullRootOccupation_eq hβ hd hz] with ω hω
      simp only [I, hω]
    _ = ∫ ω, I ω ∂P := by
      have hmap : law.map (rootSoftMarks β d z) = P := map_rootSoftMarks β d z
      rw [← hmap, integral_map (measurable_rootSoftMarks β d z).aemeasurable
        hI.aestronglyMeasurable]
    _ = _ := by
      rw [cavityOverlap_soft_eq_integral_rootOccupation_sq hβ hd hz]
      apply integral_congr_ae
      filter_upwards [ae_soft_rootOccupation_spec hβ hd hz] with ω h
      apply min_eq_right
      have hle (i : ℕ) : (rootOccupation β d z ω i)^2 ≤ rootOccupation β d z ω i := by
        have hi := (h.2.1.le_tsum i (fun j _ => (h.1 j).le)).trans h.2.2
        nlinarith [mul_nonneg (h.1 i).le (sub_nonneg.mpr hi)]
      exact ((h.2.1.of_nonneg_of_le (fun _ => sq_nonneg _) hle).tsum_le_tsum hle
        h.2.1).trans h.2.2

/-- Test a fixed triple of incident edges for a small occupation. -/
noncomputable def firstThreeScore (η : ℝ) (p : ℕ → ℝ) : ℝ :=
  smallOccupationTest η (min (p 0) (min (p 1) (p 2)))

theorem firstThreeScore_mem_Icc (η : ℝ) (p : ℕ → ℝ) :
    firstThreeScore η p ∈ Icc 0 1 :=
  smallOccupationTest_mem _ _

theorem measurable_firstThreeScore {Ω : Type*} [MeasurableSpace Ω] (η : ℝ)
    (p : ℕ → Ω → ℝ) (hp : ∀ i, Measurable (p i)) :
    Measurable (fun ω => firstThreeScore η (fun i => p i ω)) := by
  unfold firstThreeScore smallOccupationTest
  fun_prop

theorem tendsto_firstThreeScore {η : ℝ} {p : ℕ → ℕ → ℝ} {q : ℕ → ℝ}
    (h : ∀ i, Tendsto (fun n => p n i) atTop (𝓝 (q i))) :
    Tendsto (fun n => firstThreeScore η (p n)) atTop (𝓝 (firstThreeScore η q)) := by
  unfold firstThreeScore smallOccupationTest
  exact tendsto_const_nhds.max (tendsto_const_nhds.min
    (tendsto_const_nhds.sub (((h 0).min ((h 1).min (h 2))).div_const _)))

/-- Measurability of the cutoff and degree-trimmed occupation coordinates. -/
theorem measurable_cutoffRootOccupation (β d R z : ℝ) (i : ℕ) :
    Measurable (fun ω => cutoffRootOccupation β d R z ω i) := by
  have h := measurable_cutoffKernel β R
  have hW : Measurable (fun ω : Environment =>
      weightFor (cutoffKernel β R) d ω [] i) := by
    apply h.comp
    unfold arrivalLength
    fun_prop
  exact (hW.mul (measurable_lowerFor h d z [])).mul
    (measurable_lowerFor h d z (child [] i))

private theorem measurable_cutoffDegree (d R : ℝ) (v : Vertex) :
    Measurable (fun ω => cutoffDegree d R ω v) :=
  ((measurable_to_countable' (measurableSet_cutoffOffspringNat_eq d R)).comp
    (measurable_pi_apply v)).add_const _

private theorem measurable_cutoffColumnDegree (d R : ℝ) (D : ℕ) (v : Vertex) :
    Measurable (fun ω => cutoffColumnDegree d R D ω v) := by
  let m (ω : Environment) := cutoffOffspringNat d R (ω v)
  let a (i : ℕ) (ω : Environment) := if cutoffDegree d R ω (child v i) ≤ D then 1 else 0
  let b (ω : Environment) := if v = [] then 0 else if cutoffDegree d R ω v.dropLast ≤ D then 1 else 0
  have hm : Measurable m :=
    (measurable_to_countable' (measurableSet_cutoffOffspringNat_eq d R)).comp
      (measurable_pi_apply v)
  have ha (i : ℕ) : Measurable (a i) :=
    Measurable.ite (measurableSet_le (measurable_cutoffDegree d R _) measurable_const)
      measurable_const measurable_const
  have hb : Measurable b := by
    unfold b
    split_ifs with h
    · exact measurable_const
    · exact Measurable.ite
        (measurableSet_le (measurable_cutoffDegree d R _) measurable_const)
        measurable_const measurable_const
  apply measurable_to_countable'
  intro k
  have heq : {ω | cutoffColumnDegree d R D ω v = k} =
      ⋃ n : ℕ, ({ω | m ω = n} ∩ {ω | (∑ i ∈ Finset.range n, a i ω) + b ω = k}) := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
    have hs (n : ℕ) : (∑ i ∈ Finset.range n, a i ω) =
        ((Finset.range n).filter (fun i => cutoffDegree d R ω (child v i) ≤ D)).card := by
      simp [a]
    constructor
    · intro h
      exact ⟨m ω, rfl, by simpa only [hs, cutoffColumnDegree, m, b] using h⟩
    · rintro ⟨n, hn, h⟩
      rw [← hn] at h
      simpa only [hs, cutoffColumnDegree, m, b] using h
  change MeasurableSet {ω | cutoffColumnDegree d R D ω v = k}
  rw [heq]
  exact MeasurableSet.iUnion fun n =>
    (measurableSet_eq_fun hm measurable_const).inter
      (measurableSet_eq_fun ((Finset.measurable_fun_sum _ fun i _ => ha i).add hb) measurable_const)

theorem measurable_trimmedWeight (β d R : ℝ) (D : ℕ) (v : Vertex) (i : ℕ) :
    Measurable (fun ω => trimmedWeight β d R D ω v i) := by
  have hW : Measurable (fun ω : Environment => weightFor (cutoffKernel β R) d ω v i) := by
    apply (measurable_cutoffKernel β R).comp
    unfold arrivalLength
    fun_prop
  have hset (r c : Vertex) : MeasurableSet {ω : Environment |
      cutoffDegree d R ω r ≤ D ∧ cutoffColumnDegree d R D ω c ≤ D} :=
    (measurableSet_le (measurable_cutoffDegree d R r) measurable_const).inter
      (measurableSet_le (measurable_cutoffColumnDegree d R D c) measurable_const)
  by_cases h : v.length % 2 = 0
  · simpa only [trimmedWeight, if_pos h] using Measurable.ite (hset v (child v i)) hW measurable_const
  · simpa only [trimmedWeight, if_neg h] using Measurable.ite (hset (child v i) v) hW measurable_const

private theorem measurable_trimmedDepth (β d R z : ℝ) (D k : ℕ) (v : Vertex) :
    Measurable (fun ω => TreeBoundary.bounds z child (trimmedWeight β d R D ω) k v) := by
  induction k generalizing v with
  | zero => exact measurable_const
  | succ k ih =>
    simp only [TreeBoundary.bounds, TreeBoundary.update]
    exact ((measurable_const.add (Measurable.tsum fun i =>
      (measurable_trimmedWeight β d R D v i).mul (ih (child v i)).snd)).inv).prodMk
      ((measurable_const.add (Measurable.tsum fun i =>
        (measurable_trimmedWeight β d R D v i).mul (ih (child v i)).fst)).inv)

theorem measurable_trimmedRootOccupation (β d R z : ℝ) (D i : ℕ) :
    Measurable (fun ω => trimmedRootOccupation β d R z D ω i) :=
  ((measurable_trimmedWeight β d R D [] i).mul
    (Measurable.iInf fun k => (measurable_trimmedDepth β d R z D k []).snd)).mul
    (Measurable.iSup fun k => (measurable_trimmedDepth β d R z D k (child [] i)).fst)

theorem tendsto_integral_of_mem_Icc {f : ℕ → Environment → ℝ} {g : Environment → ℝ}
    (hm : ∀ n, Measurable (f n)) (hb : ∀ n ω, f n ω ∈ Icc 0 1)
    (ht : ∀ᵐ ω ∂law, Tendsto (fun n => f n ω) atTop (𝓝 (g ω))) :
    Tendsto (fun n => ∫ ω, f n ω ∂law) atTop (𝓝 (∫ ω, g ω ∂law)) := by
  let : IsProbabilityMeasure law := isProbabilityMeasure_law
  refine tendsto_integral_of_dominated_convergence (fun _ => 1)
    (fun n => (hm n).aestronglyMeasurable) (integrable_const _) (fun n => ?_) ht
  exact Eventually.of_forall fun ω => (Real.norm_of_nonneg (hb n ω).1).trans_le (hb n ω).2

theorem tendsto_integral_square_of_sqSum {p : ℕ → Environment → ℕ → ℝ}
    {q : Environment → ℕ → ℝ} (hm : ∀ n i, Measurable (fun ω => p n ω i))
    (ht : ∀ᵐ ω ∂law, Tendsto (fun n => ∑' i, (p n ω i)^2) atTop (𝓝 (∑' i, (q ω i)^2))) :
    Tendsto (fun n => ∫ ω, min 1 (∑' i, (p n ω i)^2) ∂law) atTop
      (𝓝 (∫ ω, min 1 (∑' i, (q ω i)^2) ∂law)) := by
  apply tendsto_integral_of_mem_Icc
  · exact fun n => measurable_const.min (Measurable.tsum fun i => (hm n i).pow_const 2)
  · exact fun n ω => ⟨le_min zero_le_one (tsum_nonneg fun _ => sq_nonneg _), min_le_left _ _⟩
  · exact ht.mono fun _ h => tendsto_const_nhds.min h

theorem tendsto_integral_firstThreeScore {η : ℝ} {p : ℕ → Environment → ℕ → ℝ}
    {q : Environment → ℕ → ℝ} (hm : ∀ n i, Measurable (fun ω => p n ω i))
    (ht : ∀ᵐ ω ∂law, ∀ i, Tendsto (fun n => p n ω i) atTop (𝓝 (q ω i))) :
    Tendsto (fun n => ∫ ω, firstThreeScore η (p n ω) ∂law) atTop
      (𝓝 (∫ ω, firstThreeScore η (q ω) ∂law)) :=
  tendsto_integral_of_mem_Icc (fun n => measurable_firstThreeScore η _ (hm n))
    (fun n ω => firstThreeScore_mem_Icc η (p n ω)) (ht.mono fun _ => tendsto_firstThreeScore)

/-- The full-tree smooth test of the first three occupations has arbitrarily
small expectation, at a fixed threshold for all sufficiently small fugacities. -/
theorem eventually_integral_firstThreeScore_full_lt {β d : ℝ}
    (hβ : 0 < β) (hd : 0 < d) (H : ProbabilityMeasure ℝ)
    (hH : IsCavityLaw β d (H : Measure ℝ))
    (hUnique : ∀ ν : Measure ℝ, IsCavityLaw β d ν → ν = (H : Measure ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ z in 𝓝[>] (0:ℝ),
      (∫ ω, firstThreeScore η (fullRootOccupation β d z ω) ∂law) < ε := by
  obtain ⟨a,ha,hsmall⟩ :=
    eventually_measure_firstThree_rootOccupation_small hβ hd H hH hUnique
      (show 0 < ε/2 by positivity)
  let η := a/2
  have hη : 0 < η := by dsimp [η]; positivity
  refine ⟨η,hη,?_⟩
  filter_upwards [hsmall,self_mem_nhdsWithin] with z hsmall hz
  have hz' : 0 < z := hz
  let P := markedSpacings (softCavityProbability β d z : Measure ℝ)
  let : IsProbabilityMeasure P := inferInstanceAs
    (IsProbabilityMeasure (markedSpacings (softCavityProbability β d z : Measure ℝ)))
  let f (ω : ArrivalConfiguration) := firstThreeScore η (rootOccupation β d z ω)
  let B : Set ArrivalConfiguration := {ω | ∃ i : Fin 3, rootOccupation β d z ω i.val ≤ a}
  have hB : MeasurableSet B := by
    have heq : B = ⋃ i : Fin 3, {ω | rootOccupation β d z ω i.val ≤ a} := by
      ext ω
      simp [B]
    rw [heq]
    exact MeasurableSet.iUnion fun i =>
      measurableSet_le (measurable_rootOccupation β d z i.val) measurable_const
  have hf := measurable_firstThreeScore η (fun i ω => rootOccupation β d z ω i)
    (measurable_rootOccupation β d z)
  have hf' : Integrable f P :=
    (integrable_const (1:ℝ)).mono' hf.aestronglyMeasurable <|
      Eventually.of_forall fun ω =>
        (Real.norm_of_nonneg (firstThreeScore_mem_Icc η (rootOccupation β d z ω)).1).trans_le
          (firstThreeScore_mem_Icc η (rootOccupation β d z ω)).2
  have hle (ω : ArrivalConfiguration) : f ω ≤ B.indicator (fun _ => (1:ℝ)) ω := by
    by_cases h : ω ∈ B
    · rw [indicator_of_mem h]
      exact (firstThreeScore_mem_Icc _ _).2
    · rw [indicator_of_notMem h]
      have hi (i : Fin 3) : a ≤ rootOccupation β d z ω i.val :=
        (lt_of_not_ge fun hi => h ⟨i,hi⟩).le
      have hmin := le_min (hi 0) (le_min (hi 1) (hi 2))
      have hthreshold : 2*η ≤ min (rootOccupation β d z ω 0)
          (min (rootOccupation β d z ω 1) (rootOccupation β d z ω 2)) := by
        have he : 2*η = a := by dsimp [η]; ring
        rw [he]
        exact hmin
      exact (smallOccupationTest_eq_zero hη hthreshold).le
  calc
    _ = ∫ ω, f (rootSoftMarks β d z ω) ∂law := by
      apply integral_congr_ae
      filter_upwards [ae_fullRootOccupation_eq hβ hd hz'] with ω hω
      simp only [f, firstThreeScore, hω]
    _ = ∫ ω, f ω ∂P := by
      have hmap : law.map (rootSoftMarks β d z) = P := map_rootSoftMarks β d z
      rw [← hmap, integral_map (measurable_rootSoftMarks β d z).aemeasurable
        hf.aestronglyMeasurable]
    _ ≤ ∫ ω, B.indicator (fun _ => (1:ℝ)) ω ∂P :=
      integral_mono hf' ((integrable_const _).indicator hB) hle
    _ ≤ ε/2 := by
      have hInt : (∫ ω, B.indicator (fun _ => (1:ℝ)) ω ∂P) = P.real B :=
        integral_indicator_one (μ := P) hB
      rw [hInt, Measure.real]
      have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsmall
      rwa [ENNReal.toReal_ofReal (by positivity : 0 ≤ ε/2)] at hh
    _ < ε := by linarith

end Certificate.CanonicalTree

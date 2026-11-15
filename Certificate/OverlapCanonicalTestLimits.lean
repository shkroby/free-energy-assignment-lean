import Certificate.OverlapCanonicalOccupation
import Certificate.OverlapCanonicalSupport
import Certificate.OverlapCanonicalIterates

/-! Fixed-cutoff occupation vectors determine the two bounded test integrals. -/

open Filter MeasureTheory Set
open scoped Topology

namespace Certificate.CanonicalTree

open Overlap

private theorem measurable_switchCount {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {s : X → ℕ} (hs : Measurable s) {f : ℕ → X → Y} (hf : ∀ n, Measurable (f n)) :
    Measurable (fun x => f (s x) x) := by
  intro A hA
  have heq : (fun x => f (s x) x) ⁻¹' A = ⋃ n : ℕ,
      ({x | s x = n} ∩ f n ⁻¹' A) := by
    ext x
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_ofPred_eq]
    exact ⟨fun h => ⟨s x, rfl, h⟩, fun ⟨n, h, hn⟩ => h.symm ▸ hn⟩
  rw [heq]
  exact MeasurableSet.iUnion fun n =>
    (measurableSet_eq_fun hs measurable_const).inter (hf n hA)

private theorem measurable_rootCutoffCount (d R : ℝ) :
    Measurable (fun ω : Environment => cutoffOffspringNat d R (ω [])) :=
  (measurable_to_countable' (measurableSet_cutoffOffspringNat_eq d R)).comp
    (measurable_pi_apply [])

private theorem measurable_trimmedRootOccupationIterate (β d R z : ℝ) (D k i : ℕ) :
    Measurable (fun ω => trimmedRootOccupationIterate β d R z D k ω i) := by
  have hdown (k : ℕ) (v : Vertex) :
      Measurable (fun ω => trimmedDownwardIterate β d R z D k ω v) := by
    induction k generalizing v with
    | zero => exact measurable_const
    | succ k ih =>
      exact (measurable_const.add (Measurable.tsum fun j =>
        (measurable_trimmedWeight β d R D v j).mul (ih (child v j)))).inv
  have hcav : Measurable (fun ω => trimmedRootCavityIterate β d R z D ω k i) := by
    cases k with
    | zero => exact measurable_const
    | succ k =>
      have hweight (j : ℕ) : Measurable (fun ω : Environment =>
          if j = i then 0 else trimmedWeight β d R D ω [] j) := by
        by_cases h : j = i
        · simp [h]
        · simpa only [if_neg h] using measurable_trimmedWeight β d R D [] j
      exact (measurable_const.add (Measurable.tsum fun j =>
        (hweight j).mul (hdown k (child [] j)))).inv
  let hp := ((measurable_trimmedWeight β d R D [] i).mul hcav).mul (hdown k (child [] i))
  exact hp.div (measurable_const.add hp)

private theorem continuousAt_rowTest_of_continuous
    (p : ℕ → ℕ → ℝ) (q : ℕ → ℝ) (h : ∀ i, Tendsto (fun k => p k i) atTop (𝓝 (q i)))
    {F : (ℕ → ℝ) → ℝ} (hF : Continuous F) :
    Tendsto (fun k => F (p k)) atTop (𝓝 (F q)) :=
  hF.continuousAt.tendsto.comp (tendsto_pi_nhds.mpr h)

theorem tendsto_integral_trimmedSquareTest {β d R z : ℝ} (hd : 0 < d) (hR : 0 ≤ R) (D : ℕ)
    (ht : ∀ᵐ ω ∂law, ∀ i, Tendsto (fun k => trimmedRootOccupationIterate β d R z D k ω i)
      atTop (𝓝 (trimmedRootOccupation β d R z D ω i))) :
    Tendsto (fun k => ∫ ω, trimmedSquareTest β d R z D k ω ∂law) atTop
      (𝓝 (∫ ω, min 1 (∑' i, (trimmedRootOccupation β d R z D ω i)^2) ∂law)) := by
  apply tendsto_integral_of_mem_Icc
  · intro k
    apply measurable_switchCount (f := fun n ω => squareRowTest (Finset.range n)
      (trimmedRootOccupationIterate β d R z D k ω)) (measurable_rootCutoffCount d R)
    intro n
    exact measurable_const.min (Finset.measurable_fun_sum _ fun i _ =>
      (measurable_trimmedRootOccupationIterate β d R z D k i).pow_const 2)
  · exact fun _ _ => squareRowTest_mem _ _
  · filter_upwards [ht, ae_cutoffKernel_eq_zero_off_range hd hR β] with ω h hzero
    let s := Finset.range (cutoffOffspringNat d R (ω []))
    have hs (i : ℕ) (hi : i ∉ s) : (trimmedRootOccupation β d R z D ω i)^2 = 0 := by
      have hw := trimmedWeight_bounds β d R D ω [] i
      have hz : trimmedWeight β d R D ω [] i = 0 :=
        le_antisymm (hw.2.trans_eq (hzero [] i hi)) hw.1
      simp [trimmedRootOccupation, hz]
    rw [tsum_eq_sum hs]
    exact continuousAt_rowTest_of_continuous _ _ h
      (continuous_squareRowTest s (fun p : ℕ → ℝ => p) (fun i _ => continuous_apply i))

noncomputable def trimmedThirdScore (β d R z η : ℝ) (D : ℕ) (ω : Environment) : ℝ :=
  smallOccupationTest η (thirdOccupation (Finset.range (cutoffOffspringNat d R (ω [])))
    (trimmedRootOccupation β d R z D ω))

theorem tendsto_integral_trimmedSmallThirdTest {β d R z η : ℝ} (D : ℕ)
    (ht : ∀ᵐ ω ∂law, ∀ i, Tendsto (fun k => trimmedRootOccupationIterate β d R z D k ω i)
      atTop (𝓝 (trimmedRootOccupation β d R z D ω i))) :
    Tendsto (fun k => ∫ ω, trimmedSmallThirdTest β d R z η D k ω ∂law) atTop
      (𝓝 (∫ ω, trimmedThirdScore β d R z η D ω ∂law)) := by
  apply tendsto_integral_of_mem_Icc
  · intro k
    apply measurable_switchCount (f := fun n ω => smallOccupationTest η
      (thirdOccupation (Finset.range n) (trimmedRootOccupationIterate β d R z D k ω)))
        (measurable_rootCutoffCount d R)
    intro n
    exact ((continuous_smallOccupationTest η).comp (continuous_thirdOccupation
      (Finset.range n) (fun p : ℕ → ℝ => p) (fun i _ => continuous_apply i))).measurable.comp
        (measurable_pi_iff.mpr (measurable_trimmedRootOccupationIterate β d R z D k))
  · exact fun _ _ => smallOccupationTest_mem _ _
  · filter_upwards [ht] with ω h
    exact continuousAt_rowTest_of_continuous _ _ h <|
      (continuous_smallOccupationTest η).comp <| continuous_thirdOccupation
        _ (fun p : ℕ → ℝ => p) (fun i _ => continuous_apply i)

theorem integral_trimmedThirdScore_le_firstThreeScore {β d R z η : ℝ} (hd : 0 < d)
    (hR : 0 ≤ R) (hη : 0 < η) (D : ℕ) :
    (∫ ω, trimmedThirdScore β d R z η D ω ∂law) ≤
      ∫ ω, firstThreeScore η (trimmedRootOccupation β d R z D ω) ∂law := by
  let : IsProbabilityMeasure law := isProbabilityMeasure_law
  have hm : Measurable (trimmedThirdScore β d R z η D) := by
    apply measurable_switchCount (f := fun n ω => smallOccupationTest η
      (thirdOccupation (Finset.range n) (trimmedRootOccupation β d R z D ω)))
        (measurable_rootCutoffCount d R)
    intro n
    exact ((continuous_smallOccupationTest η).comp (continuous_thirdOccupation
      (Finset.range n) (fun p : ℕ → ℝ => p) (fun i _ => continuous_apply i))).measurable.comp
        (measurable_pi_iff.mpr (measurable_trimmedRootOccupation β d R z D))
  have hm' := measurable_firstThreeScore η (fun i ω => trimmedRootOccupation β d R z D ω i)
    (measurable_trimmedRootOccupation β d R z D)
  apply integral_mono_ae
    (Integrable.of_bound hm.aestronglyMeasurable 1 (Eventually.of_forall fun ω => by
      unfold trimmedThirdScore
      rw [Real.norm_of_nonneg (smallOccupationTest_mem _ _).1]
      exact (smallOccupationTest_mem _ _).2))
    (Integrable.of_bound hm'.aestronglyMeasurable 1 (Eventually.of_forall fun ω => by
      rw [Real.norm_of_nonneg (firstThreeScore_mem_Icc _ _).1]
      exact (firstThreeScore_mem_Icc _ _).2))
  filter_upwards [ae_cutoffKernel_eq_zero_off_range hd hR β] with ω hzero
  let p := trimmedRootOccupation β d R z D ω
  let t := min (p 0) (min (p 1) (p 2))
  by_cases h : t ≤ 0
  · rw [show firstThreeScore η p = 1 from smallOccupationTest_eq_one hη (h.trans hη.le)]
    exact (smallOccupationTest_mem _ _).2
  have ht : 0 < t := lt_of_not_ge h
  let s := Finset.range (cutoffOffspringNat d R (ω []))
  have hmem (i : ℕ) (hi : t ≤ p i) : i ∈ s := by
    by_contra hout
    have hw := trimmedWeight_bounds β d R D ω [] i
    have hz : trimmedWeight β d R D ω [] i = 0 :=
      le_antisymm (hw.2.trans_eq (hzero [] i hout)) hw.1
    exact (ne_of_gt (ht.trans_le hi)) (by simp [p,trimmedRootOccupation,hz])
  have h0 : t ≤ p 0 := min_le_left _ _
  have h1 : t ≤ p 1 := (min_le_right _ _).trans (min_le_left _ _)
  have h2 : t ≤ p 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hle : t ≤ thirdOccupation s p := (threeLargeOn_iff_le_thirdOccupation ht).mp
    ⟨0, hmem 0 h0, 1, hmem 1 h1, 2, hmem 2 h2, by decide, by decide, by decide, h0, h1, h2⟩
  change smallOccupationTest η (thirdOccupation s p) ≤ smallOccupationTest η t
  unfold smallOccupationTest
  exact max_le_max le_rfl (min_le_min le_rfl
    (sub_le_sub_left (div_le_div_of_nonneg_right hle hη.le) _))

end Certificate.CanonicalTree

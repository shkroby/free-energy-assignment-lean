import Certificate.Intensity
import Certificate.PoissonArrival

/-!
# Marked insertion on the exponential arrival space

Deleting the chosen arrival merges its adjacent exponential gaps and deletes
its corresponding independent mark. The indexed split identity recovers the
remaining law and the integration over the split position. Summing over the
gaps gives all positive time, which the power map sends to the length
intensity in the assignment model.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators

namespace Certificate

variable {Y : Type*} [MeasurableSpace Y]

/-- Canonical positive-time exponential arrivals with independent iid marks. -/
noncomputable def markedArrivalSequenceLaw (μ : Measure Y) : Measure ((ℕ → ℝ) × (ℕ → Y)) :=
  exponentialSpacings.prod (Measure.infinitePi (fun _ : ℕ => μ))

theorem isProbabilityMeasure_markedArrivalSequenceLaw (μ : Measure Y) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (markedArrivalSequenceLaw μ) := by
  let : IsProbabilityMeasure exponentialSpacings := isProbabilityMeasure_exponentialSpacings
  unfold markedArrivalSequenceLaw
  infer_instance

/-- Deleting arrival `i` does not change the time at the start of its gap. -/
theorem arrivalPrefix_eraseArrivalGap (ω : ℕ → ℝ) (i : ℕ) :
    arrivalPrefix (eraseArrivalGap i ω) i = arrivalPrefix ω i := by
  unfold arrivalPrefix
  apply Finset.sum_congr rfl
  intro j hj
  have hji : j < i := Finset.mem_range.mp hj
  rw [eraseArrivalGap, Function.update_of_ne hji.ne,
    eraseSequence_apply_of_lt ω (hji.trans (Nat.lt_succ_self i))]

private theorem measurable_lintegral_split {Ω : Type*} [MeasurableSpace Ω]
    {u : Ω → ℝ} (hu : Measurable u) {f : Ω × ℝ → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun z => ∫⁻ a in Ioo 0 (u z), f (z,a)) := by
  let D : Set (Ω × ℝ) := {p | 0 < p.2 ∧ p.2 < u p.1}
  have hD : MeasurableSet D := (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd (hu.comp measurable_fst))
  have hM := (hf.indicator hD).lintegral_prod_right' (ν := volume)
  have heq : (fun z => ∫⁻ a in Ioo 0 (u z), f (z,a)) =
      (fun z => ∫⁻ a, D.indicator f (z,a)) := by
    funext z
    exact (lintegral_indicator measurableSet_Ioo (fun a => f (z,a))).symm
  rw [heq]
  exact hM

private def deletedArrivalTest (g : (ℝ × Y) × ((ℕ → ℝ) × (ℕ → Y)) → ℝ≥0∞) (i : ℕ) (ω : (ℕ → ℝ) × (ℕ → Y)) : ℝ≥0∞ :=
  g ((arrivalPrefix ω.1 (i+1), ω.2 i), (eraseArrivalGap i ω.1, eraseSequence i ω.2))

private noncomputable def splitArrivalTest (g : (ℝ × Y) × ((ℕ → ℝ) × (ℕ → Y)) → ℝ≥0∞) (i : ℕ) (ω : (ℕ → ℝ)) (z : Y × (ℕ → Y)) : ℝ≥0∞ :=
  ∫⁻ a in Ioo 0 (ω i), g ((arrivalPrefix ω i+a, z.1), (ω,z.2))

private theorem measurable_deletedArrivalTest {g : (ℝ × Y) × ((ℕ → ℝ) × (ℕ → Y)) → ℝ≥0∞} (hg : Measurable g) (i : ℕ) :
    Measurable (deletedArrivalTest g i) := by
  unfold deletedArrivalTest
  fun_prop

private theorem measurable_splitArrivalTest {g : (ℝ × Y) × ((ℕ → ℝ) × (ℕ → Y)) → ℝ≥0∞} (hg : Measurable g) (i : ℕ) :
    Measurable (Function.uncurry (splitArrivalTest g i)) := by
  let T (p : (ℕ → ℝ) × (Y × (ℕ → Y))) := p.1 i
  let F (p : ((ℕ → ℝ) × (Y × (ℕ → Y))) × ℝ) :=
    g ((arrivalPrefix p.1.1 i+p.2, p.1.2.1), (p.1.1,p.1.2.2))
  have hT : Measurable T := (measurable_pi_apply i).comp measurable_fst
  have hF : Measurable F := by dsimp [F]; fun_prop
  exact measurable_lintegral_split hT hF

private theorem lintegral_deletedArrivalTest (μ : Measure Y) [IsProbabilityMeasure μ]
    (g : (ℝ × Y) × ((ℕ → ℝ) × (ℕ → Y)) → ℝ≥0∞) (hg : Measurable g) (i : ℕ) :
    (∫⁻ ω, deletedArrivalTest g i ω ∂markedArrivalSequenceLaw μ) =
      ∫⁻ r, ∫⁻ z, splitArrivalTest g i r z
        ∂μ.prod (Measure.infinitePi (fun _ : ℕ => μ)) ∂exponentialSpacings := by
  let P := exponentialSpacings
  let M := Measure.infinitePi (fun _ : ℕ => μ)
  let Q := μ.prod M
  let A (r : (ℕ → ℝ)) (z : Y × (ℕ → Y)) :=
    g ((arrivalPrefix r (i+1),z.1), (eraseArrivalGap i r,z.2))
  let : IsProbabilityMeasure P := isProbabilityMeasure_exponentialSpacings
  have hA : Measurable (Function.uncurry A) := by dsimp [A, Function.uncurry]; fun_prop
  have hAr (r : (ℕ → ℝ)) : Measurable (A r) := hA.comp (measurable_const.prodMk measurable_id)
  have hK (z : Y × (ℕ → Y)) : (∫⁻ r, A r z ∂P) = ∫⁻ r, splitArrivalTest g i r z ∂P := by
    let B (p : ℝ × (ℕ → ℝ)) := g ((arrivalPrefix p.2 i + p.1,z.1), (p.2,z.2))
    have hB : Measurable B := by dsimp [B]; fun_prop
    calc
      _ = ∫⁻ r, B (r i, eraseArrivalGap i r) ∂P := by
        apply lintegral_congr
        intro r
        simp only [A, B, arrivalPrefix_succ, arrivalPrefix_eraseArrivalGap]
      _ = ∫⁻ r, (∫⁻ a in Ioo 0 (r i), B (a,r)) ∂P := exp_indexed_gap_split_lintegral i B hB
      _ = _ := rfl
  have hsplit : Measurable (Function.uncurry (splitArrivalTest g i)) :=
    measurable_splitArrivalTest hg i
  change (∫⁻ ω, deletedArrivalTest g i ω ∂P.prod M) = _
  calc
    _ = ∫⁻ r, ∫⁻ m, deletedArrivalTest g i (r,m) ∂M ∂P :=
      lintegral_prod _ (measurable_deletedArrivalTest hg i).aemeasurable
    _ = ∫⁻ r, ∫⁻ z, A r z ∂Q ∂P :=
      lintegral_congr (fun r => iid_eraseSequence_lintegral μ i (A r) (hAr r))
    _ = ∫⁻ z, ∫⁻ r, A r z ∂P ∂Q := lintegral_lintegral_swap hA.aemeasurable
    _ = ∫⁻ z, ∫⁻ r, splitArrivalTest g i r z ∂P ∂Q := lintegral_congr hK
    _ = ∫⁻ r, ∫⁻ z, splitArrivalTest g i r z ∂Q ∂P :=
      (lintegral_lintegral_swap hsplit.aemeasurable).symm

private theorem lintegral_arrivalTest_sum (μ : Measure Y) [IsProbabilityMeasure μ]
    (g : (ℝ × Y) × ((ℕ → ℝ) × (ℕ → Y)) → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ ω, ∑' i, deletedArrivalTest g i ω ∂markedArrivalSequenceLaw μ) =
      ∫⁻ r, ∫⁻ z, (∫⁻ t in Ioi (0:ℝ), g ((t,z.1),(r,z.2)))
        ∂μ.prod (Measure.infinitePi (fun _ : ℕ => μ)) ∂exponentialSpacings := by
  let P := exponentialSpacings
  let M := Measure.infinitePi (fun _ : ℕ => μ)
  let Q := μ.prod M
  rw [lintegral_tsum (fun i => (measurable_deletedArrivalTest hg i).aemeasurable)]
  simp_rw [lintegral_deletedArrivalTest μ g hg]
  have hM (i : ℕ) : Measurable (fun r => ∫⁻ z, splitArrivalTest g i r z ∂Q) :=
    (measurable_splitArrivalTest hg i).lintegral_prod_right' (ν := Q)
  rw [← lintegral_tsum (fun i => (hM i).aemeasurable)]
  apply lintegral_congr_ae
  filter_upwards [ae_arrivalGap_partition_lintegral] with r hr
  have hz (i : ℕ) : Measurable (splitArrivalTest g i r) :=
    (measurable_splitArrivalTest hg i).comp (measurable_const.prodMk measurable_id)
  rw [← lintegral_tsum (fun i => (hz i).aemeasurable)]
  apply lintegral_congr
  intro z
  have hgz : Measurable (fun t => g ((t,z.1),(r,z.2))) := by fun_prop
  exact hr _ hgz

private theorem lintegral_arrivalTest_reorder (μ : Measure Y) [IsProbabilityMeasure μ]
    (g : (ℝ × Y) × ((ℕ → ℝ) × (ℕ → Y)) → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ r, ∫⁻ z, (∫⁻ t in Ioi (0:ℝ), g ((t,z.1),(r,z.2)))
      ∂μ.prod (Measure.infinitePi (fun _ : ℕ => μ)) ∂exponentialSpacings) =
        ∫⁻ p, g p ∂((volume.restrict (Ioi (0:ℝ))).prod μ).prod (markedArrivalSequenceLaw μ) := by
  let V := (volume : Measure ℝ).restrict (Ioi (0:ℝ))
  let P := exponentialSpacings
  let M := Measure.infinitePi (fun _ : ℕ => μ)
  let Q := μ.prod M
  let : IsProbabilityMeasure P := isProbabilityMeasure_exponentialSpacings
  let T (r : (ℕ → ℝ)) (t : ℝ) (z : Y × (ℕ → Y)) := g ((t,z.1),(r,z.2))
  have hTr (r : (ℕ → ℝ)) : Measurable (Function.uncurry (T r)) := by
    dsimp [T, Function.uncurry]; fun_prop
  have hT : Measurable (fun p : ((ℕ → ℝ) × ℝ) × (Y × (ℕ → Y)) => T p.1.1 p.1.2 p.2) := by
    dsimp [T]; fun_prop
  have hI : Measurable (fun p : (ℕ → ℝ) × ℝ => ∫⁻ z, T p.1 p.2 z ∂Q) :=
    hT.lintegral_prod_right' (ν := Q)
  have hIz (r : (ℕ → ℝ)) (t : ℝ) : Measurable (T r t) :=
    (hTr r).comp (measurable_const.prodMk measurable_id)
  have hT2 (t : ℝ) : Measurable (fun p : ((ℕ → ℝ) × Y) × (ℕ → Y) => g ((t,p.1.2),(p.1.1,p.2))) := by fun_prop
  have hI2 (t : ℝ) : Measurable (fun p : (ℕ → ℝ) × Y => ∫⁻ m, g ((t,p.2),(p.1,m)) ∂M) :=
    (hT2 t).lintegral_prod_right' (ν := M)
  have hG (p : ℝ × Y) : Measurable (fun q : ((ℕ → ℝ) × (ℕ → Y)) => g (p,q)) := by fun_prop
  have hG2 : Measurable (fun p : ℝ × Y => ∫⁻ ω, g (p,ω) ∂P.prod M) :=
    hg.lintegral_prod_right' (ν := P.prod M)
  change (∫⁻ r, ∫⁻ z, ∫⁻ t, T r t z ∂V ∂Q ∂P) =
    ∫⁻ p, g p ∂(V.prod μ).prod (P.prod M)
  calc
    _ = ∫⁻ r, ∫⁻ t, ∫⁻ z, T r t z ∂Q ∂V ∂P :=
      lintegral_congr (fun r =>
        (lintegral_lintegral_swap (hTr r).aemeasurable).symm)
    _ = ∫⁻ t, ∫⁻ r, ∫⁻ z, T r t z ∂Q ∂P ∂V := lintegral_lintegral_swap hI.aemeasurable
    _ = ∫⁻ t, ∫⁻ r, ∫⁻ y, ∫⁻ m, g ((t,y),(r,m)) ∂M ∂μ ∂P ∂V :=
      lintegral_congr (fun t => lintegral_congr (fun r => lintegral_prod _ (hIz r t).aemeasurable))
    _ = ∫⁻ t, ∫⁻ y, ∫⁻ r, ∫⁻ m, g ((t,y),(r,m)) ∂M ∂P ∂μ ∂V :=
      lintegral_congr (fun t => lintegral_lintegral_swap (hI2 t).aemeasurable)
    _ = ∫⁻ t, ∫⁻ y, ∫⁻ ω, g ((t,y),ω) ∂P.prod M ∂μ ∂V :=
      lintegral_congr (fun t =>
        lintegral_congr (fun y => (lintegral_prod _ (hG (t,y)).aemeasurable).symm))
    _ = ∫⁻ z, (∫⁻ ω, g (z,ω) ∂P.prod M) ∂V.prod μ :=
      (lintegral_prod _ hG2.aemeasurable).symm
    _ = _ := (lintegral_prod _ hg.aemeasurable).symm

/-- Nonnegative marked Mecke identity for the unit-rate exponential arrivals. -/
theorem canonical_iid_marked_time_insertion (μ : Measure Y) [IsProbabilityMeasure μ]
    (g : (ℝ × Y) × ((ℕ → ℝ) × (ℕ → Y)) → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ ω, ∑' i, g ((arrivalPrefix ω.1 (i+1), ω.2 i),
        (eraseArrivalGap i ω.1, eraseSequence i ω.2)) ∂markedArrivalSequenceLaw μ) =
      ∫⁻ z, g z ∂((volume.restrict (Ioi (0:ℝ))).prod μ).prod (markedArrivalSequenceLaw μ) :=
  (lintegral_arrivalTest_sum μ g hg).trans (lintegral_arrivalTest_reorder μ g hg)

/-- Nonnegative marked Mecke identity for the exact canonical law used by
`IsCavityLaw`. The power map changes unit-rate time into length. -/
theorem canonical_iid_marked_arrival_insertion {d : ℝ} (hd : 0 < d)
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (g : (ℝ × Y) × ((ℕ → ℝ) × (ℕ → Y)) → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ ω, ∑' i, g ((arrivalLength d ω.1 i, ω.2 i),
        (eraseArrivalGap i ω.1, eraseSequence i ω.2)) ∂markedArrivalSequenceLaw μ) =
      ∫⁻ z, g z ∂((intensity d).prod μ).prod (markedArrivalSequenceLaw μ) := by
  let p : ℝ → ℝ := fun t => t ^ (1/d : ℝ)
  let p1 : ℝ × Y → ℝ × Y := Prod.map p id
  let p2 : (ℝ × Y) × ((ℕ → ℝ) × (ℕ → Y)) → (ℝ × Y) × ((ℕ → ℝ) × (ℕ → Y)) := Prod.map p1 id
  let V := (volume : Measure ℝ).restrict (Ioi 0)
  let P := markedArrivalSequenceLaw μ
  let : IsProbabilityMeasure P := isProbabilityMeasure_markedArrivalSequenceLaw μ
  have hp : Measurable p := by dsimp [p]; fun_prop
  have hp1 : Measurable p1 := hp.prodMap measurable_id
  have hp2 : Measurable p2 := hp1.prodMap measurable_id
  have hmap1 : (V.prod μ).map p1 = (intensity d).prod μ := by
    calc
      _ = (V.map p).prod (μ.map id) := (Measure.map_prod_map _ _ hp measurable_id).symm
      _ = _ := by
        rw [Measure.map_id]
        exact congrArg (fun v : Measure ℝ => v.prod μ) (map_volume_rpow_eq_intensity hd)
  have hmap : ((V.prod μ).prod P).map p2 = ((intensity d).prod μ).prod P := by
    calc
      _ = ((V.prod μ).map p1).prod (P.map id) :=
        (Measure.map_prod_map _ _ hp1 measurable_id).symm
      _ = _ := by rw [hmap1, Measure.map_id]
  have h := canonical_iid_marked_time_insertion μ (g ∘ p2) (hg.comp hp2)
  calc
    _ = ∫⁻ z, (g ∘ p2) z ∂(V.prod μ).prod P := h
    _ = ∫⁻ z, g z ∂((V.prod μ).prod P).map p2 := (lintegral_map hg hp2).symm
    _ = _ := by rw [hmap]

/-- Scalar-mark version on the manuscript's `markedSpacings` law. -/
theorem canonical_marked_time_insertion (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (g : (ℝ × ℝ) × ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ ω, ∑' i, g ((arrivalPrefix ω.1 (i+1), ω.2 i),
        (eraseArrivalGap i ω.1, eraseSequence i ω.2)) ∂markedSpacings μ) =
      ∫⁻ z, g z ∂((volume.restrict (Ioi (0:ℝ))).prod μ).prod (markedSpacings μ) :=
  canonical_iid_marked_time_insertion μ g hg

/-- Scalar-mark version on the manuscript's `markedSpacings` law. -/
theorem canonical_marked_arrival_insertion {d : ℝ} (hd : 0 < d)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (g : (ℝ × ℝ) × ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ ω, ∑' i, g ((arrivalLength d ω.1 i, ω.2 i),
        (eraseArrivalGap i ω.1, eraseSequence i ω.2)) ∂markedSpacings μ) =
      ∫⁻ z, g z ∂((intensity d).prod μ).prod (markedSpacings μ) :=
  canonical_iid_marked_arrival_insertion hd μ g hg

end Certificate

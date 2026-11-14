import Certificate.ArrivalDeletion
import Certificate.Endpoints
import Certificate.ComparisonIntegrability
import Certificate.PoissonArrivalMecke

/-!
# Endpoint exchange for an invariant hard coupling

On the canonical marked arrival law, deletion gives the root cavity pair
before the selected edge is inserted. The invariant-law assumption makes it
an independent draw of the same law as the selected child pair under Mecke.
Swapping those two pairs exchanges the full endpoints.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Certificate

abbrev PairedArrivalConfiguration := (ℕ → ℝ) × (ℕ → (ℝ × ℝ))

/-- The scalar configuration obtained from the first coordinates of the marks. -/
def firstArrivalConfiguration (ω : PairedArrivalConfiguration) : ArrivalConfiguration :=
  (ω.1, fun i => (ω.2 i).1)

/-- The scalar configuration obtained from the second coordinates of the marks. -/
def secondArrivalConfiguration (ω : PairedArrivalConfiguration) : ArrivalConfiguration :=
  (ω.1, fun i => (ω.2 i).2)

@[fun_prop] theorem measurable_firstArrivalConfiguration : Measurable firstArrivalConfiguration :=
  measurable_fst.prodMk (measurable_pi_lambda _ fun i =>
    measurable_fst.comp ((measurable_pi_apply i).comp measurable_snd))

@[fun_prop] theorem measurable_secondArrivalConfiguration : Measurable secondArrivalConfiguration :=
  measurable_fst.prodMk (measurable_pi_lambda _ fun i =>
    measurable_snd.comp ((measurable_pi_apply i).comp measurable_snd))

private noncomputable def scalarHardRoot (β d : ℝ) (ω : ArrivalConfiguration) : ℝ :=
  (arrivalWeightedSum β d ω).toReal⁻¹

/-- The two full root messages. Both use the same arrival lengths. -/
noncomputable def pairedHardRoot (β d : ℝ) (ω : PairedArrivalConfiguration) : ℝ × ℝ :=
  (scalarHardRoot β d (firstArrivalConfiguration ω),
    scalarHardRoot β d (secondArrivalConfiguration ω))

@[fun_prop] theorem measurable_pairedHardRoot (β d : ℝ) :
    Measurable (pairedHardRoot β d) := by
  have h₁ := ((measurable_arrivalWeightedSum β d).comp
    measurable_firstArrivalConfiguration).ennreal_toReal.inv
  have h₂ := ((measurable_arrivalWeightedSum β d).comp
    measurable_secondArrivalConfiguration).ennreal_toReal.inv
  exact h₁.prodMk h₂

/-- The pair of edge occupations in the two coupled systems. -/
noncomputable def pairedHardOccupation (β d : ℝ) (ω : PairedArrivalConfiguration)
    (i : ℕ) : ℝ × ℝ :=
  let w := Real.exp (-β * arrivalLength d ω.1 i)
  let A := pairedHardRoot β d ω
  let B := ω.2 i
  (w * B.1 * A.1, w * B.2 * A.2)

/-- The two messages at the full endpoint of the selected child. -/
noncomputable def pairedHardChild (β d : ℝ) (ω : PairedArrivalConfiguration)
    (i : ℕ) : ℝ × ℝ :=
  let a := pairedHardOccupation β d ω i
  ((1-a.1) * (ω.2 i).1, (1-a.2) * (ω.2 i).2)

private noncomputable def pairEdgeOccupation (w : ℝ) (A B : ℝ × ℝ) : ℝ × ℝ :=
  (edgeOccupation w A.1 B.1, edgeOccupation w A.2 B.2)

private noncomputable def pairFullEndpoint (w : ℝ) (A B : ℝ × ℝ) : ℝ × ℝ :=
  (fullEndpoint w A.1 B.1, fullEndpoint w A.2 B.2)

private theorem pairEdgeOccupation_swap (w : ℝ) (A B : ℝ × ℝ) :
    pairEdgeOccupation w A B = pairEdgeOccupation w B A :=
  Prod.ext (edgeOccupation_swap w A.1 B.1) (edgeOccupation_swap w A.2 B.2)

private theorem scalar_hard_reinsert (β d : ℝ) (ω : ArrivalConfiguration) (i : ℕ)
    (hfin : arrivalWeightedSum β d ω ≠ ∞) (hmarks : ∀ j, 0 < ω.2 j) :
    let r := scalarHardRoot β d ω
    let s := scalarHardRoot β d (eraseArrivalGap i ω.1, eraseSequence i ω.2)
    let w := Real.exp (-β * arrivalLength d ω.1 i)
    let B := ω.2 i
    (w*B*r = edgeOccupation w s B) ∧
      (r = fullEndpoint w s B) ∧
      ((1-w*B*r)*B = fullEndpoint w B s) := by
  dsimp only
  let B := ω.2 i
  let w := Real.exp (-β * arrivalLength d ω.1 i)
  let erased : ArrivalConfiguration := (eraseArrivalGap i ω.1, eraseSequence i ω.2)
  let S := (arrivalWeightedSum β d erased).toReal
  have hw : 0 < w := Real.exp_pos _
  have hB : 0 < B := hmarks i
  have hrestore : arrivalWeightedSum β d erased + ENNReal.ofReal (w*B) =
      arrivalWeightedSum β d ω := arrivalWeightedSum_erase_add β d ω i
  have hkeepLe : arrivalWeightedSum β d erased ≤ arrivalWeightedSum β d ω := by
    calc
      _ ≤ arrivalWeightedSum β d erased + ENNReal.ofReal (w*B) := le_self_add
      _ = _ := hrestore
  have hkeepFin : arrivalWeightedSum β d erased ≠ ∞ := ne_top_of_le_ne_top hfin hkeepLe
  have mark0 : 0 < erased.2 0 := by
    change 0 < eraseSequence i ω.2 0
    by_cases hi : 0 < i
    · rw [eraseSequence_apply_of_lt ω.2 hi]
      exact hmarks 0
    · rw [eraseSequence_apply_of_ge ω.2 (le_of_not_gt hi)]
      exact hmarks 1
  have hkeepPos : 0 < arrivalWeightedSum β d erased := by
    calc
      _ < ENNReal.ofReal (cavityTerm β d erased 0) :=
        ENNReal.ofReal_pos.mpr (mul_pos (Real.exp_pos _) mark0)
      _ ≤ _ := ENNReal.le_tsum (f := fun j => ENNReal.ofReal (cavityTerm β d erased j)) 0
  have hS : 0 < S := ENNReal.toReal_pos hkeepPos.ne' hkeepFin
  have hreal := congrArg ENNReal.toReal hrestore
  rw [ENNReal.toReal_add hkeepFin ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (mul_nonneg hw.le hB.le)] at hreal
  have hr : scalarHardRoot β d ω = (S+w*B)⁻¹ := by
    change (arrivalWeightedSum β d ω).toReal⁻¹ = _
    rw [← hreal]
  have hden : 0 < S+w*B := by positivity
  have hden₁ : 0 < 1+w*S⁻¹*B := by positivity
  have hden₂ : 0 < 1+w*B*S⁻¹ := by positivity
  change (w*B*scalarHardRoot β d ω = edgeOccupation w S⁻¹ B) ∧
    (scalarHardRoot β d ω = fullEndpoint w S⁻¹ B) ∧
    ((1-w*B*scalarHardRoot β d ω)*B = fullEndpoint w B S⁻¹)
  rw [hr]
  unfold edgeOccupation fullEndpoint
  refine ⟨?_, ?_, ?_⟩
  all_goals field_simp [hS.ne', hden.ne', hden₁.ne', hden₂.ne']
  all_goals ring

private theorem paired_hard_reinsert (β d : ℝ) (ω : PairedArrivalConfiguration)
    (i : ℕ) (hfin₁ : arrivalWeightedSum β d (firstArrivalConfiguration ω) ≠ ∞)
    (hfin₂ : arrivalWeightedSum β d (secondArrivalConfiguration ω) ≠ ∞)
    (hmarks : ∀ j, 0 < (ω.2 j).1 ∧ 0 < (ω.2 j).2) :
    let A := pairedHardRoot β d (eraseArrivalGap i ω.1, eraseSequence i ω.2)
    let B := ω.2 i
    let w := Real.exp (-β * arrivalLength d ω.1 i)
    (pairedHardOccupation β d ω i = pairEdgeOccupation w A B) ∧
      (pairedHardRoot β d ω = pairFullEndpoint w A B) ∧
      (pairedHardChild β d ω i = pairFullEndpoint w B A) := by
  have h₁ := scalar_hard_reinsert β d (firstArrivalConfiguration ω) i hfin₁
    (fun j => (hmarks j).1)
  have h₂ := scalar_hard_reinsert β d (secondArrivalConfiguration ω) i hfin₂
    (fun j => (hmarks j).2)
  exact ⟨Prod.ext h₁.1 h₂.1, Prod.ext h₁.2.1 h₂.2.1, Prod.ext h₁.2.2 h₂.2.2⟩

private theorem lintegral_pair_law_swap (τ : Measure ℝ) (ρ : Measure (ℝ × ℝ))
    [IsProbabilityMeasure ρ]
    {G G' : (ℝ × (ℝ × ℝ)) × (ℝ × ℝ) → ℝ≥0∞}
    (hG : Measurable G) (hG' : Measurable G')
    (h : ∀ x A B, G ((x,A),B) = G' ((x,B),A)) :
    (∫⁻ p, G p ∂(τ.prod ρ).prod ρ) = ∫⁻ p, G' p ∂(τ.prod ρ).prod ρ := by
  rw [lintegral_prod _ hG.aemeasurable, lintegral_prod _ hG'.aemeasurable,
    lintegral_prod _ (hG.lintegral_prod_right' (ν := ρ)).aemeasurable,
    lintegral_prod _ (hG'.lintegral_prod_right' (ν := ρ)).aemeasurable]
  apply lintegral_congr
  intro x
  have h1 : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => G ((x,p.1),p.2)) := by fun_prop
  have h2 : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => G' ((x,p.1),p.2)) := by fun_prop
  calc
    _ = ∫⁻ p, G ((x,p.1),p.2) ∂ρ.prod ρ := (lintegral_prod _ h1.aemeasurable).symm
    _ = ∫⁻ p, G' ((x,p.2),p.1) ∂ρ.prod ρ := lintegral_congr (fun p => h x p.1 p.2)
    _ = ∫⁻ p, G' ((x,p.1),p.2) ∂ρ.prod ρ :=
      (Measure.measurePreserving_swap (μ := ρ) (ν := ρ)).lintegral_comp h2
    _ = _ := lintegral_prod _ h2.aemeasurable

/-- Once a hard pair recursion has an invariant coupling, testing its common
occupations and full endpoint pairs is invariant under exchanging those
endpoints on the original marked arrival law. -/
theorem paired_hard_endpoint_exchange {β d : ℝ} (hd : 0 < d)
    (ρ : Measure (ℝ × ℝ)) [IsProbabilityMeasure ρ]
    (hfin : ∀ᵐ ω ∂markedArrivalSequenceLaw ρ,
      arrivalWeightedSum β d (firstArrivalConfiguration ω) ≠ ∞ ∧
      arrivalWeightedSum β d (secondArrivalConfiguration ω) ≠ ∞)
    (hmarks : ∀ᵐ ω ∂markedArrivalSequenceLaw ρ, ∀ j,
      0 < (ω.2 j).1 ∧ 0 < (ω.2 j).2)
    (hinv : (markedArrivalSequenceLaw ρ).map (pairedHardRoot β d) = ρ)
    (F : (ℝ × ℝ) × ((ℝ × ℝ) × (ℝ × ℝ)) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ ω, ∑' i, F (pairedHardOccupation β d ω i,
      (pairedHardRoot β d ω, pairedHardChild β d ω i)) ∂markedArrivalSequenceLaw ρ) =
    ∫⁻ ω, ∑' i, F (pairedHardOccupation β d ω i,
      (pairedHardChild β d ω i, pairedHardRoot β d ω)) ∂markedArrivalSequenceLaw ρ := by
  let P := markedArrivalSequenceLaw ρ
  let T := (intensity d).prod ρ
  let : IsProbabilityMeasure P := isProbabilityMeasure_markedArrivalSequenceLaw ρ
  let : SigmaFinite (intensity d) := sigmaFinite_intensity d
  let testLeft (p : (ℝ × (ℝ × ℝ)) × (ℝ × ℝ)) :=
    let w := Real.exp (-β*p.1.1)
    F (pairEdgeOccupation w p.2 p.1.2,
      (pairFullEndpoint w p.2 p.1.2, pairFullEndpoint w p.1.2 p.2))
  let testRight (p : (ℝ × (ℝ × ℝ)) × (ℝ × ℝ)) :=
    let w := Real.exp (-β*p.1.1)
    F (pairEdgeOccupation w p.2 p.1.2,
      (pairFullEndpoint w p.1.2 p.2, pairFullEndpoint w p.2 p.1.2))
  have htestLeft : Measurable testLeft := by
    dsimp [testLeft, pairEdgeOccupation, pairFullEndpoint, edgeOccupation, fullEndpoint]; fun_prop
  have htestRight : Measurable testRight := by
    dsimp [testRight, pairEdgeOccupation, pairFullEndpoint, edgeOccupation, fullEndpoint]; fun_prop
  have hlift (G : (ℝ × (ℝ × ℝ)) × (ℝ × ℝ) → ℝ≥0∞) (hG : Measurable G) :
      (∫⁻ p, G (p.1, pairedHardRoot β d p.2) ∂T.prod P) = ∫⁻ p, G p ∂T.prod ρ := by
    have hmap : (T.prod P).map (Prod.map id (pairedHardRoot β d)) = T.prod ρ := by
      have H : P.map (pairedHardRoot β d) = ρ := hinv
      rw [← Measure.map_prod_map _ _ measurable_id (measurable_pairedHardRoot β d),
        Measure.map_id, H]
    rw [← hmap, lintegral_map hG (measurable_id.prodMap (measurable_pairedHardRoot β d))]
    rfl
  let gL (p : (ℝ × (ℝ × ℝ)) × PairedArrivalConfiguration) :=
    testLeft (p.1, pairedHardRoot β d p.2)
  let gR (p : (ℝ × (ℝ × ℝ)) × PairedArrivalConfiguration) :=
    testRight (p.1, pairedHardRoot β d p.2)
  have hgL : Measurable gL := htestLeft.comp (measurable_id.prodMap (measurable_pairedHardRoot β d))
  have hgR : Measurable gR := htestRight.comp (measurable_id.prodMap (measurable_pairedHardRoot β d))
  have hL : (∫⁻ ω, ∑' i, F (pairedHardOccupation β d ω i,
      (pairedHardRoot β d ω, pairedHardChild β d ω i)) ∂P) = ∫⁻ p, testLeft p ∂T.prod ρ := by
    calc
      _ = ∫⁻ ω, ∑' i, gL ((arrivalLength d ω.1 i, ω.2 i),
          (eraseArrivalGap i ω.1, eraseSequence i ω.2)) ∂P := by
        apply lintegral_congr_ae
        filter_upwards [hfin, hmarks] with ω hω hm
        apply tsum_congr
        intro i
        obtain ⟨ho,hr,hc⟩ := paired_hard_reinsert β d ω i hω.1 hω.2 hm
        rw [ho,hr,hc]
      _ = ∫⁻ p, gL p ∂T.prod P := canonical_iid_marked_arrival_insertion hd ρ gL hgL
      _ = _ := hlift testLeft htestLeft
  have hR : (∫⁻ ω, ∑' i, F (pairedHardOccupation β d ω i,
      (pairedHardChild β d ω i, pairedHardRoot β d ω)) ∂P) = ∫⁻ p, testRight p ∂T.prod ρ := by
    calc
      _ = ∫⁻ ω, ∑' i, gR ((arrivalLength d ω.1 i, ω.2 i),
          (eraseArrivalGap i ω.1, eraseSequence i ω.2)) ∂P := by
        apply lintegral_congr_ae
        filter_upwards [hfin, hmarks] with ω hω hm
        apply tsum_congr
        intro i
        obtain ⟨ho,hr,hc⟩ := paired_hard_reinsert β d ω i hω.1 hω.2 hm
        rw [ho,hr,hc]
      _ = ∫⁻ p, gR p ∂T.prod P := canonical_iid_marked_arrival_insertion hd ρ gR hgR
      _ = _ := hlift testRight htestRight
  have swap (x : ℝ) (A B : ℝ × ℝ) : testLeft ((x,A),B) = testRight ((x,B),A) := by
    dsimp only [testLeft, testRight]
    rw [pairEdgeOccupation_swap]
  exact hL.trans ((lintegral_pair_law_swap _ _ htestLeft htestRight swap).trans hR.symm)

/-- The full log difference of a pair. -/
noncomputable def pairLogDifference (p : ℝ × ℝ) : ℝ :=
  Real.log p.1 - Real.log p.2

/-- Nonnegative exchange for the two signed weighted log differences used in
the simplex comparison. This supplies the exchange input to
`ae_occupations_eq_of_nonnegative_exchange`. -/
theorem paired_hard_log_difference_exchange {β d : ℝ} (hd : 0 < d)
    (ρ : Measure (ℝ × ℝ)) [IsProbabilityMeasure ρ]
    (hfin : ∀ᵐ ω ∂markedArrivalSequenceLaw ρ,
      arrivalWeightedSum β d (firstArrivalConfiguration ω) ≠ ∞ ∧
      arrivalWeightedSum β d (secondArrivalConfiguration ω) ≠ ∞)
    (hmarks : ∀ᵐ ω ∂markedArrivalSequenceLaw ρ, ∀ j,
      0 < (ω.2 j).1 ∧ 0 < (ω.2 j).2)
    (hinv : (markedArrivalSequenceLaw ρ).map (pairedHardRoot β d) = ρ)
    (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ ω, ∑' i, g (((pairedHardOccupation β d ω i).1 -
      (pairedHardOccupation β d ω i).2) * pairLogDifference (pairedHardChild β d ω i))
      ∂markedArrivalSequenceLaw ρ) =
    ∫⁻ ω, ∑' i, g (((pairedHardOccupation β d ω i).1 -
      (pairedHardOccupation β d ω i).2) * pairLogDifference (pairedHardRoot β d ω))
      ∂markedArrivalSequenceLaw ρ := by
  let F (p : (ℝ × ℝ) × ((ℝ × ℝ) × (ℝ × ℝ))) :=
    g ((p.1.1-p.1.2) * pairLogDifference p.2.2)
  have hF : Measurable F := by dsimp [F, pairLogDifference]; fun_prop
  exact paired_hard_endpoint_exchange hd ρ hfin hmarks hinv F hF


@[fun_prop] theorem measurable_pairedHardOccupation (β d : ℝ) (i : ℕ) :
    Measurable (fun ω => pairedHardOccupation β d ω i) := by
  unfold pairedHardOccupation arrivalLength
  fun_prop

@[fun_prop] theorem measurable_pairedHardChild (β d : ℝ) (i : ℕ) :
    Measurable (fun ω => pairedHardChild β d ω i) := by
  unfold pairedHardChild
  fun_prop

@[fun_prop] theorem measurable_pairLogDifference : Measurable pairLogDifference := by
  unfold pairLogDifference
  fun_prop

private theorem scalar_hard_root_and_occupation (β d : ℝ) (ω : ArrivalConfiguration)
    (hfin : arrivalWeightedSum β d ω ≠ ∞) (hmarks : ∀ i, 0 < ω.2 i) :
    0 < scalarHardRoot β d ω ∧
      HasSum (fun i => cavityTerm β d ω i * scalarHardRoot β d ω) 1 ∧
      (∀ i, 0 < cavityTerm β d ω i * scalarHardRoot β d ω) := by
  let f := cavityTerm β d ω
  have hpos (i : ℕ) : 0 < f i := mul_pos (Real.exp_pos _) (hmarks i)
  have hnorm : (∑' i, ‖f i‖ₑ) ≠ ∞ := by
    have hn (i : ℕ) : ‖f i‖ₑ = ENNReal.ofReal (f i) := Real.enorm_eq_ofReal (hpos i).le
    simp_rw [hn]
    exact hfin
  have hf : Summable f := (tsum_enorm_ne_top_iff_summable_norm.mp hnorm).of_norm
  have hs : 0 < ∑' i, f i :=
    hf.tsum_pos (fun i => (hpos i).le) 0 (hpos 0)
  have hr : scalarHardRoot β d ω = (∑' i, f i)⁻¹ := by
    unfold scalarHardRoot arrivalWeightedSum
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => (hpos i).le) hf,
      ENNReal.toReal_ofReal hs.le]
  have hroot : 0 < scalarHardRoot β d ω := by rw [hr]; exact inv_pos.mpr hs
  refine ⟨hroot, ?_, fun i => mul_pos (hpos i) hroot⟩
  have h := hf.hasSum.mul_right (scalarHardRoot β d ω)
  rw [hr, mul_inv_cancel₀ hs.ne'] at h
  simpa only [hr] using h

private theorem scalar_erased_hard_root_pos (β d : ℝ) (ω : ArrivalConfiguration)
    (i : ℕ) (hfin : arrivalWeightedSum β d ω ≠ ∞) (hmarks : ∀ j, 0 < ω.2 j) :
    0 < scalarHardRoot β d (eraseArrivalGap i ω.1, eraseSequence i ω.2) := by
  let e : ArrivalConfiguration := (eraseArrivalGap i ω.1, eraseSequence i ω.2)
  have le : arrivalWeightedSum β d e ≤ arrivalWeightedSum β d ω := by
    change arrivalWeightedSum β d (eraseArrivalGap i ω.1, eraseSequence i ω.2) ≤ _
    rw [← arrivalWeightedSum_erase_add β d ω i]
    exact le_self_add
  apply (scalar_hard_root_and_occupation β d e (ne_top_of_le_ne_top hfin le) ?_).1
  intro j
  change 0 < eraseSequence i ω.2 j
  by_cases hj : j < i
  · rw [eraseSequence_apply_of_lt ω.2 hj]
    exact hmarks j
  · rw [eraseSequence_apply_of_ge ω.2 (le_of_not_gt hj)]
    exact hmarks (j+1)

/-- The simplex comparison forces the coupled edge choices to coincide under
an invariant hard coupling with finite outgoing sums and an integrable log
difference. -/
theorem ae_paired_hard_occupations_eq {β d : ℝ} (hd : 0 < d)
    (ρ : Measure (ℝ × ℝ)) [IsProbabilityMeasure ρ]
    (hfin : ∀ᵐ ω ∂markedArrivalSequenceLaw ρ,
      arrivalWeightedSum β d (firstArrivalConfiguration ω) ≠ ∞ ∧
      arrivalWeightedSum β d (secondArrivalConfiguration ω) ≠ ∞)
    (hmarks : ∀ᵐ ω ∂markedArrivalSequenceLaw ρ, ∀ j,
      0 < (ω.2 j).1 ∧ 0 < (ω.2 j).2)
    (hinv : (markedArrivalSequenceLaw ρ).map (pairedHardRoot β d) = ρ)
    (hlog : Integrable pairLogDifference ρ) :
    ∀ᵐ ω ∂markedArrivalSequenceLaw ρ, ∀ i,
      (pairedHardOccupation β d ω i).1 = (pairedHardOccupation β d ω i).2 := by
  let P := markedArrivalSequenceLaw ρ
  let a (ω : PairedArrivalConfiguration) (i : ℕ) := (pairedHardOccupation β d ω i).1
  let b (ω : PairedArrivalConfiguration) (i : ℕ) := (pairedHardOccupation β d ω i).2
  let Δ (ω : PairedArrivalConfiguration) (i : ℕ) := pairLogDifference (pairedHardChild β d ω i)
  let D (ω : PairedArrivalConfiguration) := pairLogDifference (pairedHardRoot β d ω)
  have hprob : ∀ᵐ ω ∂P, HasSum (a ω) 1 ∧ HasSum (b ω) 1 ∧
      (∀ i, 0 < a ω i) ∧ (∀ i, 0 < b ω i) := by
    filter_upwards [hfin,hmarks] with ω hω hm
    have h₁ := scalar_hard_root_and_occupation β d (firstArrivalConfiguration ω)
      hω.1 (fun j => (hm j).1)
    have h₂ := scalar_hard_root_and_occupation β d (secondArrivalConfiguration ω)
      hω.2 (fun j => (hm j).2)
    exact ⟨h₁.2.1, h₂.2.1, h₁.2.2, h₂.2.2⟩
  have hfactor : ∀ᵐ ω ∂P, ∀ i, simplexTerm (a ω) (b ω) i = (a ω i-b ω i) * (D ω + Δ ω i) := by
    filter_upwards [hfin,hmarks] with ω hω hm
    intro i
    obtain ⟨ho,hr,hc⟩ := paired_hard_reinsert β d ω i hω.1 hω.2 hm
    have h₁ := scalar_erased_hard_root_pos β d (firstArrivalConfiguration ω) i hω.1
      (fun j => (hm j).1)
    have h₂ := scalar_erased_hard_root_pos β d (secondArrivalConfiguration ω) i hω.2
      (fun j => (hm j).2)
    let A := pairedHardRoot β d (eraseArrivalGap i ω.1, eraseSequence i ω.2)
    let B := ω.2 i
    let W := Real.exp (-β * arrivalLength d ω.1 i)
    have hA₁ : 0 < A.1 := h₁
    have hA₂ : 0 < A.2 := h₂
    have H := occupation_log_ratio (w := W) (Real.exp_pos _) hA₁ (hm i).1 hA₂ (hm i).2
    unfold simplexTerm a b D Δ
    rw [ho,hr,hc]
    exact congrArg (fun x => (edgeOccupation W A.1 B.1 - edgeOccupation W A.2 B.2) * x) H
  have hD : Integrable D P := by
    have hI : Integrable pairLogDifference (P.map (pairedHardRoot β d)) := by
      change Integrable pairLogDifference ((markedArrivalSequenceLaw ρ).map (pairedHardRoot β d))
      rwa [hinv]
    exact hI.comp_measurable (measurable_pairedHardRoot β d)
  have hchild (i : ℕ) : AEStronglyMeasurable (fun ω => (a ω i - b ω i) * Δ ω i) P := by
    apply Measurable.aestronglyMeasurable
    dsimp [a,b,Δ]
    fun_prop
  have hroot (i : ℕ) : AEStronglyMeasurable (fun ω => (a ω i - b ω i) * D ω) P := by
    apply Measurable.aestronglyMeasurable
    dsimp [a,b,D]
    fun_prop
  have heq := ae_occupations_eq_of_nonnegative_exchange hprob hfactor hD hchild hroot
    (fun g hg => paired_hard_log_difference_exchange hd ρ hfin hmarks hinv g hg)
  exact heq.mono (fun _ h i => congrFun h i)


/-- An invariant hard coupling with finite outgoing sums, positive marks and a
square-integrable log difference has equal marginals. -/
theorem hard_invariant_coupling_marginals_eq {β d : ℝ} (hd : 0 < d)
    (ρ : Measure (ℝ × ℝ)) [IsProbabilityMeasure ρ]
    (hfin : ∀ᵐ ω ∂markedArrivalSequenceLaw ρ,
      arrivalWeightedSum β d (firstArrivalConfiguration ω) ≠ ∞ ∧
      arrivalWeightedSum β d (secondArrivalConfiguration ω) ≠ ∞)
    (hmarks : ∀ᵐ ω ∂markedArrivalSequenceLaw ρ, ∀ j,
      0 < (ω.2 j).1 ∧ 0 < (ω.2 j).2)
    (hinv : (markedArrivalSequenceLaw ρ).map (pairedHardRoot β d) = ρ)
    (hlog : MemLp pairLogDifference 2 ρ) :
    ρ.map Prod.fst = ρ.map Prod.snd := by
  let P := markedArrivalSequenceLaw ρ
  let M := Measure.infinitePi (fun _ : ℕ => ρ)
  let : IsProbabilityMeasure P := isProbabilityMeasure_markedArrivalSequenceLaw ρ
  let : IsProbabilityMeasure exponentialSpacings := isProbabilityMeasure_exponentialSpacings
  let Δ₀ := fun ω => pairLogDifference (pairedHardRoot β d ω)
  let C (i : ℕ) (ω : PairedArrivalConfiguration) := ω.2 i
  let D (i : ℕ) (ω : PairedArrivalConfiguration) := pairLogDifference (C i ω)
  have hC (i : ℕ) : Measurable (C i) := (measurable_pi_apply i).comp measurable_snd
  have hD (i : ℕ) : Measurable (D i) := measurable_pairLogDifference.comp (hC i)
  have hΔ₀ : Measurable Δ₀ := measurable_pairLogDifference.comp (measurable_pairedHardRoot β d)
  have hCp (i : ℕ) : MeasurePreserving (C i) P ρ :=
    (measurePreserving_eval_infinitePi (fun _ : ℕ => ρ) i).comp
      (measurePreserving_snd (μ := exponentialSpacings) (ν := M))
  have hOcc := ae_paired_hard_occupations_eq hd ρ hfin hmarks hinv
    (hlog.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))
  have hRootPos : ∀ᵐ ω ∂P, 0 < (pairedHardRoot β d ω).1 ∧ 0 < (pairedHardRoot β d ω).2 := by
    filter_upwards [hfin,hmarks] with ω hf hm
    exact ⟨(scalar_hard_root_and_occupation β d (firstArrivalConfiguration ω) hf.1
      (fun i => (hm i).1)).1,
      (scalar_hard_root_and_occupation β d (secondArrivalConfiguration ω) hf.2
      (fun i => (hm i).2)).1⟩
  have hcancel (i : ℕ) : ∀ᵐ ω ∂P, D i ω = -Δ₀ ω := by
    filter_upwards [hOcc, hmarks, hRootPos] with ω hop hm hr
    have h := log_differences_cancel (w := Real.exp (-β * arrivalLength d ω.1 i))
      (Real.exp_pos _) (hm i).1 hr.1 (hm i).2 hr.2 (hop i)
    change pairLogDifference (C i ω) = -pairLogDifference (pairedHardRoot β d ω)
    unfold pairLogDifference C
    linarith
  have hind₀ : IndepFun (C 0) (C 1) P := by
    apply (indepFun_iff_map_prod_eq_prod_map_map (hC 0).aemeasurable (hC 1).aemeasurable).mpr
    rw [(hCp 0).map_eq, (hCp 1).map_eq]
    change P.map ((fun m : ℕ → ℝ × ℝ => (m 0,m 1)) ∘ Prod.snd) = ρ.prod ρ
    have hs : P.map Prod.snd = M :=
      (measurePreserving_snd (μ := exponentialSpacings) (ν := M)).map_eq
    rw [← Measure.map_map (by fun_prop) measurable_snd, hs]
    exact Measure.infinitePi_map_eval_prod (P := fun _ : ℕ => ρ) (by decide : (0:ℕ) ≠ 1)
  have hind : IndepFun (D 0) (D 1) P :=
    hind₀.comp measurable_pairLogDifference measurable_pairLogDifference
  have hID : IdentDistrib Δ₀ (D 0) P P := by
    refine ⟨hΔ₀.aemeasurable, (hD 0).aemeasurable, ?_⟩
    change P.map (pairLogDifference ∘ pairedHardRoot β d) =
      P.map (pairLogDifference ∘ C 0)
    rw [← Measure.map_map measurable_pairLogDifference (measurable_pairedHardRoot β d),
      ← Measure.map_map measurable_pairLogDifference (hC 0),
      show P.map (pairedHardRoot β d) = ρ from hinv, (hCp 0).map_eq]
  have hzero : ∀ᵐ ω ∂P, Δ₀ ω = 0 :=
    ae_root_log_difference_zero (hlog.comp_measurePreserving (hCp 0))
      (hlog.comp_measurePreserving (hCp 1)) hind hID (hcancel 0) (hcancel 1)
  have eqMap := map_eq_of_ae_log_difference_zero hRootPos hzero
  rw [← (show P.map (pairedHardRoot β d) = ρ from hinv),
    Measure.map_map measurable_fst (measurable_pairedHardRoot β d),
    Measure.map_map measurable_snd (measurable_pairedHardRoot β d)]
  exact eqMap

end Certificate

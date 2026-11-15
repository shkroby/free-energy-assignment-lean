import Certificate.ArrivalHardExchange

/-!
# Comparing cavity laws through an invariant coupling

The marginal recursion gives finite outgoing sums, and the marginal support
condition gives positive sampled marks. These are the conditions used by the
endpoint comparison on the marked arrival space.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Certificate

/-- Each indexed mark on the canonical arrival sequence has the mark law. -/
theorem markedArrival_eval_preserving {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsProbabilityMeasure μ] (i : ℕ) :
    MeasurePreserving (fun ω : (ℕ → ℝ) × (ℕ → Y) => ω.2 i)
      (markedArrivalSequenceLaw μ) μ := by
  let : IsProbabilityMeasure exponentialSpacings := isProbabilityMeasure_exponentialSpacings
  exact (measurePreserving_eval_infinitePi (fun _ : ℕ => μ) i).comp
    (measurePreserving_snd (μ := exponentialSpacings)
      (ν := Measure.infinitePi (fun _ : ℕ => μ)))

/-- Projecting each iid mark preserves the projected canonical marked law. -/
theorem markedArrival_projection (ρ : Measure (ℝ × ℝ)) [IsProbabilityMeasure ρ]
    (f : ℝ × ℝ → ℝ) (hf : Measurable f) :
    MeasurePreserving (fun ω : PairedArrivalConfiguration => (ω.1,fun i => f (ω.2 i)))
      (markedArrivalSequenceLaw ρ) (markedSpacings (ρ.map f)) := by
  let : IsProbabilityMeasure exponentialSpacings := isProbabilityMeasure_exponentialSpacings
  let F := fun marks : ℕ → ℝ × ℝ => fun i => f (marks i)
  have hF : Measurable F := measurable_pi_lambda _ fun i => hf.comp (measurable_pi_apply i)
  refine ⟨measurable_id.prodMap hF, ?_⟩
  change (exponentialSpacings.prod (Measure.infinitePi (fun _ : ℕ => ρ))).map
      (Prod.map id F) = exponentialSpacings.prod (Measure.infinitePi (fun _ : ℕ => ρ.map f))
  rw [← Measure.map_prod_map _ _ measurable_id hF, Measure.map_id]
  have H : (Measure.infinitePi (fun _ : ℕ => ρ)).map F =
      Measure.infinitePi (fun _ : ℕ => ρ.map f) :=
    Measure.infinitePi_map_pi (fun _ : ℕ => ρ) (fun _ => hf)
  rw [H]

private theorem ae_cavityLaw_pos {β d : ℝ} {μ : Measure ℝ} (h : IsCavityLaw β d μ) :
    ∀ᵐ x ∂μ, 0 < x := by
  let : IsProbabilityMeasure μ := h.1
  exact (mem_ae_iff_prob_eq_one (measurableSet_Ioi (a := (0:ℝ)))).mpr h.2.1

/-- For a cavity law, the extended-sum output at zero fugacity agrees with
the original reciprocal of the real series almost surely. -/
theorem ae_cavityMap_eq_arrivalSoftOutput_zero {β d : ℝ} {μ : Measure ℝ}
    (h : IsCavityLaw β d μ) :
    cavityMap β d =ᵐ[markedSpacings μ] arrivalSoftOutput β d 0 := by
  let : IsProbabilityMeasure μ := h.1
  have hpos : ∀ᵐ ω ∂markedSpacings μ, ∀ i, 0 < ω.2 i := by
    apply ae_all_iff.mpr
    intro i
    exact (markedArrival_eval_preserving μ i).quasiMeasurePreserving.tendsto_ae.eventually
      (ae_cavityLaw_pos h)
  filter_upwards [h.2.2.1, hpos] with ω hω hp
  have hnonneg (i : ℕ) : 0 ≤ cavityTerm β d ω i :=
    mul_nonneg (Real.exp_nonneg _) (hp i).le
  have hsum : arrivalWeightedSum β d ω = ENNReal.ofReal (∑' i, cavityTerm β d ω i) :=
    (ENNReal.ofReal_tsum_of_nonneg hnonneg hω.1).symm
  change (∑' i, cavityTerm β d ω i)⁻¹ = (0 + (arrivalWeightedSum β d ω).toReal)⁻¹
  rw [zero_add, hsum, ENNReal.toReal_ofReal hω.2.le]

/-- The zero-fugacity output map pushes a cavity law's marked configuration to
that same law. -/
theorem map_arrivalSoftOutput_zero_of_IsCavityLaw {β d : ℝ} {μ : Measure ℝ}
    (h : IsCavityLaw β d μ) :
    (markedSpacings μ).map (arrivalSoftOutput β d 0) = μ :=
  (Measure.map_congr (ae_cavityMap_eq_arrivalSoftOutput_zero h).symm).trans h.2.2.2

/-- Under an invariant coupling between two hard cavity laws with finite log
second moments, the two marginal laws coincide. -/
theorem hard_cavity_law_marginals_eq_of_invariant {β d : ℝ} (hd : 0 < d)
    (ρ : Measure (ℝ × ℝ)) [IsProbabilityMeasure ρ]
    (h₁ : IsCavityLaw β d (ρ.map Prod.fst)) (h₂ : IsCavityLaw β d (ρ.map Prod.snd))
    (hinv : (markedArrivalSequenceLaw ρ).map (pairedHardRoot β d) = ρ)
    (hlog₁ : MemLp Real.log 2 (ρ.map Prod.fst))
    (hlog₂ : MemLp Real.log 2 (ρ.map Prod.snd)) :
    ρ.map Prod.fst = ρ.map Prod.snd := by
  let P := markedArrivalSequenceLaw ρ
  have hProj₁ : MeasurePreserving Prod.fst ρ (ρ.map Prod.fst) := ⟨measurable_fst,rfl⟩
  have hProj₂ : MeasurePreserving Prod.snd ρ (ρ.map Prod.snd) := ⟨measurable_snd,rfl⟩
  have hρ : ∀ᵐ x ∂ρ, 0 < x.1 ∧ 0 < x.2 :=
    (hProj₁.quasiMeasurePreserving.tendsto_ae.eventually (ae_cavityLaw_pos h₁)).and
      (hProj₂.quasiMeasurePreserving.tendsto_ae.eventually (ae_cavityLaw_pos h₂))
  have hmarks : ∀ᵐ ω ∂P, ∀ j, 0 < (ω.2 j).1 ∧ 0 < (ω.2 j).2 := by
    apply ae_all_iff.mpr
    intro i
    exact (markedArrival_eval_preserving ρ i).quasiMeasurePreserving.tendsto_ae.eventually hρ
  have hs₁ : ∀ᵐ ω ∂P, Summable (cavityTerm β d (firstArrivalConfiguration ω)) :=
    (markedArrival_projection ρ Prod.fst measurable_fst).quasiMeasurePreserving.tendsto_ae.eventually
      (h₁.2.2.1.mono fun _ h => h.1)
  have hs₂ : ∀ᵐ ω ∂P, Summable (cavityTerm β d (secondArrivalConfiguration ω)) :=
    (markedArrival_projection ρ Prod.snd measurable_snd).quasiMeasurePreserving.tendsto_ae.eventually
      (h₂.2.2.1.mono fun _ h => h.1)
  have hfin : ∀ᵐ ω ∂P,
      arrivalWeightedSum β d (firstArrivalConfiguration ω) ≠ ∞ ∧
      arrivalWeightedSum β d (secondArrivalConfiguration ω) ≠ ∞ := by
    filter_upwards [hs₁,hs₂,hmarks] with ω hω₁ hω₂ hp
    have he₁ : arrivalWeightedSum β d (firstArrivalConfiguration ω) =
        ENNReal.ofReal (∑' i, cavityTerm β d (firstArrivalConfiguration ω) i) :=
      (ENNReal.ofReal_tsum_of_nonneg
        (fun i => mul_nonneg (Real.exp_nonneg _) (hp i).1.le) hω₁).symm
    have he₂ : arrivalWeightedSum β d (secondArrivalConfiguration ω) =
        ENNReal.ofReal (∑' i, cavityTerm β d (secondArrivalConfiguration ω) i) :=
      (ENNReal.ofReal_tsum_of_nonneg
        (fun i => mul_nonneg (Real.exp_nonneg _) (hp i).2.le) hω₂).symm
    exact ⟨he₁ ▸ ENNReal.ofReal_ne_top, he₂ ▸ ENNReal.ofReal_ne_top⟩
  have hlog : MemLp pairLogDifference 2 ρ :=
    (hlog₁.comp_measurePreserving hProj₁).sub (hlog₂.comp_measurePreserving hProj₂)
  exact hard_invariant_coupling_marginals_eq hd ρ hfin hmarks hinv hlog

end Certificate

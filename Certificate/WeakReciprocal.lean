import Certificate.WeakTruncation
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Continuous mapping at a positive weak limit

A measurable function continuous on the positive half-line preserves weak
convergence to a positive limit. Continuous clipping away from zero permits
reciprocation and taking logarithms.
-/

open Filter MeasureTheory Set
open scoped Topology ENNReal

namespace Certificate

/-- A measurable function continuous on the positive half-line preserves
convergence in distribution when the limit is positive almost surely. -/
theorem tendstoInDistribution_comp_of_ae_pos
    {Ω Ψ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ]
    {P : ℕ → Measure Ω} [∀ n, IsProbabilityMeasure (P n)]
    {Q : Measure Ψ} [IsProbabilityMeasure Q]
    {X : ℕ → Ω → ℝ} {Y : Ψ → ℝ}
    {f : ℝ → ℝ} (hf : Measurable f) (hfcont : ContinuousOn f (Ioi 0))
    (hX : ∀ n, Measurable (X n)) (hY : Measurable Y)
    (h : TendstoInDistribution X atTop Y P Q)
    (hpos : ∀ᵐ ω ∂Q, 0 < Y ω) :
    TendstoInDistribution (fun n ↦ f ∘ X n) atTop (f ∘ Y) P Q := by
  let r (R : ℕ) : ℝ := 1 / ((R : ℝ) + 1)
  have hr (R : ℕ) : 0 < r R := by dsimp [r]; positivity
  have hr₀ : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hranti : Antitone r := by
    intro a b hab
    apply one_div_le_one_div_of_le (by positivity : 0 < (a : ℝ) + 1)
    exact add_le_add_left (Nat.cast_le.mpr hab) 1
  let cut (R : ℕ) (x : ℝ) : ℝ := f (max (r R) x)
  have hcont (R : ℕ) : Continuous (cut R) :=
    hfcont.comp_continuous (continuous_const.max continuous_id)
      (fun x ↦ (hr R).trans_le (le_max_left _ _))
  apply tendstoInDistribution_of_uniform_truncations
    (Xcut := fun R n ↦ cut R ∘ X n) (Ycut := fun R ↦ cut R ∘ Y)
    (fun n ↦ hf.comp (hX n)) (hf.comp hY) (fun R n ↦ (hcont R).measurable.comp (hX n))
    (fun R ↦ (hcont R).measurable.comp hY) (fun R ↦ h.continuous_comp (hcont R))
  intro δ hδ η hη
  let L : ProbabilityMeasure ℝ := ⟨Q.map Y, Measure.isProbabilityMeasure_map hY.aemeasurable⟩
  let A (R : ℕ) : Set ℝ := Iic (r R)
  have hInter : (⋂ R, A R) = Iic (0 : ℝ) := by
    ext x
    constructor
    · intro hx
      exact ge_of_tendsto hr₀ (.of_forall fun R ↦ mem_iInter.mp hx R)
    · intro hx
      exact mem_iInter.mpr fun R ↦ show x ≤ r R from hx.trans (hr R).le
  have hZero : (L : Measure ℝ) (Iic 0) = 0 := by
    rw [show (L : Measure ℝ) = Q.map Y by rfl, Measure.map_apply hY measurableSet_Iic]
    apply measure_eq_zero_iff_ae_notMem.mpr
    exact hpos.mono fun _ hx ↦ not_le_of_gt hx
  have hRlim : Tendsto (fun R ↦ (L : Measure ℝ) (A R)) atTop (𝓝 0) := by
    have ht := tendsto_measure_iInter_atTop (μ := (L : Measure ℝ)) (s := A)
      (fun _ ↦ measurableSet_Iic.nullMeasurableSet)
      (show Antitone A from fun a b hab ↦ Iic_subset_Iic.mpr (hranti hab))
      ⟨0, measure_ne_top _ _⟩
    change Tendsto ((L : Measure ℝ) ∘ A) atTop (𝓝 0)
    rwa [hInter, hZero] at ht
  obtain ⟨R, hR⟩ := (hRlim.eventually (Iio_mem_nhds
    (ENNReal.ofReal_pos.mpr hη))).exists
  refine ⟨R, ?_, ?_⟩
  · have hlimsup := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto h.tendsto
      (F := A R) isClosed_Iic
    have hN := eventually_lt_of_limsup_lt (hlimsup.trans_lt hR)
    filter_upwards [hN] with n hn
    have hsub : {ω : Ω | δ ≤ |f (X n ω) - cut R (X n ω)|} ⊆ X n ⁻¹' A R := by
      intro ω hω
      by_contra hnot
      have hge : r R ≤ X n ω := (lt_of_not_ge (show ¬ X n ω ≤ r R from hnot)).le
      have he : cut R (X n ω) = f (X n ω) := by simp [cut, max_eq_right hge]
      exact (not_le_of_gt hδ) (by simpa only [he, sub_self, abs_zero, mem_ofPred_eq] using hω)
    have hmajor : P n (X n ⁻¹' A R) ≤ ENNReal.ofReal η := by
      rw [← Measure.map_apply (hX n) measurableSet_Iic]
      exact hn.le
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top
      ((measure_mono hsub).trans hmajor)).trans_eq (ENNReal.toReal_ofReal hη.le)
  · have hsub : {ω : Ψ | δ ≤ |cut R (Y ω) - f (Y ω)|} ⊆ Y ⁻¹' A R := by
      intro ω hω
      by_contra hnot
      have hge : r R ≤ Y ω := (lt_of_not_ge (show ¬ Y ω ≤ r R from hnot)).le
      have he : cut R (Y ω) = f (Y ω) := by simp [cut, max_eq_right hge]
      exact (not_le_of_gt hδ) (by simpa only [he, sub_self, abs_zero, mem_ofPred_eq] using hω)
    have hmajor : Q (Y ⁻¹' A R) ≤ ENNReal.ofReal η := by
      rw [← Measure.map_apply hY measurableSet_Iic]
      exact hR.le
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top
      ((measure_mono hsub).trans hmajor)).trans_eq (ENNReal.toReal_ofReal hη.le)

/-- Weak convergence to a law supported in the positive half-line allows
application of any measurable function continuous on that half-line. -/
theorem tendsto_probabilityMeasure_map_of_ae_pos
    {μ : ℕ → ProbabilityMeasure ℝ} {ν : ProbabilityMeasure ℝ}
    (h : Tendsto μ atTop (𝓝 ν)) (hν : ∀ᵐ x ∂(ν : Measure ℝ), 0 < x)
    {f : ℝ → ℝ} (hf : Measurable f) (hfcont : ContinuousOn f (Ioi 0)) :
    Tendsto (fun n => (μ n).map hf.aemeasurable) atTop (𝓝 (ν.map hf.aemeasurable)) := by
  have hId : TendstoInDistribution (fun _ : ℕ => (id : ℝ → ℝ)) atTop id
      (fun n => (μ n : Measure ℝ)) (ν : Measure ℝ) := by
    refine ⟨fun _ => measurable_id.aemeasurable, measurable_id.aemeasurable, ?_⟩
    have hmap (q : ProbabilityMeasure ℝ) :
        (⟨(q : Measure ℝ).map id,
          Measure.isProbabilityMeasure_map measurable_id.aemeasurable⟩ : ProbabilityMeasure ℝ) = q :=
      Subtype.ext Measure.map_id
    simpa only [hmap] using h
  exact (tendstoInDistribution_comp_of_ae_pos hf hfcont (fun _ => measurable_id)
    measurable_id hId hν).tendsto

/-- A weak limit which is strictly positive permits inversion. -/
theorem tendstoInDistribution_inv_of_ae_pos
    {Ω Ψ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ]
    {P : ℕ → Measure Ω} [∀ n, IsProbabilityMeasure (P n)]
    {Q : Measure Ψ} [IsProbabilityMeasure Q]
    {X : ℕ → Ω → ℝ} {Y : Ψ → ℝ}
    (hX : ∀ n, Measurable (X n)) (hY : Measurable Y)
    (h : TendstoInDistribution X atTop Y P Q)
    (hpos : ∀ᵐ ω ∂Q, 0 < Y ω) :
    TendstoInDistribution (fun n ω ↦ (X n ω)⁻¹) atTop (fun ω ↦ (Y ω)⁻¹) P Q :=
  tendstoInDistribution_comp_of_ae_pos measurable_inv
    (continuousOn_inv₀.mono (fun _ hx => ne_of_gt hx)) hX hY h hpos

end Certificate

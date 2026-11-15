import Certificate.CanonicalBethePressure
import Certificate.ArrivalSoftMarkedExchange

/-! Marked endpoint exchange on the same canonical tree used for differentiation. -/

open Filter MeasureTheory Set
open scoped ENNReal

namespace Certificate.CanonicalTree

private noncomputable def occupiedChild (β d t : ℝ) (ω : Environment) (i : ℕ) : ℝ :=
  weight β d ω [] i * lower β d (Real.exp t) (child [] i) ω * lower β d (Real.exp t) [] ω

private noncomputable def occupiedEdge (β d t : ℝ) (p : EdgeSample) : ℝ :=
  edgeOccupation (Real.exp (-β * p.1)) (lower β d (Real.exp t) [] p.2.1)
    (lower β d (Real.exp t) [] p.2.2)

private theorem measurable_occupiedChild (β d t : ℝ) (i : ℕ) :
    Measurable (fun ω => occupiedChild β d t ω i) :=
  ((measurable_weight β d [] i).mul (measurable_lower β d (Real.exp t) (child [] i))).mul
    (measurable_lower β d (Real.exp t) [])

private theorem measurable_occupiedEdge (β d t : ℝ) : Measurable (occupiedEdge β d t) := by
  have ha := (measurable_lower β d (Real.exp t) []).comp
    (show Measurable (fun p : EdgeSample => p.2.1) from measurable_fst.comp measurable_snd)
  have hb := (measurable_lower β d (Real.exp t) []).comp
    (show Measurable (fun p : EdgeSample => p.2.2) from measurable_snd.comp measurable_snd)
  have hw : Measurable (fun p : EdgeSample => Real.exp (-β * p.1)) :=
    Real.measurable_exp.comp ((measurable_fst : Measurable (Prod.fst : EdgeSample → ℝ)).const_mul (-β))
  have h := (hw.mul ha).mul hb
  unfold occupiedEdge edgeOccupation
  exact h.div (measurable_const.add h)

private theorem measurable_logMessageDerivative_at (β d t : ℝ) (v : Vertex) :
    Measurable (fun ω : Environment => logMessageDerivative β d v t ω) := by
  have h : Measurable (Function.uncurry (logMessageDerivative β d v)) :=
    measurable_logMessageDerivative β d v
  exact h.of_uncurry_left (x := t)

private theorem measurable_softMarkedOccupation (β d z : ℝ) (i : ℕ) :
    Measurable (fun ω => softMarkedOccupation β d z ω i) := by
  have hL : Measurable (fun e : Spacings => arrivalLength d e i) := by
    unfold arrivalLength
    fun_prop
  unfold softMarkedOccupation
  exact ((Real.measurable_exp.comp ((hL.comp measurable_fst).const_mul (-β))).mul
    (measurable_fst.comp ((measurable_pi_apply i).comp measurable_snd))).mul
    ((measurable_arrivalSoftOutput β d z).comp measurable_firstArrivalConfiguration)

/-- A nonnegative test of the log-message derivative on an occupied child edge
agrees in expectation with the same test at one independent Bethe endpoint. -/
private theorem lintegral_canonical_occupiedDerivative {β d : ℝ} (hβ : 0 < β) (hd : 0 < d) (t : ℝ)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, ∑' i, ENNReal.ofReal (occupiedChild β d t ω i) *
        f (logMessageDerivative β d (child [] i) t ω) ∂law) =
      ∫⁻ p, ENNReal.ofReal (occupiedEdge β d t p) *
        f (logMessageDerivative β d [] t p.2.2) ∂betheEdgeMeasure d := by
  let : IsProbabilityMeasure law := isProbabilityMeasure_law
  let : SigmaFinite (intensity d) := sigmaFinite_intensity d
  let z := Real.exp t
  let H := lower β d z []
  let D := logMessageDerivative β d [] t
  let mark (ω : Environment) := (H ω, D ω)
  let ρ := law.map mark
  let μ := law.map H
  let data (ω : Environment) : PairedArrivalConfiguration := (ω [], fun i => mark (branch i ω))
  let test : ℝ × (ℝ × ℝ) → ℝ≥0∞ := fun p => f p.2.2
  have hH : Measurable H := measurable_lower β d z []
  have hD : Measurable D := measurable_logMessageDerivative_at β d t []
  have hm : Measurable mark := hH.prodMk hD
  let : IsProbabilityMeasure ρ := Measure.isProbabilityMeasure_map hm.aemeasurable
  let : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map hH.aemeasurable
  have hdata : Measurable data := (measurable_pi_apply []).prodMk
    (measurable_pi_iff.mpr fun i => hm.comp (measurable_branch i))
  have hP : law.map data = markedArrivalSequenceLaw ρ := map_root_marks hm
  have hproj : ρ.map Prod.fst = μ := (Measure.map_map measurable_fst hm).trans rfl
  have hLaw : (markedSpacings μ).map (arrivalSoftOutput β d z) = μ := by
    have h := (crossed_arrival_laws hβ hd (Real.exp_pos t)).2
    rw [← Measure.map_congr (ae_lower_eq_upper hβ hd (Real.exp_pos t))] at h
    exact h
  have hmarks : ∀ᵐ x ∂μ, x ∈ Icc 0 z⁻¹ := by
    apply (ae_map_iff hH.aemeasurable measurableSet_Icc).2
    exact (ae_lower_logFugacity_recursion hβ hd).mono fun _ h => ⟨(h t []).1.le, (h t []).2.1⟩
  have hfin : ∀ᵐ ω ∂markedSpacings μ, arrivalWeightedSum β d ω ≠ ∞ :=
    (ae_arrivalWeightedSum_eq_ofReal_tsum hd hβ μ hmarks).mono fun _ h => by
      rw [h]
      exact ENNReal.ofReal_ne_top
  have hmark : ∀ᵐ ω ∂markedArrivalSequenceLaw ρ, ∀ i, 0 ≤ (ω.2 i).1 := by
    rw [← hP]
    apply (ae_map_iff hdata.aemeasurable ?_).2
    · exact (ae_lower_logFugacity_recursion hβ hd).mono fun ω h i => by
        change 0 ≤ H (branch i ω)
        simpa only [H, lower_branch, child, List.nil_append] using (h t (child [] i)).1.le
    · simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun i => measurableSet_le measurable_const
        (measurable_fst.comp ((measurable_pi_apply i).comp measurable_snd))
  have ht : Measurable test := hf.comp (measurable_snd.comp measurable_snd)
  have hMecke := lintegral_soft_marked_occupation hd (Real.exp_pos t) ρ μ hproj hLaw hfin hmark test ht
  have hLmeas : Measurable (fun ω : PairedArrivalConfiguration => ∑' i,
      ENNReal.ofReal (softMarkedOccupation β d z ω i) * test (arrivalLength d ω.1 i, ω.2 i)) := by
    refine Measurable.tsum fun i => (measurable_softMarkedOccupation β d z i).ennreal_ofReal.mul ?_
    exact hf.comp (measurable_snd.comp ((measurable_pi_apply i).comp measurable_snd))
  have hL : (∫⁻ ω, ∑' i, ENNReal.ofReal (occupiedChild β d t ω i) *
        f (logMessageDerivative β d (child [] i) t ω) ∂law) =
      ∫⁻ ω, ∑' i, ENNReal.ofReal (softMarkedOccupation β d z ω i) *
        test (arrivalLength d ω.1 i, ω.2 i) ∂markedArrivalSequenceLaw ρ := by
    rw [← hP, lintegral_map hLmeas hdata]
    apply lintegral_congr_ae
    filter_upwards [ae_lower_logFugacity_recursion hβ hd, ae_summable_weight hβ hd] with ω hω hw
    have hi (i : ℕ) : H (branch i ω) = lower β d z (child [] i) ω := lower_branch β d z [] ω i
    let q (i : ℕ) := weight β d ω [] i * lower β d z (child [] i) ω
    have hq₀ (i : ℕ) : 0 ≤ q i :=
      mul_nonneg (weight_nonneg β d ω [] i) (hω t (child [] i)).1.le
    have hq : Summable q := Summable.of_nonneg_of_le hq₀
      (fun i => mul_le_mul_of_nonneg_left (hω t (child [] i)).2.1 (weight_nonneg β d ω [] i))
      ((hw []).mul_right z⁻¹)
    have hterm (i : ℕ) : cavityTerm β d (firstArrivalConfiguration (data ω)) i = q i := by
      change weight β d ω [] i * H (branch i ω) = q i
      rw [hi]
    have hupdate : arrivalSoftOutput β d z (firstArrivalConfiguration (data ω)) = H ω := by
      unfold arrivalSoftOutput arrivalWeightedSum
      simp only [hterm, ← ENNReal.ofReal_tsum_of_nonneg hq₀ hq, ENNReal.toReal_ofReal (tsum_nonneg hq₀)]
      exact (hω t []).2.2.symm
    apply tsum_congr
    intro i
    change ENNReal.ofReal (occupiedChild β d t ω i) *
        f (logMessageDerivative β d (child [] i) t ω) =
      ENNReal.ofReal (weight β d ω [] i * H (branch i ω) *
        arrivalSoftOutput β d z (firstArrivalConfiguration (data ω))) * f (D (branch i ω))
    have hDb (i : ℕ) : D (branch i ω) = logMessageDerivative β d (child [] i) t ω :=
      logMessageDerivative_branch β d [] t ω i
    rw [hupdate, hi, hDb]
    rfl
  rw [hL, hMecke]
  have hRm : Measurable (fun p : EdgeSample =>
      ENNReal.ofReal (occupiedEdge β d t p) * f (D p.2.2)) := by
    have hsnd : Measurable (fun p : EdgeSample => p.2.2) := measurable_snd.comp measurable_snd
    exact (measurable_occupiedEdge β d t).ennreal_ofReal.mul (hf.comp (hD.comp hsnd))
  change _ = ∫⁻ p, ENNReal.ofReal (occupiedEdge β d t p) * f (D p.2.2)
    ∂(intensity d).prod (law.prod law)
  rw [lintegral_prod _ hRm.aemeasurable]
  apply lintegral_congr
  intro x
  have hslice : Measurable (fun p : Environment × Environment =>
      ENNReal.ofReal (occupiedEdge β d t (x, p)) * f (D p.2)) := by
    have hs : Measurable (fun p : Environment × Environment => (x, p)) :=
      measurable_const.prodMk measurable_id
    exact hRm.comp hs
  rw [lintegral_prod_symm _ hslice.aemeasurable]
  let K (p : (ℝ × ℝ) × ℝ) :=
    ENNReal.ofReal (edgeOccupation (Real.exp (-β * x)) p.1.1 p.2) * f p.1.2
  have hK : Measurable K := by
    have hA : Measurable (fun p : (ℝ × ℝ) × ℝ => p.1.1) := measurable_fst.comp measurable_fst
    have hB : Measurable (fun p : (ℝ × ℝ) × ℝ => p.2) := measurable_snd
    have hw : Measurable (fun _ : (ℝ × ℝ) × ℝ => Real.exp (-β * x)) := measurable_const
    have h := (hw.mul hA).mul hB
    exact (h.div (measurable_const.add h)).ennreal_ofReal.mul
      (hf.comp (measurable_snd.comp measurable_fst))
  change (∫⁻ B, ∫⁻ A, K (B, A) ∂μ ∂law.map mark) = _
  rw [lintegral_map (hK.lintegral_prod_right' (ν := μ)) hm]
  apply lintegral_congr
  intro B
  have hconst : Measurable (fun A : ℝ => (mark B, A)) := measurable_const.prodMk measurable_id
  change (∫⁻ A, K (mark B, A) ∂law.map H) = _
  have hKm : Measurable (fun A : ℝ => K (mark B, A)) := hK.comp hconst
  rw [lintegral_map hKm hH]
  apply lintegral_congr
  intro A
  change ENNReal.ofReal (edgeOccupation (Real.exp (-β * x)) (H B) (H A)) * f (D B) =
    ENNReal.ofReal (edgeOccupation (Real.exp (-β * x)) (H A) (H B)) * f (D B)
  unfold edgeOccupation
  rw [show Real.exp (-β * x) * H B * H A = Real.exp (-β * x) * H A * H B by ring]

private theorem ae_logMessageDerivative_mem_Icc {β d t : ℝ} (hβ : 0 < β) (hd : 0 < d)
    (ht : ∀ᵐ ω ∂law, ∀ v : Vertex,
      HasDerivAt (fun s => Real.log (lower β d (Real.exp s) v ω))
        (logMessageDerivative β d v t ω) t) :
    ∀ᵐ ω ∂law, ∀ v, logMessageDerivative β d v t ω ∈ Icc (-1) 1 := by
  filter_upwards [ht, ae_extremal_logLipschitz hβ hd] with ω hder hreg
  intro v
  apply abs_le.mp
  rw [← Real.norm_eq_abs, ← (hder v).deriv]
  simpa only [NNReal.coe_one] using norm_deriv_le_of_lipschitz (x₀ := t) (hreg v).2.1

private theorem ae_occupiedChild_bounds {β d : ℝ} (hβ : 0 < β) (hd : 0 < d) (t : ℝ) :
    ∀ᵐ ω ∂law, ∀ i, occupiedChild β d t ω i ∈ Icc 0
      (weight β d ω [] i * Real.exp (-2*t)) := by
  filter_upwards [ae_lower_logFugacity_recursion hβ hd] with ω hω
  intro i
  have hA := hω t (child [] i)
  have hB := hω t []
  have hw := weight_nonneg β d ω [] i
  refine ⟨mul_nonneg (mul_nonneg hw hA.1.le) hB.1.le, ?_⟩
  unfold occupiedChild
  rw [mul_assoc, show -2 * t = -t + -t by ring, Real.exp_add, Real.exp_neg]
  exact mul_le_mul_of_nonneg_left (mul_le_mul hA.2.1 hB.2.1 hB.1.le (by positivity)) hw

private theorem ae_occupiedEdge_bounds {β d : ℝ} (hβ : 0 < β) (hd : 0 < d) (t : ℝ) :
    ∀ᵐ p ∂betheEdgeMeasure d, occupiedEdge β d t p ∈ Icc 0
      (Real.exp (-β*p.1) * Real.exp (-2*t)) := by
  filter_upwards [ae_edge_pair d (ae_lower_logFugacity_recursion hβ hd)] with p hp
  let W := Real.exp (-β * p.1)
  let A := lower β d (Real.exp t) [] p.2.1
  let B := lower β d (Real.exp t) [] p.2.2
  have hA := hp.1 t []
  have hB := hp.2 t []
  have hw : 0 ≤ W := Real.exp_nonneg _
  have hprod : 0 ≤ W * A * B := mul_nonneg (mul_nonneg hw hA.1.le) hB.1.le
  have hden : 1 ≤ 1 + W * A * B := le_add_of_nonneg_right hprod
  refine ⟨div_nonneg hprod (zero_le_one.trans hden), (div_le_self hprod hden).trans ?_⟩
  rw [mul_assoc, show -2 * t = -t + -t by ring, Real.exp_add, Real.exp_neg]
  exact mul_le_mul_of_nonneg_left (mul_le_mul hA.2.1 hB.2.1 hB.1.le (by positivity)) hw

private noncomputable def rootOccupiedTest (β d t : ℝ) (f : ℝ → ℝ) (ω : Environment) :=
  ∑' i, occupiedChild β d t ω i * f (logMessageDerivative β d (child [] i) t ω)

private noncomputable def edgeOccupiedTest (β d t : ℝ) (f : ℝ → ℝ) (p : EdgeSample) :=
  occupiedEdge β d t p * f (logMessageDerivative β d [] t p.2.2)

private theorem integral_occupiedTest_nonneg {β d t : ℝ} (hβ : 0 < β) (hd : 0 < d)
    (hD : ∀ᵐ ω ∂law, ∀ v, logMessageDerivative β d v t ω ∈ Icc (-1) 1)
    {f : ℝ → ℝ} (hf : Measurable f) (hf₀ : ∀ x, 0 ≤ f x)
    (hf₁ : ∀ x ∈ Icc (-1) 1, f x ≤ 1) :
    Integrable (rootOccupiedTest β d t f) law ∧
    Integrable (edgeOccupiedTest β d t f) (betheEdgeMeasure d) ∧
    (∀ᵐ ω ∂law, Summable (fun i => occupiedChild β d t ω i *
      f (logMessageDerivative β d (child [] i) t ω))) ∧
    (∫ ω, rootOccupiedTest β d t f ω ∂law) =
      ∫ p, edgeOccupiedTest β d t f p ∂betheEdgeMeasure d := by
  let F := rootOccupiedTest β d t f
  let G := edgeOccupiedTest β d t f
  have hmF : Measurable F := Measurable.tsum fun i => (measurable_occupiedChild β d t i).mul
    (hf.comp (measurable_logMessageDerivative_at β d t (child [] i)))
  have hmG : Measurable G := (measurable_occupiedEdge β d t).mul
    (hf.comp ((measurable_logMessageDerivative_at β d t []).comp (measurable_snd.comp measurable_snd)))
  have hF : ∀ᵐ ω ∂law, ∀ i, occupiedChild β d t ω i *
      f (logMessageDerivative β d (child [] i) t ω) ∈
      Icc 0 (weight β d ω [] i * Real.exp (-2*t)) := by
    filter_upwards [hD, ae_occupiedChild_bounds hβ hd t] with ω hω hq i
    exact ⟨mul_nonneg (hq i).1 (hf₀ _),
      (mul_le_of_le_one_right (hq i).1 (hf₁ _ (hω (child [] i)))).trans (hq i).2⟩
  have hG : ∀ᵐ p ∂betheEdgeMeasure d, G p ∈ Icc 0
      (Real.exp (-β * p.1) * Real.exp (-2*t)) := by
    filter_upwards [ae_edge_pair d hD, ae_occupiedEdge_bounds hβ hd t] with p hp hq
    exact ⟨mul_nonneg hq.1 (hf₀ _), (mul_le_of_le_one_right hq.1 (hf₁ _ (hp.2 []))).trans hq.2⟩
  have hS : ∀ᵐ ω ∂law, Summable (fun i => occupiedChild β d t ω i *
      f (logMessageDerivative β d (child [] i) t ω)) := by
    filter_upwards [hF, ae_summable_weight hβ hd] with ω hω hw
    exact Summable.of_nonneg_of_le (fun i => (hω i).1) (fun i => (hω i).2) ((hw []).mul_right _)
  have hnn : 0 ≤ᵐ[law] F := hF.mono fun ω hω => tsum_nonneg fun i => (hω i).1
  have hfi : Integrable F law := by
    refine ((integrable_root_totalWeight hβ hd).mul_const (Real.exp (-2*t))).mono'
      hmF.aestronglyMeasurable ?_
    filter_upwards [hnn, hF, hS, ae_summable_weight hβ hd] with ω h₀ hω hs hw
    rw [Real.norm_of_nonneg h₀]
    change F ω ≤ (∑' i, weight β d ω [] i) * Real.exp (-2*t)
    rw [← tsum_mul_right]
    exact hs.tsum_le_tsum (fun i => (hω i).2) ((hw []).mul_right _)
  have hgi : Integrable G (betheEdgeMeasure d) :=
    ((integrable_betheWeight hβ hd).mul_const (Real.exp (-2*t))).mono' hmG.aestronglyMeasurable
      (hG.mono fun p hp => (Real.norm_of_nonneg hp.1).trans_le hp.2)
  refine ⟨hfi, hgi, hS, ?_⟩
  have hEq : (∫⁻ ω, ENNReal.ofReal (F ω) ∂law) =
      ∫⁻ p, ENNReal.ofReal (G p) ∂betheEdgeMeasure d := by
    calc
      _ = ∫⁻ ω, ∑' i, ENNReal.ofReal (occupiedChild β d t ω i) *
          ENNReal.ofReal (f (logMessageDerivative β d (child [] i) t ω)) ∂law := by
        apply lintegral_congr_ae
        filter_upwards [hF, hS] with ω hω hs
        unfold F rootOccupiedTest
        rw [ENNReal.ofReal_tsum_of_nonneg (fun i => (hω i).1) hs]
        exact tsum_congr fun i => ENNReal.ofReal_mul' (hf₀ _)
      _ = ∫⁻ p, ENNReal.ofReal (occupiedEdge β d t p) *
          ENNReal.ofReal (f (logMessageDerivative β d [] t p.2.2)) ∂betheEdgeMeasure d :=
        lintegral_canonical_occupiedDerivative hβ hd t (ENNReal.ofReal ∘ f) hf.ennreal_ofReal
      _ = _ := lintegral_congr fun p => (ENNReal.ofReal_mul' (hf₀ _)).symm
  rw [integral_eq_lintegral_of_nonneg_ae hnn hmF.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (hG.mono fun _ h => h.1) hmG.aestronglyMeasurable, hEq]

private theorem mul_eq_pos_sub_neg (a b : ℝ) :
    a * b = a * max b 0 - a * max (-b) 0 := by
  by_cases h : 0 ≤ b
  · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
    ring
  · rw [max_eq_right (not_le.mp h).le, max_eq_left (neg_nonneg.mpr (not_le.mp h).le)]
    ring

/-- Signed endpoint exchange for the differentiated canonical recursion. -/
theorem ae_integral_rootEndpointDerivative_eq {β d : ℝ} (hβ : 0 < β) (hd : 0 < d) :
    ∀ᵐ t : ℝ ∂volume,
      (∫ ω, rootEndpointDerivative β d t ω ∂law) =
        ∫ p, edgeEndpointDerivative β d t p ∂betheEdgeMeasure d := by
  filter_upwards [ae_ae_hasDerivAt_logMessage hβ hd] with t hder
  have hD := ae_logMessageDerivative_mem_Icc hβ hd hder
  let fp (x : ℝ) := max x 0
  let fm (x : ℝ) := max (-x) 0
  have hp := integral_occupiedTest_nonneg hβ hd hD
    (show Measurable fp by unfold fp; fun_prop)
    (fun x => le_max_right x 0) (fun x hx => max_le hx.2 zero_le_one)
  have hm := integral_occupiedTest_nonneg hβ hd hD
    (show Measurable fm by unfold fm; fun_prop)
    (fun x => le_max_right (-x) 0) (fun x hx => max_le (by linarith only [hx.1]) zero_le_one)
  have hroot : rootEndpointDerivative β d t =ᵐ[law] (fun ω =>
      rootOccupiedTest β d t fp ω - rootOccupiedTest β d t fm ω) := by
    filter_upwards [hp.2.2.1, hm.2.2.1] with ω h₁ h₂
    unfold rootEndpointDerivative rootOccupiedTest
    rw [← h₁.tsum_sub h₂]
    exact tsum_congr fun i => mul_eq_pos_sub_neg (occupiedChild β d t ω i) _
  have hedge : ∀ p, edgeEndpointDerivative β d t p =
      edgeOccupiedTest β d t fp p - edgeOccupiedTest β d t fm p :=
    fun p => mul_eq_pos_sub_neg (occupiedEdge β d t p) (logMessageDerivative β d [] t p.2.2)
  rw [integral_congr_ae hroot, integral_sub hp.1 hm.1,
    hp.2.2.2, hm.2.2.2, ← integral_sub hp.2.1 hm.2.1]
  exact integral_congr_ae (Eventually.of_forall fun p => (hedge p).symm)

/-- The canonical soft Bethe pressure equals the integrated vacancy expression. -/
theorem softBethePressure_eq_integral {β d : ℝ} (hβ : 0 < β) (hd : 0 < d) (t : ℝ) :
    softBethePressure β d t =
      2 * t + 2 * ∫ s in Ioi t, (1 - expectedVacancy β d s) :=
  softBethePressure_eq_integral_of_endpoint_exchange hβ hd t
    (ae_integral_rootEndpointDerivative_eq hβ hd)

end Certificate.CanonicalTree

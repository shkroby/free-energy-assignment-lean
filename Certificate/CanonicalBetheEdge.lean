import Certificate.CanonicalBetheVertex

/-! Differentiation and endpoint symmetry for the canonical Bethe edge term. -/

open Filter MeasureTheory Set
open scoped Topology

namespace Certificate.CanonicalTree

abbrev EdgeSample := ℝ × (Environment × Environment)

/-- The intensity measure of one edge and two independent endpoint trees. -/
noncomputable def betheEdgeMeasure (d : ℝ) : Measure EdgeSample :=
  (intensity d).prod (law.prod law)

noncomputable def edgeLogTerm (β d t : ℝ) (p : EdgeSample) : ℝ :=
  Real.log (1 + Real.exp (-β * p.1) * lower β d (Real.exp t) [] p.2.1 *
    lower β d (Real.exp t) [] p.2.2)

noncomputable def edgeEndpointDerivative (β d t : ℝ) (p : EdgeSample) : ℝ :=
  edgeOccupation (Real.exp (-β * p.1)) (lower β d (Real.exp t) [] p.2.1)
    (lower β d (Real.exp t) [] p.2.2) * logMessageDerivative β d [] t p.2.2

theorem measurable_edgeLogTerm (β d t : ℝ) :
    Measurable (edgeLogTerm β d t) := by
  have hA := (measurable_lower β d (Real.exp t) []).comp
    (measurable_fst.comp (measurable_snd : Measurable (Prod.snd : EdgeSample → _)))
  have hB := (measurable_lower β d (Real.exp t) []).comp
    (measurable_snd.comp (measurable_snd : Measurable (Prod.snd : EdgeSample → _)))
  unfold edgeLogTerm
  exact (measurable_const.add (((Real.measurable_exp.comp
    (measurable_fst.const_mul (-β))).mul hA).mul hB)).log

private theorem measurable_edgeEndpointDerivative (β d t : ℝ) :
    Measurable (edgeEndpointDerivative β d t) := by
  have hfst : Measurable (fun p : EdgeSample => p.2.1) := measurable_fst.comp measurable_snd
  have hsnd : Measurable (fun p : EdgeSample => p.2.2) := measurable_snd.comp measurable_snd
  have ha := (measurable_lower β d (Real.exp t) []).comp hfst
  have hb := (measurable_lower β d (Real.exp t) []).comp hsnd
  have hw : Measurable (fun p : EdgeSample => Real.exp (-β * p.1)) :=
    Real.measurable_exp.comp ((measurable_fst : Measurable (Prod.fst : EdgeSample → ℝ)).const_mul (-β))
  have hpair : Measurable (fun p : EdgeSample => (t, p.2.2)) := measurable_const.prodMk hsnd
  have hD := (measurable_logMessageDerivative β d []).comp hpair
  have hg := (hw.mul ha).mul hb
  unfold edgeEndpointDerivative edgeOccupation
  exact (hg.div (measurable_const.add hg)).mul hD

theorem integrable_betheWeight {β d : ℝ} (hβ : 0 < β) (hd : 0 < d) :
    Integrable (fun p : EdgeSample => Real.exp (-β * p.1)) (betheEdgeMeasure d) := by
  let : IsProbabilityMeasure law := isProbabilityMeasure_law
  let : SigmaFinite (intensity d) := sigmaFinite_intensity d
  have h := integrable_intensity_exp_rpow hd zero_lt_one hβ
  simp only [Real.rpow_one] at h
  have hf := measurePreserving_fst (μ := intensity d) (ν := law.prod law)
  exact hf.integrable_comp_of_integrable h

theorem ae_edge_pair {p : Environment → Prop} (d : ℝ) (hp : ∀ᵐ ω ∂law, p ω) :
    ∀ᵐ e ∂betheEdgeMeasure d, p e.2.1 ∧ p e.2.2 := by
  let : IsProbabilityMeasure law := isProbabilityMeasure_law
  let : SigmaFinite (intensity d) := sigmaFinite_intensity d
  have hfst := Measure.quasiMeasurePreserving_fst (μ := law) (ν := law)
  have hsnd := Measure.quasiMeasurePreserving_snd (μ := law) (ν := law)
  have hpair := Measure.quasiMeasurePreserving_snd (μ := intensity d) (ν := law.prod law)
  exact hpair.tendsto_ae.eventually (hfst.tendsto_ae.eventually hp |>.and
    (hsnd.tendsto_ae.eventually hp))

private theorem bound_rootProduct {β d t : ℝ} {a b : Environment}
    (ha : lower β d (Real.exp t) [] a ∈ Ioc 0 (Real.exp t)⁻¹)
    (hb : lower β d (Real.exp t) [] b ∈ Ioc 0 (Real.exp t)⁻¹) :
    lower β d (Real.exp t) [] a * lower β d (Real.exp t) [] b ≤ Real.exp (-2 * t) := by
  calc
    _ ≤ (Real.exp t)⁻¹ * (Real.exp t)⁻¹ := mul_le_mul ha.2 hb.2 hb.1.le (by positivity)
    _ = _ := by rw [← Real.exp_neg, ← Real.exp_add]; congr 1; ring

theorem ae_norm_edgeLogTerm_le {β d : ℝ} (hβ : 0 < β) (hd : 0 < d) (t : ℝ) :
    ∀ᵐ p ∂betheEdgeMeasure d, ‖edgeLogTerm β d t p‖ ≤ Real.exp (-β * p.1) * Real.exp (-2*t) := by
  filter_upwards [ae_edge_pair d (ae_lower_logFugacity_recursion hβ hd)]
    with p hp
  have hA := hp.1 t []
  have hB := hp.2 t []
  let w := Real.exp (-β * p.1)
  let A := lower β d (Real.exp t) [] p.2.1
  let B := lower β d (Real.exp t) [] p.2.2
  have hw : 0 ≤ w := Real.exp_nonneg _
  have h₂ : 0 ≤ w * A * B := mul_nonneg (mul_nonneg hw hA.1.le) hB.1.le
  have hab := bound_rootProduct (a := p.2.1) (b := p.2.2) ⟨hA.1, hA.2.1⟩ ⟨hB.1, hB.2.1⟩
  change ‖Real.log (1 + w * A * B)‖ ≤ w * Real.exp (-2 * t)
  rw [Real.norm_of_nonneg (Real.log_nonneg (le_add_of_nonneg_right h₂))]
  calc
    _ ≤ w * A * B := by
      linarith only [Real.log_le_sub_one_of_pos (show 0 < 1 + w * A * B by positivity)]
    _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hab hw

theorem integrable_edgeLogTerm {β d : ℝ} (hβ : 0 < β) (hd : 0 < d) (t : ℝ) :
    Integrable (edgeLogTerm β d t) (betheEdgeMeasure d) :=
  ((integrable_betheWeight hβ hd).mul_const (Real.exp (-2*t))).mono'
    (measurable_edgeLogTerm β d t).aestronglyMeasurable (ae_norm_edgeLogTerm_le hβ hd t)

private theorem edgeSlopeEnvelope {w x t c : ℝ} {A B : ℝ → ℝ} (hw : 0 ≤ w)
    (hA : ∀ s, A s ∈ Ioc 0 (Real.exp s)⁻¹) (hB : ∀ s, B s ∈ Ioc 0 (Real.exp s)⁻¹)
    (hAlip : LipschitzWith 1 (fun s => Real.log (A s)))
    (hBlip : LipschitzWith 1 (fun s => Real.log (B s))) (hx : c ≤ x) (ht : c ≤ t) :
    ‖Real.log (1 + w * A x * B x) - Real.log (1 + w * A t * B t)‖ ≤
      (w * (2 * Real.exp (-2 * c))) * ‖x - t‖ := by
  let G (a : ℝ) := Real.log (1 + w * Real.exp a)
  let L (s : ℝ) := Real.log (A s) + Real.log (B s)
  let C := -2 * c
  have hG (a : ℝ) : HasDerivAt G (w * Real.exp a / (1 + w * Real.exp a)) a :=
    (((Real.hasDerivAt_exp a).const_mul w).const_add 1).log
      ((show 0 < 1 + w * Real.exp a by positivity).ne')
  have hbound (a : ℝ) (ha : a ∈ Iic C) : ‖deriv G a‖ ≤ w * Real.exp C := by
    have hwa : 0 ≤ w * Real.exp a := by positivity
    rw [(hG a).deriv, Real.norm_of_nonneg (by positivity)]
    calc
      _ ≤ w * Real.exp a := div_le_self hwa (le_add_of_nonneg_right hwa)
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ha) hw
  have heq (s : ℝ) : G (L s) = Real.log (1 + w * A s * B s) := by
    dsimp [G, L]
    rw [Real.exp_add, Real.exp_log (hA s).1, Real.exp_log (hB s).1, mul_assoc]
  have hL (s : ℝ) (hs : c ≤ s) : L s ∈ Iic C := by
    have ha := Real.log_le_log (hA s).1 (hA s).2
    have hb := Real.log_le_log (hB s).1 (hB s).2
    rw [Real.log_inv, Real.log_exp] at ha hb
    change Real.log (A s) + Real.log (B s) ≤ -2 * c
    linarith only [ha, hb, hs]
  have hLlip : ‖L x - L t‖ ≤ 2 * ‖x - t‖ := by
    have ha := lipschitzWith_iff_dist_le_mul.mp hAlip x t
    have hb := lipschitzWith_iff_dist_le_mul.mp hBlip x t
    simp only [NNReal.coe_one, one_mul, dist_eq_norm] at ha hb
    have he : L x - L t =
        (Real.log (A x) - Real.log (A t)) + (Real.log (B x) - Real.log (B t)) := by dsimp [L]; ring
    rw [he]
    linarith only [norm_add_le (Real.log (A x) - Real.log (A t))
      (Real.log (B x) - Real.log (B t)), ha, hb]
  rw [← heq x, ← heq t]
  calc
    _ ≤ (w * Real.exp C) * ‖L x - L t‖ :=
      (convex_Iic C).norm_image_sub_le_of_norm_deriv_le
        (fun a _ => (hG a).differentiableAt) hbound
        (hL t ht) (hL x hx)
    _ ≤ (w * Real.exp C) * (2 * ‖x - t‖) :=
      mul_le_mul_of_nonneg_left hLlip (by positivity)
    _ = _ := by dsimp only [C]; ring

private def swapEndpoints (p : EdgeSample) : EdgeSample := (p.1, p.2.swap)

private theorem measurePreserving_swapEndpoints (d : ℝ) :
    MeasurePreserving swapEndpoints (betheEdgeMeasure d) (betheEdgeMeasure d) := by
  let : IsProbabilityMeasure law := isProbabilityMeasure_law
  let : SigmaFinite (intensity d) := sigmaFinite_intensity d
  refine ⟨measurable_fst.prodMk (measurable_swap.comp measurable_snd), ?_⟩
  change ((intensity d).prod (law.prod law)).map (Prod.map id Prod.swap) = _
  rw [← Measure.map_prod_map _ _ measurable_id measurable_swap, Measure.map_id, Measure.prod_swap]
  rfl

private theorem integrable_edgeEndpointDerivative {β d t : ℝ} (hβ : 0 < β) (hd : 0 < d)
    (ht : ∀ᵐ ω ∂law, ∀ v : Vertex,
      HasDerivAt (fun s => Real.log (lower β d (Real.exp s) v ω))
        (logMessageDerivative β d v t ω) t) :
    Integrable (edgeEndpointDerivative β d t) (betheEdgeMeasure d) := by
  refine ((integrable_betheWeight hβ hd).mul_const (Real.exp (-2*t))).mono'
    (measurable_edgeEndpointDerivative β d t).aestronglyMeasurable ?_
  have hall := (ae_lower_logFugacity_recursion hβ hd).and ((ae_extremal_logLipschitz hβ hd).and ht)
  filter_upwards [ae_edge_pair d hall] with p hp
  have hA := hp.1.1 t []
  have hB := hp.2.1 t []
  have hL := (hp.2.2.1 []).2.1
  have hD := hp.2.2.2 []
  have hnorm : ‖logMessageDerivative β d [] t p.2.2‖ ≤ 1 := by
    rw [← hD.deriv]
    simpa only [NNReal.coe_one] using norm_deriv_le_of_lipschitz (x₀ := t) hL
  let w := Real.exp (-β * p.1)
  let A := lower β d (Real.exp t) [] p.2.1
  let B := lower β d (Real.exp t) [] p.2.2
  have hw : 0 ≤ w := Real.exp_nonneg _
  have hab := bound_rootProduct (a := p.2.1) (b := p.2.2) ⟨hA.1, hA.2.1⟩ ⟨hB.1, hB.2.1⟩
  have h₂ : 0 ≤ w * A * B := mul_nonneg (mul_nonneg hw hA.1.le) hB.1.le
  let q := w * A * B / (1 + w * A * B)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  change ‖q * logMessageDerivative β d [] t p.2.2‖ ≤ w * Real.exp (-2*t)
  rw [norm_mul, Real.norm_of_nonneg hq]
  calc
    _ ≤ q * 1 := mul_le_mul_of_nonneg_left hnorm hq
    _ ≤ w * A * B := by rw [mul_one]; exact div_le_self h₂ (le_add_of_nonneg_right h₂)
    _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hab hw

/-- The expected edge correction is differentiable at almost every deterministic
log fugacity. Endpoint symmetry doubles the contribution of the second endpoint. -/
theorem ae_hasDerivAt_expected_edgeLogTerm {β d : ℝ} (hβ : 0 < β) (hd : 0 < d) :
    ∀ᵐ t : ℝ ∂volume,
      HasDerivAt (fun s => ∫ p, edgeLogTerm β d s p ∂betheEdgeMeasure d)
        (2 * ∫ p, edgeEndpointDerivative β d t p ∂betheEdgeMeasure d) t := by
  filter_upwards [ae_ae_hasDerivAt_logMessage hβ hd] with t ht
  let D := edgeEndpointDerivative β d t
  let μ := betheEdgeMeasure d
  let E (p : EdgeSample) := D (swapEndpoints p) + D p
  have hi := integrable_edgeEndpointDerivative hβ hd ht
  have h₁ : Integrable (D ∘ swapEndpoints) μ :=
    (measurePreserving_swapEndpoints d).integrable_comp_of_integrable hi
  have hval : (∫ p, E p ∂μ) = 2 * ∫ p, D p ∂μ := by
    change (∫ p, (D ∘ swapEndpoints) p + D p ∂μ) = _
    rw [integral_add h₁ hi]
    have hm := measurePreserving_swapEndpoints d
    have hs : (∫ p, D p ∂μ.map swapEndpoints) = (∫ p, (D ∘ swapEndpoints) p ∂μ) :=
      integral_map hm.measurable.aemeasurable (measurable_edgeEndpointDerivative β d t).aestronglyMeasurable
    have hmap : μ.map swapEndpoints = μ := hm.map_eq
    rw [hmap] at hs
    rw [← hs]
    change (∫ p, D p ∂μ) + (∫ p, D p ∂μ) = _
    ring
  rw [← hval]
  apply hasDerivAt_integral_of_slope_envelope (integrable_edgeLogTerm hβ hd)
    ((integrable_betheWeight hβ hd).mul_const (2 * Real.exp (2*(1-t))))
  · have hall := (ae_lower_logFugacity_recursion hβ hd).and ht
    filter_upwards [ae_edge_pair d hall] with p hp
    have h := hasDerivAt_edge_logCorrection (Real.exp_nonneg (-β * p.1))
      (fun s => (hp.1.1 s []).1) (fun s => (hp.2.1 s []).1) (hp.1.2 []) (hp.2.2 [])
    refine h.congr_deriv ?_
    let w := Real.exp (-β * p.1)
    let a := lower β d (Real.exp t) [] p.2.1
    let b := lower β d (Real.exp t) [] p.2.2
    let da := logMessageDerivative β d [] t p.2.1
    let db := logMessageDerivative β d [] t p.2.2
    change edgeOccupation w a b * (da + db) = edgeOccupation w b a * da + edgeOccupation w a b * db
    have hswap : edgeOccupation w b a = edgeOccupation w a b := by
      unfold edgeOccupation
      rw [show w * b * a = w * a * b by ring]
    rw [hswap]
    ring
  · have hnear : ∀ᶠ s in 𝓝[≠] t, t - 1 < s :=
      nhdsWithin_le_nhds (Ioi_mem_nhds (by linarith : t - 1 < t))
    filter_upwards [hnear, self_mem_nhdsWithin] with s hs hst
    have hall := (ae_lower_logFugacity_recursion hβ hd).and (ae_extremal_logLipschitz hβ hd)
    filter_upwards [ae_edge_pair d hall] with p hp
    have h := edgeSlopeEnvelope (Real.exp_nonneg (-β * p.1))
      (fun u => ⟨(hp.1.1 u []).1, (hp.1.1 u []).2.1⟩)
      (fun u => ⟨(hp.2.1 u []).1, (hp.2.1 u []).2.1⟩)
      (hp.1.2 []).2.1 (hp.2.2 []).2.1 hs.le (show t - 1 ≤ t by linarith)
    have hst' : s ≠ t := hst
    rw [slope_def_field, norm_div, div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hst'))]
    simpa only [edgeLogTerm, show -2 * (t - 1) = 2 * (1-t) by ring] using h

/-- The expected edge term is Lipschitz on each compact log-fugacity interval. -/
theorem absolutelyContinuousOnInterval_expected_edgeLogTerm {β d : ℝ}
    (hβ : 0 < β) (hd : 0 < d) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun s => ∫ p, edgeLogTerm β d s p ∂betheEdgeMeasure d) a b := by
  let c := min a b
  let w (p : EdgeSample) := Real.exp (-β * p.1)
  let W := ∫ p, w p ∂betheEdgeMeasure d
  let K := 2 * Real.exp (-2 * c)
  have hW : 0 ≤ W := integral_nonneg fun _ => Real.exp_nonneg _
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hlip : LipschitzOnWith (Real.toNNReal (K * W))
      (fun s => ∫ p, edgeLogTerm β d s p ∂betheEdgeMeasure d) (uIcc a b) := by
    apply lipschitzOnWith_iff_dist_le_mul.mpr
    intro s hs t ht
    change s ∈ Icc c (max a b) at hs
    change t ∈ Icc c (max a b) at ht
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (mul_nonneg hK hW),
      ← integral_sub (integrable_edgeLogTerm hβ hd s) (integrable_edgeLogTerm hβ hd t)]
    have hcalc :
        (∫ p, w p * (K * ‖s - t‖) ∂betheEdgeMeasure d) = K * W * ‖s - t‖ := by
      rw [integral_mul_const]
      dsimp only [W]
      ring
    rw [← hcalc]
    apply norm_integral_le_of_norm_le ((integrable_betheWeight hβ hd).mul_const _)
    have hall := (ae_lower_logFugacity_recursion hβ hd).and (ae_extremal_logLipschitz hβ hd)
    filter_upwards [ae_edge_pair d hall] with p hp
    have h := edgeSlopeEnvelope (Real.exp_nonneg (-β * p.1))
      (fun u => ⟨(hp.1.1 u []).1, (hp.1.1 u []).2.1⟩)
      (fun u => ⟨(hp.2.1 u []).1, (hp.2.1 u []).2.1⟩)
      (hp.1.2 []).2.1 (hp.2.2 []).2.1 hs.1 ht.1
    simpa only [edgeLogTerm, w, K, mul_assoc] using h
  exact hlip.absolutelyContinuousOnInterval

end Certificate.CanonicalTree

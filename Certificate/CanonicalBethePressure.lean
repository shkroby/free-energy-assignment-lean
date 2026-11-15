import Certificate.CanonicalBetheEdge
import Mathlib.MeasureTheory.Integral.ExpDecay

/-! Normalization and integration of the Bethe pressure on the canonical tree. -/

open Filter MeasureTheory Set
open scoped Topology

namespace Certificate.CanonicalTree

noncomputable def expectedVacancy (β d t : ℝ) : ℝ :=
  ∫ ω, Real.exp t * lower β d (Real.exp t) [] ω ∂law

noncomputable def softBethePressure (β d t : ℝ) : ℝ :=
  -2 * (∫ ω, Real.log (lower β d (Real.exp t) [] ω) ∂law) -
    ∫ p, edgeLogTerm β d t p ∂betheEdgeMeasure d

noncomputable def rootEndpointDerivative (β d t : ℝ) (ω : Environment) : ℝ :=
  ∑' i, weight β d ω [] i * lower β d (Real.exp t) (child [] i) ω *
    lower β d (Real.exp t) [] ω * logMessageDerivative β d (child [] i) t ω

private theorem integrable_vacancy {β d : ℝ} (hβ : 0 < β) (hd : 0 < d) (t : ℝ) :
    Integrable (fun ω => Real.exp t * lower β d (Real.exp t) [] ω) law := by
  let : IsProbabilityMeasure law := isProbabilityMeasure_law
  refine (integrable_const (1 : ℝ)).mono'
    (measurable_const.mul (measurable_lower β d (Real.exp t) [])).aestronglyMeasurable ?_
  filter_upwards [ae_lower_logFugacity_recursion hβ hd] with ω hω
  have hz := Real.exp_pos t
  have h := hω t []
  rw [Real.norm_of_nonneg (mul_nonneg hz.le h.1.le)]
  exact (mul_le_mul_of_nonneg_left h.2.1 hz.le).trans_eq (mul_inv_cancel₀ hz.ne')

theorem measurable_expectedVacancy (β d : ℝ) : Measurable (expectedVacancy β d) := by
  let : IsProbabilityMeasure law := isProbabilityMeasure_law
  have h : Measurable (fun p : ℝ × Environment => Real.exp p.1 * lower β d (Real.exp p.1) [] p.2) :=
    (Real.measurable_exp.comp measurable_fst).mul (measurable_lower_logFugacity β d [])
  exact h.stronglyMeasurable.integral_prod_right'.measurable

theorem integrableOn_vacancyDeficit {β d : ℝ} (hβ : 0 < β) (hd : 0 < d) (t : ℝ) :
    IntegrableOn (fun s => 1 - expectedVacancy β d s) (Ioi t) := by
  let : IsProbabilityMeasure law := isProbabilityMeasure_law
  let W := ∫ ω, ∑' i, weight β d ω [] i ∂law
  refine ((exp_neg_integrableOn_Ioi t (show (0 : ℝ) < 2 by norm_num)).mul_const W).mono'
    (measurable_const.sub (measurable_expectedVacancy β d)).aestronglyMeasurable ?_
  filter_upwards with s
  have hiv := integrable_vacancy hβ hd s
  have hi := (integrable_root_totalWeight hβ hd).const_mul (Real.exp (-2*s))
  have hg := ae_logFugacity_gap_bounds hβ hd s
  have hdef :
      1 - expectedVacancy β d s =
        ∫ ω, (1 - Real.exp s * lower β d (Real.exp s) [] ω) ∂law := by
    rw [integral_sub (integrable_const (1 : ℝ)) hiv, integral_const]
    simp [expectedVacancy]
  have hnonneg : 0 ≤ 1 - expectedVacancy β d s := by
    rw [hdef]
    exact integral_nonneg_of_ae (hg.mono fun _ h => h.2.1)
  rw [Real.norm_of_nonneg hnonneg, hdef]
  have hb := integral_mono_ae ((integrable_const (1 : ℝ)).sub hiv) hi
    (hg.mono fun _ h => h.2.2)
  rw [integral_const_mul] at hb
  simpa only [W, neg_mul, Pi.sub_apply] using hb

private theorem absolutelyContinuousOnInterval_expected_logMessage {β d : ℝ}
    (hβ : 0 < β) (hd : 0 < d) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun s => ∫ ω, Real.log (lower β d (Real.exp s) [] ω) ∂law) a b := by
  let : IsProbabilityMeasure law := isProbabilityMeasure_law
  have hlip : LipschitzWith 1 (fun s => ∫ ω, Real.log (lower β d (Real.exp s) [] ω) ∂law) := by
    apply lipschitzWith_iff_dist_le_mul.mpr
    intro s t
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul,
      ← integral_sub (integrable_logMessage_root hβ hd s) (integrable_logMessage_root hβ hd t)]
    refine (norm_integral_le_of_norm_le_const (C := ‖s - t‖) ?_).trans_eq ?_
    · filter_upwards [ae_extremal_logLipschitz hβ hd] with ω hω
      have h := lipschitzWith_iff_dist_le_mul.mp (hω []).2.1 s t
      simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using h
    · simp
  exact hlip.lipschitzOnWith.absolutelyContinuousOnInterval

theorem absolutelyContinuousOnInterval_softBethePressure {β d : ℝ}
    (hβ : 0 < β) (hd : 0 < d) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (softBethePressure β d) a b := by
  have h := (absolutelyContinuousOnInterval_expected_logMessage hβ hd a b).const_mul (-2)
  exact h.sub (absolutelyContinuousOnInterval_expected_edgeLogTerm hβ hd a b)

theorem tendsto_softBethePressure_minus_twice_logFugacity {β d : ℝ}
    (hβ : 0 < β) (hd : 0 < d) :
    Tendsto (fun t => softBethePressure β d t - 2 * t) atTop (𝓝 0) := by
  let : IsProbabilityMeasure law := isProbabilityMeasure_law
  let W := ∫ ω, ∑' i, weight β d ω [] i ∂law
  let V := ∫ p : EdgeSample, Real.exp (-β * p.1) ∂betheEdgeMeasure d
  have hsmall : Tendsto (fun t : ℝ => Real.exp (-2 * t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (Tendsto.const_mul_atTop_of_neg (by norm_num : (-2 : ℝ) < 0) tendsto_id)
  refine squeeze_zero_norm (a := fun t => Real.exp (-2 * t) * (2 * W + V)) ?_ ?_
  · intro t
    have h1 := norm_integral_le_of_norm_le
      ((integrable_root_totalWeight hβ hd).const_mul (Real.exp (-2 * t)))
      ((ae_logFugacity_gap_bounds hβ hd t).mono fun _ h => h.1)
    have h2 := norm_integral_le_of_norm_le
      ((integrable_betheWeight hβ hd).mul_const (Real.exp (-2 * t))) (ae_norm_edgeLogTerm_le hβ hd t)
    rw [integral_const_mul] at h1
    rw [integral_mul_const] at h2
    let A := ∫ ω, (Real.log (lower β d (Real.exp t) [] ω) + t) ∂law
    let B := ∫ p, edgeLogTerm β d t p ∂betheEdgeMeasure d
    have heq : softBethePressure β d t - 2 * t = -2 * A - B := by
      dsimp [A, B, softBethePressure]
      rw [integral_add (integrable_logMessage_root hβ hd t) (integrable_const t), integral_const]
      simp only [probReal_univ, one_smul]
      ring
    rw [heq]
    calc
      _ ≤ ‖-2 * A‖ + ‖B‖ := norm_sub_le _ _
      _ = 2 * ‖A‖ + ‖B‖ := by rw [norm_mul]; norm_num
      _ ≤ _ := by change ‖A‖ ≤ Real.exp (-2*t) * W at h1
                  change ‖B‖ ≤ V * Real.exp (-2*t) at h2
                  nlinarith only [h1, h2]
  · simpa only [zero_mul] using hsmall.mul_const (2 * W + V)

theorem integrable_rootEndpointDerivative {β d t : ℝ} (hβ : 0 < β) (hd : 0 < d)
    (ht : ∀ᵐ ω ∂law, ∀ v : Vertex,
      HasDerivAt (fun s => Real.log (lower β d (Real.exp s) v ω))
        (logMessageDerivative β d v t ω) t) :
    Integrable (rootEndpointDerivative β d t) law := by
  refine ((integrable_root_totalWeight hβ hd).mul_const (Real.exp (-2 * t))).mono' ?_ ?_
  · refine (Measurable.tsum fun i => ?_).aestronglyMeasurable
    have hpair : Measurable (fun ω : Environment => (t, ω)) := measurable_const.prodMk measurable_id
    have hD := (measurable_logMessageDerivative β d (child [] i)).comp hpair
    exact (((measurable_weight β d [] i).mul (measurable_lower β d (Real.exp t) (child [] i))).mul
      (measurable_lower β d (Real.exp t) [])).mul hD
  · filter_upwards [ht, ae_summable_weight hβ hd, ae_lower_logFugacity_recursion hβ hd,
      ae_extremal_logLipschitz hβ hd] with ω hder hw hrec hreg
    let v := ([] : Vertex)
    let D (i : ℕ) := weight β d ω v i * lower β d (Real.exp t) (child v i) ω *
      lower β d (Real.exp t) v ω * logMessageDerivative β d (child v i) t ω
    have hlim (i : ℕ) : ‖D i‖ ≤ weight β d ω v i * Real.exp (-2 * t) := by
      have hw₀ := weight_nonneg β d ω v i
      have ha := hrec t (child v i)
      have hb := hrec t v
      have hnorm : ‖logMessageDerivative β d (child v i) t ω‖ ≤ 1 := by
        rw [← (hder (child v i)).deriv]
        simpa only [NNReal.coe_one] using
          norm_deriv_le_of_lipschitz (x₀ := t) (hreg (child v i)).2.1
      dsimp only [D]
      rw [norm_mul, norm_mul, norm_mul, Real.norm_of_nonneg hw₀,
        Real.norm_of_nonneg ha.1.le, Real.norm_of_nonneg hb.1.le]
      calc
        _ ≤ weight β d ω v i * lower β d (Real.exp t) (child v i) ω *
              lower β d (Real.exp t) v ω * 1 := by
          exact mul_le_mul_of_nonneg_left hnorm (mul_nonneg (mul_nonneg hw₀ ha.1.le) hb.1.le)
        _ ≤ weight β d ω v i * ((Real.exp t)⁻¹ * (Real.exp t)⁻¹) := by
          rw [mul_one, mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul ha.2.1 hb.2.1 hb.1.le (by positivity)) hw₀
        _ = _ := by rw [← Real.exp_neg, ← Real.exp_add, show -t + -t = -2*t by ring]
    have hW := (hw v).mul_right (Real.exp (-2*t))
    have hsum := Summable.of_nonneg_of_le (fun i => norm_nonneg (D i)) hlim hW
    have hb := (norm_tsum_le_tsum_norm hsum).trans (hsum.tsum_le_tsum hlim hW)
    rw [tsum_mul_right] at hb
    exact hb

theorem expected_logMessageDerivative_eq {β d : ℝ} (hβ : 0 < β) (hd : 0 < d) :
    ∀ᵐ t : ℝ ∂volume,
      (∫ ω, logMessageDerivative β d [] t ω ∂law) =
        -(expectedVacancy β d t + ∫ ω, rootEndpointDerivative β d t ω ∂law) := by
  filter_upwards [ae_ae_logMessageDerivative_recursion hβ hd, ae_ae_hasDerivAt_logMessage hβ hd]
    with s hs hdif
  have hr : (∫ ω, logMessageDerivative β d [] s ω ∂law) =
      ∫ ω, -(Real.exp s * lower β d (Real.exp s) [] ω + rootEndpointDerivative β d s ω) ∂law :=
    integral_congr_ae (hs.mono fun _ h => h [])
  rw [hr, integral_neg, integral_add (integrable_vacancy hβ hd s)
    (integrable_rootEndpointDerivative hβ hd hdif)]
  rfl

/-- The canonical Bethe pressure is the integrated vacancy pressure once
the integrated occupied-edge endpoint test is identified by marked insertion. -/
theorem softBethePressure_eq_integral_of_endpoint_exchange {β d : ℝ}
    (hβ : 0 < β) (hd : 0 < d) (t : ℝ)
    (hx : ∀ᵐ s : ℝ ∂volume,
      (∫ ω, rootEndpointDerivative β d s ω ∂law) =
        ∫ p, edgeEndpointDerivative β d s p ∂betheEdgeMeasure d) :
    softBethePressure β d t =
      2 * t + 2 * ∫ s in Ioi t, (1 - expectedVacancy β d s) := by
  refine bethe_eq_pressure_integral_of_ae_deriv t
    (absolutelyContinuousOnInterval_softBethePressure hβ hd) ?_
    (integrableOn_vacancyDeficit hβ hd t)
    (tendsto_softBethePressure_minus_twice_logFugacity hβ hd)
  filter_upwards [hx, expected_logMessageDerivative_eq hβ hd,
    ae_hasDerivAt_expected_logMessage hβ hd, ae_hasDerivAt_expected_edgeLogTerm hβ hd]
    with s hswap hrec hv he
  have he' : HasDerivAt (fun u => ∫ p, edgeLogTerm β d u p ∂betheEdgeMeasure d)
      ((∫ p, edgeEndpointDerivative β d s p ∂betheEdgeMeasure d) +
        ∫ ω, rootEndpointDerivative β d s ω ∂law) s :=
    he.congr_deriv (by rw [hswap, two_mul])
  exact hasDerivAt_bethe_after_endpoint_exchange hv he' (by rw [hrec, neg_neg]) hswap.symm

end Certificate.CanonicalTree

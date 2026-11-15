import Certificate.ArrivalLowerTail
import Certificate.HardLogUpperTail
import Certificate.PoissonPWIT
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Lower logarithmic tail of a hard cavity law

The exceptional marks are controlled by the upper logarithmic tail. Their
stretched exponential splits into a factor in the threshold and a factor in
the integration variable. The remaining denominator is controlled by its
first moment.
-/

open Filter MeasureTheory Set
open scoped ENNReal

namespace Certificate

private theorem ae_intensity_pos (d : ℝ) : ∀ᵐ x ∂intensity d, 0 < x := by
  apply ae_iff.mpr
  have h : {x : ℝ | ¬0 < x} = Iic 0 := by ext x; simp
  rw [h, intensity_Iic_zero]

/-- A stretched exponential is integrable against its matching
pseudodimension intensity. -/
theorem lintegral_stretched_intensity_lt_top {d c : ℝ} (hd : 0 < d) (hc : 0 < c) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (-c*x^d)) ∂intensity d) < ∞ := by
  have hf : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (-c*x^d))) := by fun_prop
  have hp : Measurable (fun x : ℝ => x ^ (1/d : ℝ)) := by fun_prop
  rw [← map_volume_rpow_eq_intensity hd, lintegral_map hf hp]
  have heq :
      (∫⁻ x in Ioi (0:ℝ), ENNReal.ofReal (Real.exp (-c*(x ^ (1/d : ℝ))^d))) =
        ∫⁻ x in Ioi (0:ℝ), ENNReal.ofReal (Real.exp (-c*x)) := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro x hx
    change ENNReal.ofReal (Real.exp (-c * (x ^ (1/d : ℝ))^d)) =
      ENNReal.ofReal (Real.exp (-c*x))
    rw [one_div, Real.rpow_inv_rpow (mem_Ioi.mp hx).le hd.ne']
  rw [heq]
  have hInt : IntegrableOn (fun x : ℝ => Real.exp (-c*x)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hc) 0
  have hfin : (∫⁻ x in Ioi (0:ℝ), ‖Real.exp (-c*x)‖ₑ) < ∞ :=
    hasFiniteIntegral_iff_enorm.mp hInt.hasFiniteIntegral
  have hn (x : ℝ) : ‖Real.exp (-c*x)‖ₑ = ENNReal.ofReal (Real.exp (-c*x)) :=
    Real.enorm_eq_ofReal (Real.exp_nonneg _)
  simpa only [hn] using hfin

private theorem lintegral_quarter_intensity_lt_top {d : ℝ} (hd : 0 < d) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (-((x/4)^d / 4))) ∂intensity d) < ∞ := by
  let c : ℝ := 1 / (4 * (4 : ℝ)^d)
  have h4 : 0 < (4 : ℝ)^d := Real.rpow_pos_of_pos (by norm_num) _
  have hc : 0 < c := div_pos zero_lt_one (mul_pos (by norm_num) h4)
  have eq :
      (∫⁻ x, ENNReal.ofReal (Real.exp (-((x/4)^d / 4))) ∂intensity d) =
        ∫⁻ x, ENNReal.ofReal (Real.exp (-c*x^d)) ∂intensity d := by
    apply lintegral_congr_ae
    filter_upwards [ae_intensity_pos d] with x hx
    congr 2
    rw [Real.div_rpow hx.le (by norm_num : (0:ℝ) ≤ 4)]
    dsimp [c]
    field_simp [h4.ne']
  rw [eq]
  exact lintegral_stretched_intensity_lt_top hd hc

/-- A stretched upper mark tail bounds the exceptional intensity in the
lower-tail estimate. -/
theorem arrival_log_exceptional_intensity_le {β d K : ℝ} (hd : 0 < d) (hK : 0 ≤ K)
    (μ : Measure ℝ)
    (hUpper : ∀ t : ℝ, 0 ≤ t → μ (Ioi (Real.exp (β*t))) ≤
      ENNReal.ofReal (K * Real.exp (-((t/2)^d/2)))) (t : ℝ) (ht : 0 ≤ t) :
    let I := ∫⁻ x, ENNReal.ofReal (Real.exp (-((x/4)^d/4))) ∂intensity d
    (∫⁻ x, μ (Ioi (Real.exp (β*(t+x)/2))) ∂intensity d) ≤
      ENNReal.ofReal ((K * I.toReal) * Real.exp (-((t/4)^d/4))) := by
  let I := ∫⁻ x, ENNReal.ofReal (Real.exp (-((x/4)^d/4))) ∂intensity d
  have hI : I ≠ ∞ := (lintegral_quarter_intensity_lt_top hd).ne
  let T := Real.exp (-((t/4)^d/4))
  have hT : 0 ≤ K*T := mul_nonneg hK (Real.exp_nonneg _)
  have hpt :
      ∀ᵐ x ∂intensity d,
        μ (Ioi (Real.exp (β*(t+x)/2))) ≤
          ENNReal.ofReal (K*T) * ENNReal.ofReal (Real.exp (-((x/4)^d/4))) := by
    filter_upwards [ae_intensity_pos d] with x hx
    rw [mul_div_assoc]
    refine (hUpper ((t+x)/2) (by positivity)).trans ?_
    have ht' : (t/4)^d ≤ (((t+x)/2)/2)^d :=
      Real.rpow_le_rpow (by positivity) (by linarith) hd.le
    have hx' : (x/4)^d ≤ (((t+x)/2)/2)^d :=
      Real.rpow_le_rpow (by positivity) (by linarith) hd.le
    rw [← ENNReal.ofReal_mul hT]
    apply ENNReal.ofReal_le_ofReal
    dsimp [T]
    rw [mul_assoc, ← Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ hK
    exact Real.exp_le_exp.mpr (by linarith)
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (K*T) * ENNReal.ofReal (Real.exp (-((x/4)^d/4)))
        ∂intensity d := lintegral_mono_ae hpt
    _ = ENNReal.ofReal (K*T) * I :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = _ := by
      change ENNReal.ofReal (K*T) * I = ENNReal.ofReal (K * I.toReal * T)
      conv_lhs => rw [← ENNReal.ofReal_toReal hI, ← ENNReal.ofReal_mul hT]
      congr 1
      ring

/-- The exceptional intensity is controlled for an arbitrary hard cavity law. -/
theorem hard_cavity_log_exceptional_intensity {β d : ℝ} (hd : 0 < d) (hβ : 0 < β)
    {μ : Measure ℝ} (h : IsCavityLaw β d μ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t →
      (∫⁻ x, μ (Ioi (Real.exp (β*(t+x)/2))) ∂intensity d) ≤
        ENNReal.ofReal (C * Real.exp (-((t/4)^d/4))) := by
  obtain ⟨K, hK, hUpper⟩ := hard_cavity_log_upperTail hd hβ h
  have hK₀ : 0 ≤ K := zero_le_one.trans hK
  let I := ∫⁻ x, ENNReal.ofReal (Real.exp (-((x/4)^d/4))) ∂intensity d
  exact ⟨K * I.toReal, mul_nonneg hK₀ ENNReal.toReal_nonneg,
    arrival_log_exceptional_intensity_le hd hK₀ μ hUpper⟩

/-- The first-moment term after dividing by a fixed fraction of the
denominator threshold. -/
theorem arrival_lowerTail_remainder_eq {β d : ℝ} (hd : 0 < d) (hβ : 0 < β)
    (t : ℝ) {a : ℝ} (ha : 0 < a) :
    let I := ∫⁻ x, ENNReal.ofReal (Real.exp (-((β/2)*x))) ∂intensity d
    (∫⁻ x, ENNReal.ofReal (Real.exp (β*(t-x)/2)) ∂intensity d) /
      ENNReal.ofReal (Real.exp (β*t) / a) =
        ENNReal.ofReal (a * I.toReal * Real.exp (-(β*t/2))) := by
  dsimp only
  let I := ∫⁻ x, ENNReal.ofReal (Real.exp (-((β/2)*x))) ∂intensity d
  have hI : I ≠ ∞ := by
    exact (lintegral_exp_intensity_lt_top hd (half_pos hβ)).ne
  have hn :
      (∫⁻ x, ENNReal.ofReal (Real.exp (β*(t-x)/2)) ∂intensity d) =
        ENNReal.ofReal (Real.exp (β*t/2)) * I := by
    calc
      _ = ∫⁻ x, ENNReal.ofReal (Real.exp (β*t/2)) *
          ENNReal.ofReal (Real.exp (-((β/2)*x))) ∂intensity d := by
        apply lintegral_congr
        intro x
        rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
        congr 2
        ring
      _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  change _ = ENNReal.ofReal (a * I.toReal * Real.exp (-(β*t/2)))
  rw [hn, ← ENNReal.ofReal_toReal hI, ENNReal.toReal_ofReal ENNReal.toReal_nonneg,
    ← ENNReal.ofReal_mul (Real.exp_nonneg _),
    ← ENNReal.ofReal_div_of_pos (div_pos (Real.exp_pos _) ha)]
  congr 1
  calc
    _ = a * I.toReal * (Real.exp (β*t/2) / Real.exp (β*t)) := by
      field_simp [ha.ne', (Real.exp_pos (β*t)).ne']
    _ = _ := by
      rw [← Real.exp_sub, show β*t/2 - β*t = -(β*t/2) by ring]

/-- The lower logarithmic tail of an arbitrary hard cavity law is bounded by
a law-dependent stretched exponential plus an ordinary exponential. -/
theorem hard_cavity_log_lowerTail {β d : ℝ} (hd : 0 < d) (hβ : 0 < β)
    {μ : Measure ℝ} (h : IsCavityLaw β d μ) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ t : ℝ, 0 ≤ t →
      μ (Iio (Real.exp (-β*t))) ≤
        ENNReal.ofReal (C₁ * Real.exp (-((t/4)^d/4)) + C₂ * Real.exp (-(β*t/2))) := by
  let : IsProbabilityMeasure μ := h.1
  obtain ⟨C₁, h₁, hException⟩ := hard_cavity_log_exceptional_intensity hd hβ h
  let C₂ := (∫⁻ x, ENNReal.ofReal (Real.exp (-((β/2)*x))) ∂intensity d).toReal
  refine ⟨C₁, C₂, h₁, ENNReal.toReal_nonneg, fun t ht => ?_⟩
  have hf := ae_hard_arrivalWeightedSum_spec h
  have hp : ∀ᵐ ω ∂markedSpacings μ, 0 < 0 + (arrivalWeightedSum β d ω).toReal := by
    simpa only [zero_add] using hf.mono (fun _ hh => hh.2)
  have hL := arrival_log_lowerTail_bound hd μ (hf.mono fun _ hh => hh.1) hp
    (map_arrivalSoftOutput_zero_of_IsCavityLaw h) (Real.exp_pos (β*t))
  have hrem := arrival_lowerTail_remainder_eq hd hβ t zero_lt_one
  dsimp only at hrem
  rw [div_one, one_mul] at hrem
  rw [sub_zero, hrem] at hL
  have hTerm₁ : 0 ≤ C₁ * Real.exp (-((t/4)^d/4)) := mul_nonneg h₁ (Real.exp_nonneg _)
  have hTerm₂ : 0 ≤ C₂ * Real.exp (-(β*t/2)) := mul_nonneg ENNReal.toReal_nonneg (Real.exp_nonneg _)
  rw [ENNReal.ofReal_add hTerm₁ hTerm₂]
  exact hL.trans (add_le_add (hException t ht) le_rfl)

end Certificate

import Certificate.SoftMedianEstimate
import Certificate.SoftUpperTightness

/-! A uniform lower bound on the log median at fixed positive temperature. -/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace Certificate

/-- The log medians of all bounded soft fixed-point laws stay bounded below
as fugacity varies in `(0, 1]`. -/
theorem exists_uniform_soft_log_median_lower_bound {β d : ℝ} (hβ : 0 < β) (hd : 0 < d) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : ℝ, 0 < z → z ≤ 1 →
      ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
        (∀ᵐ h ∂μ, h ∈ Icc 0 z⁻¹) →
        (markedSpacings μ).map (arrivalSoftOutput β d z) = μ →
        ∀ b : ℝ, 1 / 2 ≤ (μ (Iic (Real.exp (β * b)))).toReal →
          1 / 2 ≤ (μ (Ici (Real.exp (β * b)))).toReal → -B ≤ b := by
  let ε := ENNReal.ofReal (1 / 2)
  let cap := ENNReal.ofReal (1 / 8)
  let c := (2 * (2 : ℝ) ^ d)⁻¹
  let f (x : ℝ) := ENNReal.ofReal (Real.exp (-c * x ^ d))
  let g (x : ℝ) := ENNReal.ofReal (Real.exp (-β * x / 2))
  let a (N : ℕ) := ∫⁻ x in Ioi (N : ℝ), f x ∂intensity d
  let e (N : ℕ) := ∫⁻ x in Ioi (N : ℝ), g x ∂intensity d
  have hc : 0 < c := by dsimp [c]; positivity
  have hε : ε ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (by norm_num)
  have hf : Measurable f := by unfold f; fun_prop
  have hg : Measurable g := by unfold g; fun_prop
  have hf0 : Tendsto a atTop (𝓝 0) :=
    lintegral_Ioi_nat_tendsto_zero f hf (lintegral_stretched_intensity_lt_top hd hc).ne
  have hgFin : (∫⁻ x, g x ∂intensity d) ≠ ∞ := by
    have hg_eq : g = fun x ↦ ENNReal.ofReal (Real.exp (-(β / 2) * x)) := by
      funext x
      unfold g
      congr 2
      ring
    rw [hg_eq]
    simpa only [neg_mul] using (lintegral_exp_intensity_lt_top hd (half_pos hβ)).ne
  have hg0 : Tendsto e atTop (𝓝 0) := lintegral_Ioi_nat_tendsto_zero g hg hgFin
  have hfar : Tendsto (fun N ↦ a N + e N / ε) atTop (𝓝 0) := by
    simpa only [ENNReal.zero_div, zero_add] using
      hf0.add (ENNReal.Tendsto.div_const hg0 (Or.inr hε))
  obtain ⟨N, hN⟩ := (hfar.eventually (Iio_mem_nhds
    (show 0 < cap by exact ENNReal.ofReal_pos.mpr (by norm_num)))).exists
  let R : ℝ := N
  have hR : 0 ≤ R := Nat.cast_nonneg N
  obtain ⟨s, _, hS⟩ :=
    exists_uniform_soft_cavity_log_upperTail_window hd hβ hR (η := 1 / 8) (by norm_num)
  let M := max 1 (R ^ d * Real.exp (β * s))
  have hM : 0 < M := zero_lt_one.trans_le (le_max_left _ _)
  have hexp : Tendsto (fun b : ℝ ↦ Real.exp (β * b)) atBot (𝓝 0) :=
    Real.tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_pos hβ).mpr
      (tendsto_id : Tendsto (fun x : ℝ ↦ x) atBot atBot))
  obtain ⟨b₀, hb₀⟩ := eventually_atBot.mp (hexp.eventually
    (Iio_mem_nhds (show 0 < (16 * M)⁻¹ by positivity)))
  let B := max 0 (-b₀)
  refine ⟨B, le_max_left _ _, fun z hz hz₁ μ _ hμ hLaw b hL hU ↦ ?_⟩
  by_contra hn
  have hb' : b ≤ b₀ := by
    have hBB : -b₀ ≤ B := le_max_right _ _
    linarith [lt_of_not_ge hn]
  have hExp : Real.exp (β * b) ≤ (16 * M)⁻¹ := (hb₀ b hb').le
  have hZ : z * Real.exp (β * b) ≤ 1 / 4 := by
    calc
      _ ≤ 1 * Real.exp (β * b) := mul_le_mul_of_nonneg_right hz₁ (Real.exp_nonneg _)
      _ ≤ (16 * M)⁻¹ := by simpa only [one_mul] using hExp
      _ ≤ (4 : ℝ)⁻¹ := inv_anti₀ (by norm_num)
        (by nlinarith only [show 1 ≤ M from le_max_left _ _])
      _ = _ := by norm_num
  have hsmall : R ^ d * Real.exp (β * (b + s)) ≤ 1 / 16 := by
    calc
      _ = (R ^ d * Real.exp (β * s)) * Real.exp (β * b) := by
        rw [mul_add, Real.exp_add]
        ring
      _ ≤ M * (16 * M)⁻¹ :=
        mul_le_mul (le_max_right _ _) hExp (Real.exp_nonneg _) hM.le
      _ = _ := by field_simp [hM.ne']
  have hFin : ∀ᵐ ω ∂markedSpacings μ, arrivalWeightedSum β d ω ≠ ∞ := by
    filter_upwards [ae_arrivalWeightedSum_eq_ofReal_tsum hd hβ μ hμ] with ω hω
    rw [hω]
    exact ENNReal.ofReal_ne_top
  have hupper := measure_shiftedArrivalMass_gt_le (s := s) (b := b) hd hβ hR μ
    hε ENNReal.ofReal_ne_top
  have hWindow : ENNReal.ofReal (R ^ d) * μ (Ioi (Real.exp (β * s))) ≤ cap :=
    (hS s le_rfl z hz μ inferInstance hμ hLaw).2
  have hFarMass : (∫⁻ x in Ioi R, μ (Ioi (Real.exp (β * (x / 2 - b)))) ∂intensity d) ≤ a N := by
    apply setLIntegral_mono' measurableSet_Ioi
    intro x (hx : R < x)
    have hx₀ := hR.trans_lt hx
    have H := arrival_cavity_median_upperTail hd hβ hz.le μ hFin hLaw hU (half_pos hx₀).le
    refine H.trans_eq ?_
    unfold f c
    rw [Real.div_rpow hx₀.le (by norm_num) d]
    congr 2
    ring
  have hNearMean : ENNReal.ofReal (R ^ d * Real.exp (β * (b + s))) / ε ≤ cap := by
    unfold ε cap
    rw [← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    apply ENNReal.ofReal_le_ofReal
    linarith only [hsmall]
  have hLess : markedSpacings μ {ω | ε < shiftedArrivalMass β d b ω} ≤ cap + cap + cap := by
    apply hupper.trans
    rw [ENNReal.add_div]
    calc
      _ ≤ (cap + a N) + (cap + e N / ε) := add_le_add (add_le_add hWindow hFarMass)
        (add_le_add hNearMean le_rfl)
      _ = cap + cap + (a N + e N / ε) := by ac_rfl
      _ ≤ _ := add_le_add_right hN.le _
  have hbig := half_le_measure_shiftedArrivalMass_of_median hz μ hFin hLaw hL hZ
  have hc' : cap + cap + cap < ε := by
    unfold cap ε
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num)).mpr (by norm_num)
  exact (not_lt_of_ge (hbig.trans hLess)) hc'

end Certificate

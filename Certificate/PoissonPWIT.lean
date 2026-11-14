import Certificate.Intensity
import Certificate.PoissonVoid
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Marked PWIT lengths on layers of unit intensity

The length layer between `n^(1/d)` and `(n+1)^(1/d)` has intensity one.
On each layer the mark law is the restricted length intensity times the
specified mark law.
-/

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace Certificate

/-- A layer of PWIT lengths with pseudodimension intensity one. -/
noncomputable def pwitLayer (d : ℝ) (n : ℕ) : Set ℝ :=
  Ioc ((n : ℝ) ^ (1/d)) (((n+1 : ℕ) : ℝ) ^ (1/d))

private theorem pwitLayer_measurable (d : ℝ) (n : ℕ) :
    MeasurableSet (pwitLayer d n) := measurableSet_Ioc

/-- The length intensity of each layer is one. -/
theorem intensity_pwitLayer {d : ℝ} (hd : 0 < d) (n : ℕ) :
    intensity d (pwitLayer d n) = 1 := by
  unfold pwitLayer
  rw [intensity_Ioc hd (Real.rpow_nonneg (Nat.cast_nonneg n) _) (by
    exact Real.rpow_le_rpow (Nat.cast_nonneg n)
      (Nat.cast_le.mpr (Nat.le_succ n)) (one_div_nonneg.mpr hd.le))]
  rw [one_div, Real.rpow_inv_rpow (Nat.cast_nonneg (n+1)) hd.ne',
    Real.rpow_inv_rpow (Nat.cast_nonneg n) hd.ne', Nat.cast_add, Nat.cast_one]
  norm_num

private theorem pwitLayer_disjoint {d : ℝ} (hd : 0 < d) :
    Pairwise (fun i j : ℕ => Disjoint (pwitLayer d i) (pwitLayer d j)) := by
  have key {i j : ℕ} (hij : i < j) : Disjoint (pwitLayer d i) (pwitLayer d j) := by
    have h : (((i+1 : ℕ) : ℝ) ^ (1/d : ℝ)) ≤ (j : ℝ) ^ (1/d : ℝ) :=
      Real.rpow_le_rpow (Nat.cast_nonneg (i+1))
        (Nat.cast_le.mpr (Nat.succ_le_of_lt hij)) (one_div_nonneg.mpr hd.le)
    exact Set.disjoint_left.mpr (fun _ hi hj => hj.1.not_ge (hi.2.trans h))
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact key h
  · exact (key h).symm

private theorem pwitLayer_union {d : ℝ} (hd : 0 < d) :
    (⋃ n, pwitLayer d n) = Ioi 0 := by
  ext x
  simp only [mem_iUnion, mem_Ioi]
  constructor
  · rintro ⟨n, hn⟩
    exact (Real.rpow_nonneg (Nat.cast_nonneg n) _).trans_lt hn.1
  · intro hx
    have hpow : 0 < x^d := Real.rpow_pos_of_pos hx d
    cases H : Nat.ceil (x^d) with
    | zero => exact (by simpa [H] using (Nat.ceil_pos.mpr hpow) : False).elim
    | succ n =>
      have hLo : (n : ℝ) < x^d := Nat.lt_ceil.mp (H ▸ Nat.lt_succ_self n)
      have hHi : x^d ≤ ((n+1 : ℕ) : ℝ) := H ▸ Nat.le_ceil (x^d)
      have hxp : (x^d)^(1/d : ℝ) = x := by
        rw [one_div, Real.rpow_rpow_inv hx.le hd.ne']
      refine ⟨n, ?_⟩
      change ((n : ℝ) ^ (1/d)) < x ∧ x ≤ (((n+1 : ℕ) : ℝ) ^ (1/d))
      rw [← hxp]
      exact ⟨Real.rpow_lt_rpow (Nat.cast_nonneg n) hLo (one_div_pos.mpr hd),
        Real.rpow_le_rpow hpow.le hHi (one_div_nonneg.mpr hd.le)⟩

/-- The layer laws partition the full positive length intensity. -/
theorem sum_intensity_restrict_pwitLayer {d : ℝ} (hd : 0 < d) :
    Measure.sum (fun n => (intensity d).restrict (pwitLayer d n)) = intensity d := by
  rw [← Measure.restrict_iUnion (pwitLayer_disjoint hd) (pwitLayer_measurable _), pwitLayer_union hd]
  apply Measure.restrict_eq_self_of_ae_mem
  apply ae_iff.mpr
  have h : {x : ℝ | x ∉ Ioi (0:ℝ)} = Iic 0 := by ext x; simp
  rw [h]
  exact intensity_Iic_zero d

/-- Independent length and mark, with the length restricted to one unit layer. -/
noncomputable def pwitBatchMarks (d : ℝ) (μ : Measure ℝ) (n : ℕ) : Measure (ℝ × ℝ) :=
  ((intensity d).restrict (pwitLayer d n)).prod μ

theorem pwitBatchMarks_isProbabilityMeasure {d : ℝ} (hd : 0 < d)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ) :
    IsProbabilityMeasure (pwitBatchMarks d μ n) := by
  let : IsProbabilityMeasure ((intensity d).restrict (pwitLayer d n)) :=
    ⟨by rw [Measure.restrict_apply_univ, intensity_pwitLayer hd n]⟩
  unfold pwitBatchMarks
  infer_instance

/-- The marked process built from iid Poisson(1) counts on the unit layers. -/
noncomputable def pwitBatchLaw (d : ℝ) (μ : Measure ℝ) :
    Measure (ℕ → PoissonBatch (ℝ × ℝ)) :=
  poissonProcessLaw (fun _ => 1) (pwitBatchMarks d μ)

theorem pwitBatchLaw_isProbabilityMeasure {d : ℝ} (hd : 0 < d)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] : IsProbabilityMeasure (pwitBatchLaw d μ) := by
  let : ∀ n, IsProbabilityMeasure (pwitBatchMarks d μ n) :=
    pwitBatchMarks_isProbabilityMeasure hd μ
  unfold pwitBatchLaw
  infer_instance

/-- The marked intensity is the manuscript's length intensity times the
independent mark law. -/
theorem pwitBatchIntensity_eq {d : ℝ} (hd : 0 < d)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    poissonIntensity (fun _ => 1) (pwitBatchMarks d μ) = (intensity d).prod μ := by
  unfold poissonIntensity
  simp only [ENNReal.coe_one, one_smul, pwitBatchMarks, ← Measure.prod_sum_left,
    sum_intensity_restrict_pwitLayer hd]

/-- Campbell's first-moment formula for the unit-layer PWIT model. -/
theorem pwit_campbell {d : ℝ} (hd : 0 < d) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f : ℝ × ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, ∑' j, poissonBatchSum (0,0) f (ω j) ∂pwitBatchLaw d μ) =
      ∫⁻ x, f x ∂(intensity d).prod μ := by
  let : ∀ n, IsProbabilityMeasure (pwitBatchMarks d μ n) :=
    pwitBatchMarks_isProbabilityMeasure hd μ
  unfold pwitBatchLaw
  rw [poisson_campbell (0,0) _ _ f hf, pwitBatchIntensity_eq hd μ]

/-- Marked insertion for the unit-layer PWIT model. -/
theorem pwit_insertion {d : ℝ} (hd : 0 < d) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (g : (ℝ × ℝ) × (ℕ → PoissonBatch (ℝ × ℝ)) → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ ω, ∑' j, poissonBatchDeletionSum (0,0)
        (fun z => g (z.1, Function.update ω j z.2)) (ω j) ∂pwitBatchLaw d μ) =
      ∫⁻ z, g z ∂((intensity d).prod μ).prod (pwitBatchLaw d μ) := by
  let : ∀ n, IsProbabilityMeasure (pwitBatchMarks d μ n) :=
    pwitBatchMarks_isProbabilityMeasure hd μ
  unfold pwitBatchLaw
  rw [poisson_insertion (0,0) _ _ g hg, pwitBatchIntensity_eq hd μ]

/-- The probability of seeing no length–mark point in a given measurable set. -/
theorem pwit_void {d : ℝ} (hd : 0 < d) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) (hfin : ((intensity d).prod μ) s ≠ ∞) :
    pwitBatchLaw d μ (poissonAvoid s) =
      ENNReal.ofReal (Real.exp (-(((intensity d).prod μ) s).toReal)) := by
  let : ∀ n, IsProbabilityMeasure (pwitBatchMarks d μ n) :=
    pwitBatchMarks_isProbabilityMeasure hd μ
  have h := poisson_void (fun _ => 1) (pwitBatchMarks d μ) hs
      (by rwa [pwitBatchIntensity_eq hd μ])
  rw [pwitBatchIntensity_eq hd μ] at h
  exact h

/-- If the first-moment integral is finite, the sum over the marked PWIT
configuration is finite almost surely. -/
theorem pwit_ae_sum_lt_top {d : ℝ} (hd : 0 < d) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f : ℝ × ℝ → ℝ≥0∞) (hf : Measurable f)
    (hfin : (∫⁻ x, f x ∂(intensity d).prod μ) ≠ ∞) :
    ∀ᵐ ω ∂pwitBatchLaw d μ, (∑' j, poissonBatchSum (0,0) f (ω j)) < ∞ := by
  have hm : Measurable (fun ω : ℕ → PoissonBatch (ℝ × ℝ) =>
      ∑' j, poissonBatchSum (0,0) f (ω j)) :=
    Measurable.tsum (fun j => (measurable_poissonBatchSum (0,0) f hf).comp (measurable_pi_apply j))
  exact ae_lt_top' hm.aemeasurable (by rwa [pwit_campbell hd μ f hf])

/-- The decaying edge weights have finite intensity integral for every positive
temperature parameter and pseudodimension. -/
theorem lintegral_exp_intensity_lt_top {d β : ℝ} (hd : 0 < d) (hβ : 0 < β) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (-(β*x))) ∂intensity d) < ∞ := by
  let c := d * Real.Gamma d / β ^ d
  have hc : 0 ≤ c := by
    dsimp [c]
    positivity
  have hD : Measurable (fun x : ℝ => ENNReal.ofReal (d * x ^ (d - 1))) := by fun_prop
  have hE : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (-(β*x)))) := by fun_prop
  have hG : Measurable (ProbabilityTheory.gammaPDF d β) :=
    (ProbabilityTheory.measurable_gammaPDFReal d β).ennreal_ofReal
  have heq (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) :
      ENNReal.ofReal (d * x ^ (d-1)) * ENNReal.ofReal (Real.exp (-(β*x))) =
        ENNReal.ofReal c * ProbabilityTheory.gammaPDF d β x := by
    rw [ProbabilityTheory.gammaPDF_of_nonneg (mem_Ioi.mp hx).le,
      ← ENNReal.ofReal_mul (mul_nonneg hd.le (Real.rpow_nonneg (mem_Ioi.mp hx).le _)),
      ← ENNReal.ofReal_mul hc]
    congr 1
    dsimp [c]
    field_simp [(Real.Gamma_pos_of_pos hd).ne', (Real.rpow_pos_of_pos hβ d).ne']
  unfold intensity
  rw [lintegral_withDensity_eq_lintegral_mul _ hD hE]
  have he : (∫⁻ x in Ioi (0:ℝ),
      ENNReal.ofReal (d * x ^ (d-1)) * ENNReal.ofReal (Real.exp (-(β*x)))) =
        ∫⁻ x in Ioi (0:ℝ), ENNReal.ofReal c * ProbabilityTheory.gammaPDF d β x :=
    setLIntegral_congr_fun measurableSet_Ioi heq
  change (∫⁻ x in Ioi (0:ℝ),
      ENNReal.ofReal (d * x ^ (d-1)) * ENNReal.ofReal (Real.exp (-(β*x)))) < ∞
  rw [he, lintegral_const_mul _ hG]
  calc
    _ ≤ ENNReal.ofReal c * ∫⁻ x, ProbabilityTheory.gammaPDF d β x := by
      apply mul_le_mul' le_rfl
      simpa only [Measure.restrict_univ] using
        (lintegral_mono_set (μ := volume) (f := ProbabilityTheory.gammaPDF d β)
          (subset_univ (Ioi (0:ℝ))))
    _ < ∞ := by simp [ProbabilityTheory.lintegral_gammaPDF_eq_one hd hβ]

/-- Exponentially weighted positive marks have a finite outgoing sum almost
surely when the mark law has a finite first positive moment. -/
theorem pwit_exp_weighted_marks_ae_finite {d β : ℝ} (hd : 0 < d) (hβ : 0 < β)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : (∫⁻ y, ENNReal.ofReal y ∂μ) < ∞) :
    ∀ᵐ ω ∂pwitBatchLaw d μ,
      (∑' j, poissonBatchSum (0,0)
        (fun z => ENNReal.ofReal (Real.exp (-(β*z.1))) * ENNReal.ofReal z.2) (ω j)) < ∞ := by
  apply pwit_ae_sum_lt_top hd μ _ (by fun_prop)
  have hE : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (-(β*x)))) := by fun_prop
  have hY : Measurable (fun y : ℝ => ENNReal.ofReal y) := measurable_id.ennreal_ofReal
  have h := lintegral_prod_mul (μ := intensity d) (ν := μ)
    hE.aemeasurable hY.aemeasurable
  rw [h]
  exact (ENNReal.mul_lt_top (lintegral_exp_intensity_lt_top hd hβ) hμ).ne

/-- No mark from a measurable set is seen before the indicated length. -/
theorem pwit_window_void {d R : ℝ} (hd : 0 < d) (hR : 0 ≤ R)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {A : Set ℝ} (hA : MeasurableSet A) :
    pwitBatchLaw d μ (poissonAvoid (Ioc 0 R ×ˢ A)) =
      ENNReal.ofReal (Real.exp (-(R ^ d * (μ A).toReal))) := by
  have hmass : ((intensity d).prod μ) (Ioc 0 R ×ˢ A) =
      ENNReal.ofReal (R ^ d) * μ A := by
    rw [Measure.prod_prod, intensity_Ioc_zero hd hR]
  have hfin : ((intensity d).prod μ) (Ioc 0 R ×ˢ A) ≠ ∞ := by
    rw [hmass]
    exact (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ A)).ne
  rw [pwit_void hd μ (measurableSet_Ioc.prod hA) hfin, hmass,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg hR d)]

end Certificate

import Certificate.LocalTreeShapeMass
import Certificate.LocalExplorationMarks
import Certificate.LocalExplorationPattern

/-!
# Independent marks conditional on a labelled neighborhood

A fixed labelled shape imposes one retained-cost restriction on each
of its selected edges. Once the shape is conditioned on, the selected
costs have the iid normalized retained law.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology BigOperators BoundedContinuousFunction

namespace Certificate.LocalExploration

/-- The vector of costs of the retained edges in a fixed labelled shape. -/
def labelledNeighborhoodCosts {n : ℕ} (E : Finset (Fin n × Fin n)) (C : CostArray) (e : E) : ℝ :=
  C (e.1.1.val, e.1.2.val)

theorem measurable_labelledNeighborhoodCosts {n : ℕ} (E : Finset (Fin n × Fin n)) :
    Measurable (labelledNeighborhoodCosts E) :=
  measurable_pi_iff.mpr (fun _ => measurable_pi_apply _)

private theorem isProbabilityMeasure_conditionalRetainedLaw
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {A : Set ℝ} (hA₀ : μ A ≠ 0) :
    IsProbabilityMeasure (conditionalRetainedLaw μ A) := by
  refine ⟨?_⟩
  rw [conditionalRetainedLaw, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
    univ_inter, smul_eq_mul, ENNReal.inv_mul_cancel hA₀ (measure_ne_top _ _)]

/-- The complete cost vector, conditioned on the shape event, has the
iid retained-cost law. -/
theorem map_cond_labelledNeighborhoodCosts {n : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (L R : Finset (Fin n)) (E : Finset (Fin n × Fin n)) (hE : E ⊆ neighborhoodTestedEdges L R)
    {A : Set ℝ} (hA : MeasurableSet A) (hA₀ : μ A ≠ 0)
    (hS₀ : (iidCosts μ) (labelledNeighborhoodEvent L R E A (fun _ => univ)) ≠ 0) :
    (ProbabilityTheory.cond (iidCosts μ) (labelledNeighborhoodEvent L R E A (fun _ => univ))).map
      (labelledNeighborhoodCosts E) =
      Measure.pi (fun _ : E => conditionalRetainedLaw μ A) := by
  classical
  let : IsProbabilityMeasure (iidCosts μ) := by unfold iidCosts; infer_instance
  let (_ : E) : IsProbabilityMeasure (conditionalRetainedLaw μ A) :=
    isProbabilityMeasure_conditionalRetainedLaw μ hA₀
  let S := labelledNeighborhoodEvent L R E A (fun _ => univ)
  have hS : MeasurableSet S := measurableSet_labelledNeighborhoodEvent L R E hA
    (fun _ _ => MeasurableSet.univ)
  symm
  apply Measure.pi_eq
  intro T hT
  let B (e : Fin n × Fin n) : Set ℝ := if h : e ∈ E then T ⟨e, h⟩ else univ
  have hB (e : Fin n × Fin n) (he : e ∈ E) : MeasurableSet (B e) := by
    simpa only [B, dif_pos he] using hT ⟨e, he⟩
  have hmark : S ∩ (labelledNeighborhoodCosts E ⁻¹' univ.pi T) =
      labelledNeighborhoodEvent L R E A B := by
    ext C
    change ((∀ e ∈ E, C (e.1.val, e.2.val) ∈ A ∩ univ) ∧
        (∀ e ∈ neighborhoodTestedEdges L R \ E, C (e.1.val, e.2.val) ∈ Aᶜ)) ∧
        labelledNeighborhoodCosts E C ∈ univ.pi T ↔
      (∀ e ∈ E, C (e.1.val, e.2.val) ∈ A ∩ B e) ∧
        (∀ e ∈ neighborhoodTestedEdges L R \ E, C (e.1.val, e.2.val) ∈ Aᶜ)
    simp only [Set.mem_inter_iff, Set.mem_univ, and_true, Set.mem_pi, true_implies,
      Subtype.forall, labelledNeighborhoodCosts]
    constructor
    · rintro ⟨⟨h₁, h₂⟩, h₃⟩
      exact ⟨fun e he => ⟨h₁ e he, by simpa only [B, dif_pos he] using h₃ e he⟩, h₂⟩
    · rintro ⟨h₁, h₂⟩
      exact ⟨⟨fun e he => (h₁ e he).1, h₂⟩,
        fun e he => by simpa only [B, dif_pos he] using (h₁ e he).2⟩
  have hsingle (e : E) : μ (A ∩ B e) = μ A * conditionalRetainedLaw μ A (T e) := by
    rw [show B e = T e by simp [B, e.property], conditionalRetainedLaw,
      Measure.smul_apply, Measure.restrict_apply (hT e), smul_eq_mul, ← mul_assoc,
      ENNReal.mul_inv_cancel hA₀ (measure_ne_top _ _), one_mul, inter_comm]
  have hfactor : (iidCosts μ) (labelledNeighborhoodEvent L R E A B) =
      (iidCosts μ) S * ∏ e : E, conditionalRetainedLaw μ A (T e) := by
    rw [measure_labelledNeighborhoodEvent μ L R E hE hA hB,
      show (iidCosts μ) S = _ from measure_labelledNeighborhoodEvent μ L R E hE hA
        (fun _ _ => MeasurableSet.univ)]
    rw [← Finset.prod_coe_sort (s := E) (f := fun e => μ (A ∩ B e))]
    simp_rw [hsingle, Finset.prod_mul_distrib, Set.inter_univ, Finset.prod_const,
      Finset.card_univ, Fintype.card_coe]
    ac_rfl
  rw [Measure.map_apply (measurable_labelledNeighborhoodCosts E) (MeasurableSet.univ_pi hT),
    ProbabilityTheory.cond_apply hS, hmark, hfactor, ← mul_assoc,
    ENNReal.inv_mul_cancel hS₀ (measure_ne_top _ _), one_mul]

/-- Scaled retained edge costs, indexed by the edges of a fixed symbolic
shape using its given labelling. -/
noncomputable def labelledNeighborhoodLengths {I : Type*} {n : ℕ} {E : Finset (Fin n × Fin n)}
    (d κ : ℝ) (labels : I ≃ E) (C : CostArray) (i : I) : ℝ :=
  lengthScale d κ n * labelledNeighborhoodCosts E C (labels i)

theorem measurable_labelledNeighborhoodLengths {I : Type*} {n : ℕ} {E : Finset (Fin n × Fin n)}
    (d κ : ℝ) (labels : I ≃ E) :
    Measurable (labelledNeighborhoodLengths d κ labels) :=
  measurable_pi_iff.mpr (fun i => measurable_const.mul
    ((measurable_pi_apply (labels i)).comp (measurable_labelledNeighborhoodCosts E)))

private theorem map_conditionalRetainedLaw_lengthScale
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {d κ R : ℝ} (hκ : 0 < κ)
    {n : ℕ} (hn : 0 < n) :
    (conditionalRetainedLaw μ (Iic (R / lengthScale d κ n))).map
      (fun c => lengthScale d κ n * c) = retainedLengthLaw μ d κ R n := by
  let s := lengthScale d κ n
  have hs : 0 < s := Real.rpow_pos_of_pos (mul_pos hκ (Nat.cast_pos.mpr hn)) _
  have hm : Measurable (fun c : ℝ => s * c) := measurable_const.mul measurable_id
  have he : (fun c : ℝ => s * c) ⁻¹' Iic R = Iic (R/s) := by
    ext x
    change s*x ≤ R ↔ x ≤ R/s
    rw [le_div_iff₀ hs, mul_comm x s]
  have hmass : μ (Iic (R/s)) = scaledLengthLaw μ d κ n (Iic R) := by
    unfold scaledLengthLaw
    rw [Measure.map_apply hm measurableSet_Iic, he]
  unfold conditionalRetainedLaw retainedLengthLaw
  rw [Measure.map_smul, ← he, ← Measure.restrict_map hm measurableSet_Iic, he, hmass]
  rfl

/-- After scaling and relabelling, the conditioned length vector is the
product of the normalized restricted scaled-length laws. -/
theorem map_cond_labelledNeighborhoodLengths {I : Type*} [Fintype I]
    {n : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ] {d κ r : ℝ}
    (hκ : 0 < κ) (hn : 0 < n) (L R : Finset (Fin n)) (E : Finset (Fin n × Fin n))
    (hE : E ⊆ neighborhoodTestedEdges L R) (labels : I ≃ E)
    (hA₀ : μ (Iic (r / lengthScale d κ n)) ≠ 0)
    (hS₀ : (iidCosts μ) (labelledNeighborhoodEvent L R E
      (Iic (r / lengthScale d κ n)) (fun _ => univ)) ≠ 0) :
    (ProbabilityTheory.cond (iidCosts μ) (labelledNeighborhoodEvent L R E
      (Iic (r / lengthScale d κ n)) (fun _ => univ))).map
      (labelledNeighborhoodLengths d κ labels) =
      Measure.infinitePi (fun _ : I => retainedLengthLaw μ d κ r n) := by
  let A := Iic (r / lengthScale d κ n)
  let s := lengthScale d κ n
  let P := conditionalRetainedLaw μ A
  let : IsProbabilityMeasure P := isProbabilityMeasure_conditionalRetainedLaw μ hA₀
  let f (u : E → ℝ) (i : I) := u (labels i)
  let g (u : I → ℝ) (i : I) := s * u i
  have hf : Measurable f := measurable_pi_lambda _ (fun i => measurable_pi_apply (labels i))
  have hg : Measurable g := measurable_pi_lambda _ (fun i => measurable_const.mul (measurable_pi_apply i))
  have hmapF : (Measure.infinitePi (fun _ : E => P)).map f =
      Measure.infinitePi (fun _ : I => P) :=
    Measure.map_infinitePi_infinitePi_of_inj labels.injective
  rw [show labelledNeighborhoodLengths d κ labels =
      (g ∘ f) ∘ labelledNeighborhoodCosts E from rfl,
    ← Measure.map_map (hg.comp hf) (measurable_labelledNeighborhoodCosts E),
    map_cond_labelledNeighborhoodCosts μ L R E hE measurableSet_Iic hA₀ hS₀,
    ← Measure.infinitePi_eq_pi, ← Measure.map_map hg hf, hmapF]
  change (Measure.infinitePi (fun _ : I => P)).map g = _
  have hg₀ : Measurable (fun x : ℝ => s * x) := measurable_const.mul measurable_id
  calc
    _ = Measure.infinitePi (fun _ : I => P.map (fun x => s * x)) :=
      Measure.infinitePi_map_pi (fun _ : I => P) (fun _ => hg₀)
    _ = _ := by simp only [P, A, s, map_conditionalRetainedLaw_lengthScale μ hκ hn]

/-- Bounded continuous tests on a prescribed finite shape's scaled
marks converge to their expectation under independent truncated
intensity marks. -/
theorem tendsto_integral_cond_labelledNeighborhoodLengths
    {I : Type*} [Fintype I] {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {d κ r : ℝ} (hd : 0 < d) (hκ : 0 < κ) (hr : 0 < r) (hμ : SmallCostTail μ κ d)
    (L R : ∀ n : ℕ, Finset (Fin (n+1))) (E : ∀ n : ℕ, Finset (Fin (n+1) × Fin (n+1)))
    (labels : ∀ n : ℕ, I ≃ E n)
    (hfit : ∀ᶠ n in atTop, E n ⊆ neighborhoodTestedEdges (L n) (R n))
    (g : (I → ℝ) →ᵇ ℝ) :
    Tendsto (fun n => ∫ C, g (labelledNeighborhoodLengths d κ (labels n) C)
      ∂ProbabilityTheory.cond (iidCosts μ) (labelledNeighborhoodEvent (L n) (R n) (E n)
        (Iic (r / lengthScale d κ (n+1))) (fun _ => univ))) atTop
      (𝓝 (∫ x, g x ∂Measure.infinitePi (fun _ : I => truncatedIntensity d r))) := by
  let : IsProbabilityMeasure (iidCosts μ) := by unfold iidCosts; infer_instance
  have h := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
    (tendsto_retainedMarkProduct hd hκ hr hμ I) g
  have hp := tendsto_zero_of_tendsto_mul_atTop (tendsto_scaled_shortEdgeProbability hd hκ hr hμ)
  have hp' := (hp.comp (tendsto_add_atTop_nat 1)).eventually (Iio_mem_nhds
    (zero_lt_one : (0 : ℝ) < 1))
  refine h.congr' ?_
  filter_upwards [hfit, hp'] with n hn hp₁
  let A := Iic (r / lengthScale d κ (n+1))
  let S := labelledNeighborhoodEvent (L n) (R n) (E n) A (fun _ => univ)
  have ha : 0 < r / lengthScale d κ (n+1) :=
    div_pos hr (Real.rpow_pos_of_pos (mul_pos hκ (Nat.cast_pos.mpr (Nat.succ_pos n))) _)
  have hA₀ : μ A ≠ 0 := by
    change μ (Iic _) ≠ 0
    rw [← ofReal_cdf]
    exact (ENNReal.ofReal_pos.mpr (cdf_pos_of_smallCostTail hκ hμ ha)).ne'
  have hA₁ : μ A ≠ 1 := by
    change μ (Iic _) ≠ 1
    rw [← ofReal_cdf, ← ENNReal.ofReal_one]
    exact ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (cdf_nonneg μ _)).mpr hp₁).ne
  have hAcompl : μ Aᶜ ≠ 0 := by
    rw [prob_compl_eq_one_sub measurableSet_Iic]
    exact (tsub_pos_of_lt ((prob_le_one (μ := μ) (s := A)).lt_of_ne hA₁)).ne'
  have hS₀ : (iidCosts μ) S ≠ 0 := by
    rw [show (iidCosts μ) S = _ from measure_labelledNeighborhoodEvent μ (L n) (R n) (E n) hn
      measurableSet_Iic (fun _ _ => MeasurableSet.univ)]
    simp only [Set.inter_univ, Finset.prod_const]
    exact mul_ne_zero (pow_ne_zero _ hA₀) (pow_ne_zero _ hAcompl)
  change (∫ x, g x ∂Measure.infinitePi (fun _ : I => retainedLengthLaw μ d κ r (n+1))) =
    ∫ C, g (labelledNeighborhoodLengths d κ (labels n) C) ∂ProbabilityTheory.cond (iidCosts μ) S
  rw [← map_cond_labelledNeighborhoodLengths μ hκ (Nat.succ_pos n) (L n) (R n) (E n)
    hn (labels n) hA₀ hS₀,
    integral_map (measurable_labelledNeighborhoodLengths d κ (labels n)).aemeasurable
      g.continuous.measurable.aestronglyMeasurable]

end Certificate.LocalExploration

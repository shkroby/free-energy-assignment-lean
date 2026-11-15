import Certificate.SoftConcentration
import Certificate.SoftAssignment
import Certificate.BoundedDifferences
import Certificate.PressureNegative
import Mathlib.Probability.Independence.InfinitePi

/-!
# Bounded differences for the iid monomer pressure

The finite square extracted from the infinite iid array has the product law
of independent rows. Clamping costs at zero gives the everywhere bounded
function required by the product concentration theorem and agrees almost
surely with the original costs.
-/

open Finset Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Topology

namespace Certificate

/-- Extract the first `n` rows and columns of the infinite cost array. -/
def costRows (n : ℕ) (C : CostArray) : Fin n → Fin n → ℝ :=
  fun i j => C (i.val,j.val)

/-- The law of the finite cost square is a product measure over rows. -/
theorem measurePreserving_costRows (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ) :
    MeasurePreserving (costRows n) (iidCosts μ)
      (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))) := by
  let idx (e : Fin n × Fin n) : ℕ × ℕ := (e.1.val,e.2.val)
  let unc (C : CostArray) (e : Fin n × Fin n) : ℝ := C (idx e)
  let cur := MeasurableEquiv.curry (Fin n) (Fin n) ℝ
  have hidx : Function.Injective idx := fun p q h =>
    Prod.ext (Fin.ext (congrArg Prod.fst h)) (Fin.ext (congrArg Prod.snd h))
  have hm (e : Fin n × Fin n) : Measurable (fun C : CostArray => C (idx e)) :=
    measurable_pi_apply (idx e)
  have hu : Measurable unc := measurable_pi_iff.mpr hm
  have hind : iIndepFun (fun e C => C (idx e)) (iidCosts μ) := by
    have h := iIndepFun_infinitePi (P := fun _ : ℕ × ℕ => μ)
      (X := fun _ => (id : ℝ → ℝ)) (fun _ => measurable_id)
    exact h.precomp hidx
  have hmap := hind.map_fun_eq_pi_map (fun e => (hm e).aemeasurable)
  have hμe (e : Fin n × Fin n) : (iidCosts μ).map (fun C => C (idx e)) = μ :=
    Measure.infinitePi_map_eval (fun _ : ℕ × ℕ => μ) (idx e)
  simp_rw [hμe] at hmap
  refine ⟨cur.measurable.comp hu, ?_⟩
  change (iidCosts μ).map (cur ∘ unc) = _
  rw [← Measure.map_map cur.measurable hu, show (iidCosts μ).map unc = _ from hmap]
  simpa only [Measure.infinitePi_eq_pi, cur] using
    (Measure.infinitePi_map_curry (fun (_ : Fin n) (_ : Fin n) => μ))

/-- The centered pressure variance proxy is `n * c²`, where `c` is
the one-row oscillation bound in the manuscript. -/
noncomputable def monomerRowOscillation (n : ℕ) (t : ℝ) : ℝ≥0 :=
  ⟨Real.log (1 + (n : ℝ) * Real.exp (-2 * t)) / n,
    div_nonneg (Real.log_nonneg (le_add_of_nonneg_right (by positivity))) (Nat.cast_nonneg _)⟩

private noncomputable def clampedMatrixWeights (β d κ : ℝ) (n : ℕ)
    (r : Fin n → Fin n → ℝ) (i j : Fin n) : ℝ :=
  Real.exp (-β * (lengthScale d κ n * max (r i j) 0))

private theorem clampedMatrixWeights_nonneg (β d κ : ℝ) (n : ℕ) (r : Fin n → Fin n → ℝ)
    (i j : Fin n) : 0 ≤ clampedMatrixWeights β d κ n r i j :=
  Real.exp_nonneg _

private theorem clampedMatrixWeights_le_one {β κ : ℝ} (hβ : 0 ≤ β) (hκ : 0 ≤ κ) (d : ℝ) (n : ℕ)
    (r : Fin n → Fin n → ℝ) (i j : Fin n) :
    clampedMatrixWeights β d κ n r i j ≤ 1 := by
  unfold clampedMatrixWeights
  apply Real.exp_le_one_iff.mpr
  have hscale : 0 ≤ lengthScale d κ n := by unfold lengthScale; positivity
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hβ)
    (mul_nonneg hscale (le_max_right _ _))

private theorem measurable_clampedPressure (β d κ t : ℝ) (n : ℕ) :
    Measurable (fun r : Fin n → Fin n → ℝ =>
      squareMonomerPressure (clampedMatrixWeights β d κ n r) t) := by
  unfold squareMonomerPressure Tree.monomerPartition clampedMatrixWeights
  fun_prop

private theorem squarePressure_interval {n : ℕ} (hn : 0 < n)
    {w : Fin n → Fin n → ℝ} (hw₀ : ∀ i j, 0 ≤ w i j) (hw₁ : ∀ i j, w i j ≤ 1) (t : ℝ) :
    squareMonomerPressure w t ∈ Icc (2 * t) (2 * t + (n : ℝ) * Real.exp (-2 * t)) := by
  let G := squareWeightedGraph w hw₀
  have hc : (G.vertices.card : ℝ) = 2 * (n : ℝ) := by
    simp [G, squareWeightedGraph]
    ring
  have h := G.logCorrected_bound t
  have heq : squareMonomerPressure w t = 2 * t + G.logCorrected t / n := by
    change Real.log (G.Z t) / n = _
    rw [WeightedGraph.logCorrected, hc]
    field_simp [(show (0 : ℝ) < n from Nat.cast_pos.mpr hn).ne']
    ring
  have hweight : ∑ e ∈ G.edges, G.weight e ≤ (n : ℝ) * n := by
    have h' : ∑ e ∈ G.edges, G.weight e ≤ ∑ _e ∈ G.edges, 1 :=
      Finset.sum_le_sum fun e _ => hw₁ e.1 e.2
    simpa [G, squareWeightedGraph, Fintype.card_prod, nsmul_eq_mul] using h'
  rw [heq]
  refine ⟨le_add_of_nonneg_right (div_nonneg h.1 (Nat.cast_nonneg _)), ?_⟩
  apply add_le_add (le_refl _)
  apply (div_le_iff₀ (Nat.cast_pos.mpr hn)).mpr
  exact (h.2.trans (mul_le_mul_of_nonneg_right hweight (Real.exp_nonneg _))).trans_eq (by ring)


private noncomputable def clampedPressure (β d κ t : ℝ) (n : ℕ) (r : Fin n → Fin n → ℝ) : ℝ :=
  squareMonomerPressure (clampedMatrixWeights β d κ n r) t

private theorem clampedPressure_mgf {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {β κ : ℝ} (hβ : 0 ≤ β) (hκ : 0 ≤ κ) (d t : ℝ) {n : ℕ} (hn : 0 < n) :
    HasSubgaussianMGF (fun r => clampedPressure β d κ t n r -
        ∫ s, clampedPressure β d κ t n s ∂Measure.pi (fun _ : Fin n =>
          Measure.pi (fun _ : Fin n => μ)))
      ((n : ℝ≥0) * (monomerRowOscillation n t) ^ 2)
      (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))) := by
  let P := Measure.pi (fun _ : Fin n => μ)
  let : IsProbabilityMeasure P := by unfold P; infer_instance
  apply hasSubgaussianMGF_of_bounded_differences
    P (a := 2 * t) (b := 2 * t + (n : ℝ) * Real.exp (-2 * t))
  · exact measurable_clampedPressure β d κ t n
  · intro r
    exact squarePressure_interval hn (clampedMatrixWeights_nonneg β d κ n r)
      (clampedMatrixWeights_le_one hβ hκ d n r) t
  · intro r s i h
    have hw (j : Fin n) (hj : j ≠ i) :
        clampedMatrixWeights β d κ n r j = clampedMatrixWeights β d κ n s j := by
      funext k
      unfold clampedMatrixWeights
      rw [congrFun (h j hj) k]
    exact squareMonomerPressure_row_oscillation hn (clampedMatrixWeights_nonneg β d κ n r)
      (clampedMatrixWeights_le_one hβ hκ d n r) (clampedMatrixWeights_nonneg β d κ n s)
      (clampedMatrixWeights_le_one hβ hκ d n s) i hw t

private theorem clampedPressure_eq_of_nonneg (β d κ t : ℝ) (n : ℕ) (C : CostArray)
    (hC : ∀ ij, 0 ≤ C ij) :
    clampedPressure β d κ t n (costRows n C) = softAssignmentPressure β d κ t n C := by
  have hw :
      (fun e : Fin n × Fin n => clampedMatrixWeights β d κ n (costRows n C) e.1 e.2) =
        (assignmentGraph β d κ n C).weight := by
    funext e
    simp only [clampedMatrixWeights, costRows, assignmentGraph, edgeLength,
      max_eq_left (hC (e.1.val,e.2.val))]
  unfold clampedPressure squareMonomerPressure
  rw [hw]
  rfl

theorem centered_mgf_pullback
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {Q : Measure Ω'}
    {g : Ω → ℝ} {f : Ω' → ℝ} {T : Ω → Ω'} (hT : MeasurePreserving T P Q)
    (hf : Measurable f) (heq : f ∘ T =ᵐ[P] g) {c : ℝ≥0}
    (h : HasSubgaussianMGF (fun x => f x - ∫ y, f y ∂Q) c Q) :
    HasSubgaussianMGF (fun x => g x - ∫ y, g y ∂P) c P := by
  have hm₁ : (∫ x, f (T x) ∂P) = ∫ y, f y ∂Q := by
    rw [← hT.map_eq]
    exact (integral_map hT.measurable.aemeasurable hf.aestronglyMeasurable).symm
  have hm₂ : (∫ x, f (T x) ∂P) = ∫ x, g x ∂P := integral_congr_ae heq
  have hmap : HasSubgaussianMGF (fun x => f x - ∫ y, f y ∂Q) c (P.map T) := by
    rw [hT.map_eq]
    exact h
  refine (hmap.of_map hT.measurable.aemeasurable).congr ?_
  filter_upwards [heq] with x hx
  change f (T x) = g x at hx
  change f (T x) - (∫ y, f y ∂Q) = g x - (∫ y, g y ∂P)
  rw [hx, ← hm₁, hm₂]

/-- The actual square monomer pressure obeys a sub-Gaussian MGF bound under
the iid law of the whole array. -/
theorem hasSubgaussianMGF_centered_softAssignmentPressure
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : μ (Iio 0) = 0)
    {β : ℝ} (hβ : 0 ≤ β) (d κ t : ℝ) (hκ : 0 ≤ κ) {n : ℕ} (hn : 0 < n) :
    HasSubgaussianMGF (fun C => softAssignmentPressure β d κ t n C -
        ∫ C', softAssignmentPressure β d κ t n C' ∂iidCosts μ)
      ((n : ℝ≥0) * (monomerRowOscillation n t) ^ 2) (iidCosts μ) := by
  have heq : (clampedPressure β d κ t n) ∘ (costRows n) =ᵐ[iidCosts μ]
      softAssignmentPressure β d κ t n :=
    (ae_cost_nonneg μ hμ).mono fun C hC => clampedPressure_eq_of_nonneg β d κ t n C hC
  exact centered_mgf_pullback (measurePreserving_costRows μ n)
    (measurable_clampedPressure β d κ t n) heq
    (clampedPressure_mgf hβ hκ d t hn)

end Certificate

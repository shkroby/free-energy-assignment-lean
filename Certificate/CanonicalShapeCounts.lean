import Certificate.CanonicalTree
import Certificate.PoissonArrivalCount

/-! The exact product law for the offspring counts of a prescribed shape. -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace Certificate.CanonicalTree

/-- The number of retained children of a vertex with the given spacings. -/
noncomputable def cutoffOffspring (d R : ℝ) (E : Spacings) : ℝ≥0∞ :=
  markedArrivalCount d (Ioc 0 R ×ˢ (Set.univ : Set Unit)) (E, fun _ ↦ ())

theorem measurable_cutoffOffspring (d R : ℝ) : Measurable (cutoffOffspring d R) :=
  (measurable_markedArrivalCount d (measurableSet_Ioc.prod MeasurableSet.univ)).comp
    (measurable_id.prodMk measurable_const)

theorem measure_cutoffOffspring_eq {d R : ℝ} (hd : 0 < d) (hR : 0 ≤ R) (k : ℕ) :
    exponentialSpacings {E | cutoffOffspring d R E = (k : ℝ≥0∞)} =
      poissonMeasure (ENNReal.ofReal (R ^ d)).toNNReal {k} := by
  let μ : Measure Unit := Measure.dirac ()
  let A := Ioc (0 : ℝ) R ×ˢ (Set.univ : Set Unit)
  let P := markedArrivalSequenceLaw μ
  let : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  let : IsProbabilityMeasure exponentialSpacings := isProbabilityMeasure_exponentialSpacings
  have hp : MeasurePreserving Prod.fst P exponentialSpacings :=
    measurePreserving_fst (μ := exponentialSpacings) (ν := Measure.infinitePi (fun _ : ℕ ↦ μ))
  have hA : MeasurableSet A := measurableSet_Ioc.prod MeasurableSet.univ
  have hInt : ((intensity d).prod μ) A = ENNReal.ofReal (R ^ d) := by
    rw [Measure.prod_prod, intensity_Ioc_zero hd hR, measure_univ, mul_one]
  have hfin : ((intensity d).prod μ) A ≠ ∞ := hInt ▸ ENNReal.ofReal_ne_top
  have hProb := canonical_iid_marked_count_probability hd μ hA hfin k
  rw [hInt] at hProb
  let S : Set Spacings := {E | cutoffOffspring d R E = (k : ℝ≥0∞)}
  have hS : MeasurableSet S := measurableSet_eq_fun (measurable_cutoffOffspring d R) measurable_const
  have hpre : Prod.fst ⁻¹' S = {ω : Spacings × (ℕ → Unit) | markedArrivalCount d A ω = (k : ℝ≥0∞)} := by
    ext ω
    have he : (fun _ : ℕ ↦ ()) = ω.2 := funext fun _ ↦ Subsingleton.elim _ _
    change markedArrivalCount d A (ω.1, fun _ ↦ ()) = (k : ℝ≥0∞) ↔ _
    rw [he]
    rfl
  change exponentialSpacings S = _
  rw [← hp.map_eq, Measure.map_apply hp.measurable hS, hpre]
  exact hProb

/-- Prescribing the offspring counts at any finite set of vertices gives
the product of the corresponding Poisson masses. For a finite plane tree
observed to a fixed depth, the prescription is imposed on the interior. -/
theorem measure_offspringCountCylinder {d R : ℝ} (hd : 0 < d) (hR : 0 ≤ R)
    (vertices : Finset Vertex) (children : Vertex → ℕ) :
    law {ω | ∀ v ∈ vertices, cutoffOffspring d R (ω v) = (children v : ℝ≥0∞)} =
      ∏ v ∈ vertices, poissonMeasure (ENNReal.ofReal (R ^ d)).toNNReal {children v} := by
  let : IsProbabilityMeasure exponentialSpacings := isProbabilityMeasure_exponentialSpacings
  let B (v : Vertex) := {E | cutoffOffspring d R E = (children v : ℝ≥0∞)}
  have hB (v : Vertex) : MeasurableSet (B v) :=
    measurableSet_eq_fun (measurable_cutoffOffspring d R) measurable_const
  change Measure.infinitePi (fun _ : Vertex ↦ exponentialSpacings)
    ((vertices : Set Vertex).pi B) = _
  rw [Measure.infinitePi_pi _ (fun v _ ↦ hB v)]
  exact Finset.prod_congr rfl fun v _ ↦ measure_cutoffOffspring_eq hd hR (children v)

end Certificate.CanonicalTree

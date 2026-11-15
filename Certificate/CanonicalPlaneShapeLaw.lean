import Certificate.CanonicalShapeCounts
import Certificate.LocalPlaneEmbedding

/-! The exact canonical probability of any prescribed finite plane shape. -/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace Certificate.CanonicalTree

open LocalExploration

theorem ae_cutoffOffspring_eq_nat {d R : ℝ} (hd : 0 < d) (hR : 0 ≤ R) :
    ∀ᵐ E ∂exponentialSpacings, ∃ k : ℕ, cutoffOffspring d R E = (k : ℝ≥0∞) := by
  let : IsProbabilityMeasure exponentialSpacings := isProbabilityMeasure_exponentialSpacings
  let A (k : ℕ) : Set Spacings := {E | cutoffOffspring d R E = (k : ℝ≥0∞)}
  have hA (k : ℕ) : MeasurableSet (A k) :=
    measurableSet_eq_fun (measurable_cutoffOffspring d R) measurable_const
  have hDisjoint : Pairwise (fun i j ↦ Disjoint (A i) (A j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro E hi hj
    apply hij
    have he : (i : ℝ≥0∞) = (j : ℝ≥0∞) := (hi : cutoffOffspring d R E = i).symm.trans hj
    exact_mod_cast he
  have hS : (∑' k : ℕ, poissonMeasure (ENNReal.ofReal (R ^ d)).toNNReal {k}) = 1 := by
    rw [← measure_iUnion (fun i j hij ↦ Set.disjoint_singleton.mpr hij) (fun _ ↦ measurableSet_singleton _)]
    have hu : (⋃ k : ℕ, ({k} : Set ℕ)) = univ := by
      apply eq_univ_of_forall
      intro k
      exact mem_iUnion.mpr ⟨k, mem_singleton k⟩
    rw [hu, measure_univ]
  have hm : exponentialSpacings (⋃ k, A k) = 1 := by
    rw [measure_iUnion hDisjoint hA]
    simp_rw [show ∀ k, exponentialSpacings (A k) =
      poissonMeasure (ENNReal.ofReal (R ^ d)).toNNReal {k} from measure_cutoffOffspring_eq hd hR]
    exact hS
  have hAE := (mem_ae_iff_prob_eq_one (MeasurableSet.iUnion hA)).mpr hm
  filter_upwards [hAE] with E he
  exact Set.mem_iUnion.mp he

/-- The finite-stopping count, given an arbitrary default off the full
measure event on which the count is finite. -/
noncomputable def cutoffOffspringNat (d R : ℝ) (E : Spacings) : ℕ := by
  classical
  exact if h : ∃ k : ℕ, cutoffOffspring d R E = (k : ℝ≥0∞) then h.choose else 0

/-- The canonical shape obtained by retaining edges of length at most the
cutoff before exploring to the fixed depth. -/
noncomputable def cutoffPlaneShape (d R : ℝ) (depth : ℕ) (ω : Environment) : PlaneShape :=
  PlaneShape.ofOffspring depth (fun v ↦ cutoffOffspringNat d R (ω v))

/-- The exact probability of a plane shape is the product of its Poisson
branch probabilities at the interior vertices. -/
theorem measure_cutoffPlaneShape_slots_eq {d R : ℝ} (hd : 0 < d) (hR : 0 ≤ R)
    (shape : PlaneShape) :
    let interior := shape.finite_slots.toFinset.filter (fun v ↦ v.length < shape.depth)
    law {ω | (cutoffPlaneShape d R shape.depth ω).slots = shape.slots} =
      ∏ v ∈ interior, poissonMeasure (ENNReal.ofReal (R ^ d)).toNNReal {shape.childCount v} := by
  classical
  let interior := shape.finite_slots.toFinset.filter (fun v ↦ v.length < shape.depth)
  change law {ω | (cutoffPlaneShape d R shape.depth ω).slots = shape.slots} =
    ∏ v ∈ interior, poissonMeasure (ENNReal.ofReal (R ^ d)).toNNReal {shape.childCount v}
  have hPos : ∀ᵐ ω ∂law, ∀ v, ∃ k : ℕ, cutoffOffspring d R (ω v) = (k : ℝ≥0∞) := by
    let : IsProbabilityMeasure exponentialSpacings := isProbabilityMeasure_exponentialSpacings
    apply ae_all_iff.mpr
    intro v
    have hp := (measurePreserving_eval_infinitePi (fun _ : Vertex ↦ exponentialSpacings) v).quasiMeasurePreserving
    exact hp.tendsto_ae.eventually (ae_cutoffOffspring_eq_nat hd hR)
  have hEq :
      {ω | (cutoffPlaneShape d R shape.depth ω).slots = shape.slots} =ᵐ[law]
        {ω | ∀ v ∈ interior, cutoffOffspring d R (ω v) = (shape.childCount v : ℝ≥0∞)} := by
    filter_upwards [hPos] with ω hω
    apply propext
    change (PlaneShape.ofOffspring shape.depth (fun v ↦ cutoffOffspringNat d R (ω v))).slots =
      shape.slots ↔ _
    rw [shape.ofOffspring_slots_eq_iff]
    have hNat (v : Vertex) : cutoffOffspring d R (ω v) = (cutoffOffspringNat d R (ω v) : ℝ≥0∞) := by
      unfold cutoffOffspringNat
      rw [dif_pos (hω v)]
      exact (hω v).choose_spec
    constructor
    · intro h v hv
      have hv' := Finset.mem_filter.mp hv
      rw [hNat, h v (shape.finite_slots.mem_toFinset.mp hv'.1) hv'.2]
    · intro h v hv hd'
      have hx := h v (Finset.mem_filter.mpr ⟨shape.finite_slots.mem_toFinset.mpr hv, hd'⟩)
      rw [hNat] at hx
      exact_mod_cast hx
  rw [measure_congr hEq]
  exact measure_offspringCountCylinder hd hR interior shape.childCount

end Certificate.CanonicalTree

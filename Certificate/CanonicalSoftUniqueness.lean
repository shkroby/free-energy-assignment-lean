import Certificate.CanonicalTree
import Certificate.ArrivalSoftExchange

/-! The two extremal canonical tree recursions coalesce at positive fugacity. -/

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace Certificate.CanonicalTree

private theorem map_update {g : Environment → ℝ} (hg : Measurable g)
    {β d z : ℝ} (hβ : 0 < β) (hd : 0 < d)
    (hgb : ∀ᵐ ω ∂law, g ω ∈ Icc 0 z⁻¹) :
    (markedSpacings (law.map g)).map (arrivalSoftOutput β d z) =
      law.map (fun ω => TreeBoundary.update z (weight β d ω [])
        (fun i => g (branch i ω))) := by
  let F (ω : Environment) : ArrivalConfiguration := (ω [], fun i => g (branch i ω))
  have hF : Measurable F :=
    (measurable_pi_apply []).prodMk
      (measurable_pi_iff.mpr fun i => hg.comp (measurable_branch i))
  have hmap : law.map F = markedSpacings (law.map g) := map_root_marks hg
  rw [← hmap, Measure.map_map (measurable_arrivalSoftOutput β d z) hF]
  apply Measure.map_congr
  have hbranch : ∀ᵐ ω ∂law, ∀ i, g (branch i ω) ∈ Icc 0 z⁻¹ := by
    apply ae_all_iff.mpr
    intro i
    exact (measurePreserving_branch i).quasiMeasurePreserving.tendsto_ae.eventually hgb
  filter_upwards [hbranch, ae_summable_weight hβ hd] with ω hω hw
  have hnonneg (i : ℕ) : 0 ≤ cavityTerm β d (F ω) i :=
    mul_nonneg (weight_nonneg β d ω [] i) (hω i).1
  have hsum : Summable (cavityTerm β d (F ω)) :=
    (hw []).mul_right z⁻¹ |>.of_nonneg_of_le hnonneg
      (fun i => mul_le_mul_of_nonneg_left (hω i).2 (weight_nonneg β d ω [] i))
  change (z + (∑' i, ENNReal.ofReal (cavityTerm β d (F ω) i)).toReal)⁻¹ =
    (z + ∑' i, cavityTerm β d (F ω) i)⁻¹
  rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg hsum,
    ENNReal.toReal_ofReal (tsum_nonneg hnonneg)]

/-- The root lower and upper laws reproduce each other under the canonical
positive-fugacity arrival recursion. -/
theorem crossed_arrival_laws {β d z : ℝ} (hβ : 0 < β) (hd : 0 < d) (hz : 0 < z) :
    (markedSpacings (law.map (upper β d z []))).map (arrivalSoftOutput β d z) =
        law.map (lower β d z []) ∧
      (markedSpacings (law.map (lower β d z []))).map (arrivalSoftOutput β d z) =
        law.map (upper β d z []) := by
  have hbL : ∀ᵐ ω ∂law, lower β d z [] ω ∈ Icc 0 z⁻¹ :=
    (ae_boundary_limits hβ hd hz).mono fun _ h =>
      ⟨(h []).2.2.1.le, (h []).2.2.2.1.trans (h []).2.2.2.2.1⟩
  have hbU : ∀ᵐ ω ∂law, upper β d z [] ω ∈ Icc 0 z⁻¹ :=
    (ae_boundary_limits hβ hd hz).mono fun _ h =>
      ⟨(h []).2.2.1.le.trans (h []).2.2.2.1, (h []).2.2.2.2.1⟩
  constructor
  · rw [map_update (measurable_upper β d z []) hβ hd hbU]
    exact Measure.map_congr ((ae_root_cross_recursions hβ hd hz).mono fun _ h => h.1.symm)
  · rw [map_update (measurable_lower β d z []) hβ hd hbL]
    exact Measure.map_congr ((ae_root_cross_recursions hβ hd hz).mono fun _ h => h.2.symm)

/-- The canonical lower and upper root messages agree almost surely. -/
theorem ae_lower_eq_upper {β d z : ℝ} (hβ : 0 < β) (hd : 0 < d) (hz : 0 < z) :
    lower β d z [] =ᵐ[law] upper β d z [] := by
  let : IsProbabilityMeasure law := isProbabilityMeasure_law
  have hbounds : ∀ᵐ ω ∂law, 0 ≤ lower β d z [] ω ∧
      lower β d z [] ω ≤ upper β d z [] ω ∧ upper β d z [] ω ≤ z⁻¹ :=
    (ae_boundary_limits hβ hd hz).mono fun _ h =>
      ⟨(h []).2.2.1.le, (h []).2.2.2.1, (h []).2.2.2.2.1⟩
  have hc := crossed_arrival_laws hβ hd hz
  exact ae_eq_of_ordered_crossed_arrival_recursions law hd hβ hz
    (measurable_lower β d z []) (measurable_upper β d z []) hbounds hc.1 hc.2

/-- The two depth approximations to the canonical root message converge to
the same value almost surely. -/
theorem ae_root_depth_same_limit {β d z : ℝ} (hβ : 0 < β) (hd : 0 < d) (hz : 0 < z) :
    ∀ᵐ ω ∂law,
      Tendsto (fun n => (depth β d z n [] ω).1) atTop (𝓝 (lower β d z [] ω)) ∧
        Tendsto (fun n => (depth β d z n [] ω).2) atTop (𝓝 (lower β d z [] ω)) := by
  filter_upwards [ae_boundary_limits hβ hd hz, ae_lower_eq_upper hβ hd hz] with ω h heq
  rw [heq]
  exact ⟨heq ▸ (h []).1, (h []).2.1⟩

/-- The common extremal limit gives a positive-fugacity solution law. -/
theorem exists_soft_cavity_law {β d z : ℝ} (hβ : 0 < β) (hd : 0 < d) (hz : 0 < z) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧
      (∀ᵐ h ∂μ, h ∈ Ioc 0 z⁻¹) ∧
      (markedSpacings μ).map (arrivalSoftOutput β d z) = μ := by
  let : IsProbabilityMeasure law := isProbabilityMeasure_law
  refine ⟨law.map (lower β d z []),
    Measure.isProbabilityMeasure_map (measurable_lower β d z []).aemeasurable, ?_, ?_⟩
  · apply (ae_map_iff (measurable_lower β d z []).aemeasurable measurableSet_Ioc).2
    exact (ae_boundary_limits hβ hd hz).mono fun _ h =>
      ⟨(h []).2.2.1, (h []).2.2.2.1.trans (h []).2.2.2.2.1⟩
  · have h := (crossed_arrival_laws hβ hd hz).2
    rw [← Measure.map_congr (ae_lower_eq_upper hβ hd hz)] at h
    exact h

end Certificate.CanonicalTree

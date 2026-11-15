import Certificate.CanonicalCutoffLimit
import Certificate.CanonicalShapePartition

/-! Removing the degree cutoff on the common positive-fugacity Poisson tree. -/

open Filter MeasureTheory Set
open scoped Topology

namespace Certificate.CanonicalTree

/-- The degree of a vertex in the rooted cutoff tree counts the parent
edge whenever the vertex is reached from the root. -/
noncomputable def cutoffDegree (d R : ℝ) (ω : Environment) (v : Vertex) : ℕ :=
  cutoffOffspringNat d R (ω v) + if v = [] then 0 else 1

/-- A column's remaining degree after removing edges incident to long rows. -/
noncomputable def cutoffColumnDegree (d R : ℝ) (D : ℕ) (ω : Environment) (v : Vertex) : ℕ :=
  ((Finset.range (cutoffOffspringNat d R (ω v))).filter
    (fun i => cutoffDegree d R ω (child v i) ≤ D)).card +
      if v = [] then 0 else if cutoffDegree d R ω v.dropLast ≤ D then 1 else 0

theorem cutoffColumnDegree_le_cutoffDegree (d R : ℝ) (D : ℕ) (ω : Environment) (v : Vertex) :
    cutoffColumnDegree d R D ω v ≤ cutoffDegree d R ω v := by
  unfold cutoffColumnDegree cutoffDegree
  refine Nat.add_le_add ?_ ?_
  · exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_range _)
  · by_cases h : v = []
    · simp [h]
    · simp only [if_neg h]
      exact ite_le_one (by decide : (1 : ℕ) ≤ 1) (by decide : (0 : ℕ) ≤ 1)

/-- The root is a row. First delete edges of high-degree rows, then delete
edges of columns whose degree in the remaining graph is still too large. -/
noncomputable def trimmedWeight (β d R : ℝ) (D : ℕ) (ω : Environment) (v : Vertex) (i : ℕ) : ℝ :=
  if (if v.length % 2 = 0 then
      cutoffDegree d R ω v ≤ D ∧ cutoffColumnDegree d R D ω (child v i) ≤ D
    else cutoffDegree d R ω (child v i) ≤ D ∧ cutoffColumnDegree d R D ω v ≤ D) then
    weightFor (cutoffKernel β R) d ω v i else 0

theorem trimmedWeight_bounds (β d R : ℝ) (D : ℕ) (ω : Environment) (v : Vertex) (i : ℕ) :
    0 ≤ trimmedWeight β d R D ω v i ∧ trimmedWeight β d R D ω v i ≤
      weightFor (cutoffKernel β R) d ω v i := by
  have h : 0 ≤ weightFor (cutoffKernel β R) d ω v i := cutoffKernel_nonneg _ _ _
  unfold trimmedWeight
  split_ifs <;> first | exact ⟨h, le_rfl⟩ | exact ⟨le_rfl, h⟩

theorem tendsto_trimmedWeight (β d R : ℝ) (ω : Environment) (v : Vertex) (i : ℕ) :
    Tendsto (fun D => trimmedWeight β d R D ω v i) atTop
      (𝓝 (weightFor (cutoffKernel β R) d ω v i)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop (max (cutoffDegree d R ω v)
    (cutoffDegree d R ω (child v i)))] with D hD
  have hv := (le_max_left (cutoffDegree d R ω v) (cutoffDegree d R ω (child v i))).trans hD
  have hc := (le_max_right (cutoffDegree d R ω v) (cutoffDegree d R ω (child v i))).trans hD
  have hv' := (cutoffColumnDegree_le_cutoffDegree d R D ω v).trans hv
  have hc' := (cutoffColumnDegree_le_cutoffDegree d R D ω (child v i)).trans hc
  simp [trimmedWeight, hv, hc, hv', hc']

noncomputable def trimmedLower (β d R z : ℝ) (D : ℕ) (v : Vertex) (ω : Environment) : ℝ :=
  ⨆ k, (TreeBoundary.bounds z child (trimmedWeight β d R D ω) k v).1

noncomputable def trimmedUpper (β d R z : ℝ) (D : ℕ) (v : Vertex) (ω : Environment) : ℝ :=
  ⨅ k, (TreeBoundary.bounds z child (trimmedWeight β d R D ω) k v).2

/-- The degree-trimmed tree solutions are confined between their finite-depth
lower and upper boundaries. -/
theorem trimmedDepth_brackets {β d R z : ℝ} (hz : 0 < z) {ω : Environment}
    (hw : ∀ v, Summable (weightFor (cutoffKernel β R) d ω v)) (D k : ℕ) (v : Vertex) :
    (TreeBoundary.bounds z child (trimmedWeight β d R D ω) k v).1 ≤ trimmedLower β d R z D v ω ∧
    trimmedLower β d R z D v ω ≤ trimmedUpper β d R z D v ω ∧
    trimmedUpper β d R z D v ω ≤ (TreeBoundary.bounds z child (trimmedWeight β d R D ω) k v).2 := by
  let W := trimmedWeight β d R D ω
  have hnon (v : Vertex) (i : ℕ) : 0 ≤ W v i := (trimmedWeight_bounds β d R D ω v i).1
  have hS (v : Vertex) : Summable (W v) := Summable.of_nonneg_of_le (hnon v)
    (fun i => (trimmedWeight_bounds β d R D ω v i).2) (hw v)
  let B (j : ℕ) := TreeBoundary.bounds z child W j v
  have hB (j : ℕ) : 0 ≤ (B j).1 ∧ (B j).1 ≤ (B j).2 ∧ (B j).2 ≤ z⁻¹ :=
    TreeBoundary.bounds_mem z child W hz hS hnon j v
  have hLmono : Monotone fun j => (B j).1 :=
    monotone_nat_of_le_succ fun j => (TreeBoundary.bounds_step z child W hz hS hnon j v).1
  have hUmono : Antitone fun j => (B j).2 :=
    antitone_nat_of_succ_le fun j => (TreeBoundary.bounds_step z child W hz hS hnon j v).2
  have hL : BddAbove (Set.range fun j => (B j).1) :=
    ⟨z⁻¹, fun _ ⟨j,hj⟩ => hj ▸ (hB j).2.1.trans (hB j).2.2⟩
  have hU : BddBelow (Set.range fun j => (B j).2) :=
    ⟨0, fun _ ⟨j,hj⟩ => hj ▸ (hB j).1.trans (hB j).2.1⟩
  refine ⟨le_ciSup hL k, ?_, ciInf_le hU k⟩
  exact le_of_tendsto_of_tendsto' (tendsto_atTop_ciSup hLmono hL)
    (tendsto_atTop_ciInf hUmono hU) (fun j => (hB j).2.1)

theorem ae_cutoff_lower_eq_upper_at_vertices {β d z : ℝ} (hβ : 0 < β) (hd : 0 < d)
    (hz : 0 < z) (R : ℕ) :
    ∀ᵐ ω ∂law, ∀ v, lowerFor (cutoffKernel β R) d z v ω = upperFor (cutoffKernel β R) d z v ω := by
  apply ae_all_iff.mpr
  intro v
  induction v with
  | nil => exact ae_cutoff_lower_eq_upper hβ hd hz R
  | cons i v ih =>
    have hs := (measurePreserving_branch i).quasiMeasurePreserving.tendsto_ae.eventually ih
    filter_upwards [hs] with ω hω
    change lowerFor (cutoffKernel β R) d z v (branch i ω) =
      upperFor (cutoffKernel β R) d z v (branch i ω) at hω
    simpa only [lowerFor_branch, upperFor_branch] using hω

/-- At a fixed length cutoff, both degree-trimmed extremal messages converge
to the untrimmed cutoff solution, at all vertices of the same tree. -/
theorem ae_tendsto_trimmed_messages {β d z : ℝ} (hβ : 0 < β) (hd : 0 < d) (hz : 0 < z) (R : ℕ) :
    ∀ᵐ ω ∂law, ∀ v,
      Tendsto (fun D => trimmedLower β d R z D v ω) atTop
        (𝓝 (lowerFor (cutoffKernel β R) d z v ω)) ∧
      Tendsto (fun D => trimmedUpper β d R z D v ω) atTop
        (𝓝 (lowerFor (cutoffKernel β R) d z v ω)) := by
  let K := cutoffKernel β R
  have hS := ae_summable_cutoffKernel hβ hd R
  filter_upwards [ae_summable_weightFor hS, ae_boundary_limitsFor hz (cutoffKernel_nonneg β R) hS,
    ae_cutoff_lower_eq_upper_at_vertices hβ hd hz R] with ω hw hL hEq
  intro v
  have h1 := (hL v).1
  have h2 := (hL v).2.1
  rw [← hEq v] at h2
  refine ⟨?_,?_⟩
  · exact TreeBoundary.tendsto_of_between_weight_cutoff_bounds v _
      hz hw (fun D v i => trimmedWeight_bounds β d R D ω v i)
      (tendsto_trimmedWeight β d R ω) h1 h2 (fun D k => by
        have h := trimmedDepth_brackets hz hw D k v
        exact ⟨h.1, h.2.1.trans h.2.2⟩)
  · exact TreeBoundary.tendsto_of_between_weight_cutoff_bounds v _
      hz hw (fun D v i => trimmedWeight_bounds β d R D ω v i)
      (tendsto_trimmedWeight β d R ω) h1 h2 (fun D k => by
        have h := trimmedDepth_brackets hz hw D k v
        exact ⟨h.1.trans h.2.1, h.2.2⟩)

/-- Compare all the outgoing occupations on the common tree. -/
noncomputable def trimmedRootOccupation (β d R z : ℝ) (D : ℕ) (ω : Environment) (i : ℕ) : ℝ :=
  trimmedWeight β d R D ω [] i * trimmedUpper β d R z D [] ω *
    trimmedLower β d R z D (child [] i) ω

noncomputable def cutoffRootOccupation (β d R z : ℝ) (ω : Environment) (i : ℕ) : ℝ :=
  weightFor (cutoffKernel β R) d ω [] i * lowerFor (cutoffKernel β R) d z [] ω *
    lowerFor (cutoffKernel β R) d z (child [] i) ω

theorem ae_tendsto_trimmed_occupations {β d z : ℝ} (hβ : 0 < β) (hd : 0 < d) (hz : 0 < z) (R : ℕ) :
    ∀ᵐ ω ∂law, ∀ i, Tendsto (fun D => trimmedRootOccupation β d R z D ω i)
      atTop (𝓝 (cutoffRootOccupation β d R z ω i)) := by
  filter_upwards [ae_tendsto_trimmed_messages hβ hd hz R] with ω hω
  intro i
  exact ((tendsto_trimmedWeight β d R ω [] i).mul (hω []).2).mul (hω (child [] i)).1

/-- The length cutoffs converge on the same realization at every vertex. -/
theorem ae_tendsto_cutoff_messages {β d z : ℝ} (hβ : 0 < β) (hd : 0 < d) (hz : 0 < z) :
    ∀ᵐ ω ∂law, ∀ v,
      Tendsto (fun R : ℕ => lowerFor (cutoffKernel β R) d z v ω)
        atTop (𝓝 (lower β d z v ω)) := by
  apply ae_all_iff.mpr
  intro v
  induction v with
  | nil => exact ae_tendsto_cutoff_root hβ hd hz
  | cons i v ih =>
    have hs := (measurePreserving_branch i).quasiMeasurePreserving.tendsto_ae.eventually ih
    filter_upwards [hs] with ω hω
    change Tendsto (fun R : ℕ => lowerFor (cutoffKernel β R) d z v (branch i ω))
      atTop (𝓝 (lower β d z v (branch i ω))) at hω
    simpa only [lowerFor_branch, lower_branch] using hω

/-- A full-tree edge occupation computed in the common environment. -/
noncomputable def fullRootOccupation (β d z : ℝ) (ω : Environment) (i : ℕ) : ℝ :=
  weight β d ω [] i * lower β d z [] ω * lower β d z (child [] i) ω

theorem ae_tendsto_cutoff_occupations {β d z : ℝ} (hβ : 0 < β) (hd : 0 < d) (hz : 0 < z) :
    ∀ᵐ ω ∂law, ∀ i, Tendsto (fun R : ℕ => cutoffRootOccupation β d R z ω i)
      atTop (𝓝 (fullRootOccupation β d z ω i)) := by
  filter_upwards [ae_tendsto_cutoff_messages hβ hd hz] with ω hω
  intro i
  have hw : Tendsto (fun R : ℕ => weightFor (cutoffKernel β R) d ω [] i) atTop
      (𝓝 (weight β d ω [] i)) := by
    apply tendsto_const_nhds.congr'
    obtain ⟨R,hR⟩ := exists_nat_ge (arrivalLength d (ω []) i)
    filter_upwards [eventually_ge_atTop R] with S hS
    change Real.exp (-β * arrivalLength d (ω []) i) =
      cutoffKernel β S (arrivalLength d (ω []) i)
    exact (if_pos (hR.trans (Nat.cast_le.mpr hS))).symm
  exact (hw.mul (hω [])).mul (hω (child [] i))

end Certificate.CanonicalTree

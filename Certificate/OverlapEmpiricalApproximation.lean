import Certificate.OverlapEmpiricalIterates
import Certificate.OverlapAssignmentTilt

/-! Uniform depth errors link the empirical iterate tests to the exact BP
center and to the number of rows with fewer than three large occupations. -/

open Filter Finset MeasureTheory Set
open scoped Topology

namespace Certificate.Overlap
open OverlapBelief

private theorem abs_mean_sub_le {n : ℕ} (a b : Fin n → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (he : ∀ i, |a i - b i| ≤ ε) :
    |(∑ i, a i)/(n:ℝ) - (∑ i, b i)/(n:ℝ)| ≤ ε := by
  by_cases hn : n = 0
  · simp [hn,hε]
  · have hn' : 0 < (n:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    rw [← sub_div, abs_div, abs_of_pos hn', ← sum_sub_distrib, div_le_iff₀ hn']
    calc
      _ ≤ ∑ i, |a i - b i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : Fin n, ε := sum_le_sum fun i _ => he i
      _ = _ := by simp [nsmul_eq_mul,mul_comm]

/-- The uniform finite-iterate error used in the two row tests. -/
noncomputable def iterateOccupationError (u : ℝ) (D k : ℕ) : ℝ :=
  let A := (D:ℝ) * Real.exp 1
  (1/2) * ((contractionRate u A : ℝ)^k * (A/u^2))

theorem iterateOccupationError_nonneg (u : ℝ) (D k : ℕ) :
    0 ≤ iterateOccupationError u D k := by
  unfold iterateOccupationError
  positivity

theorem tendsto_iterateOccupationError {u : ℝ} (hu : 0 < u) (D : ℕ) :
    Tendsto (iterateOccupationError u D) atTop (𝓝 0) := by
  let A := (D:ℝ) * Real.exp 1
  have hr : (contractionRate u A : ℝ) < 1 :=
    NNReal.coe_lt_coe.mpr (contractionRate_lt_one hu (by dsimp [A]; positivity))
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one (contractionRate u A).coe_nonneg hr
  change Tendsto (fun k : ℕ => (1/2:ℝ) *
    ((contractionRate u A : ℝ)^k * (A/u^2))) atTop (𝓝 0)
  simpa only [mul_zero,zero_mul] using (h.mul_const (A/u^2)).const_mul (1/2:ℝ)

theorem incidentOccupationIterate_mem {n : ℕ} (G : WeightedGraph (Fin n ⊕ Fin n) (Fin n × Fin n))
    (u : ℝ) (k : ℕ) (v : Fin n ⊕ Fin n) (e : Fin n × Fin n) :
    incidentOccupationIterate G u k v e ∈ Icc (0:ℝ) 1 := by
  unfold incidentOccupationIterate edgeOccupation
  have hw : 0 ≤ G.weight e := G.weight_nonneg e
  exact ⟨by positivity, (div_le_one (by positivity)).mpr (le_add_of_nonneg_left zero_le_one)⟩

private theorem abs_iterate_sub_center_le {β d κ R u : ℝ} {n D k : ℕ}
    (hβ : 0 ≤ β) (hκ : 0 ≤ κ) (hu : 0 < u) (C : CostArray)
    (hC : ∀ ij, 0 ≤ C ij) (v : Fin n ⊕ Fin n) (e : Fin n × Fin n)
    (he : e ∈ OverlapBelief.incidentEdges (trimmedAssignmentGraph β d κ R n D C) v) :
    |incidentOccupationIterate (trimmedAssignmentGraph β d κ R n D C) u k v e -
      trimmedAssignmentCenter β d κ R u n D hβ hκ hu C e| ≤ iterateOccupationError u D k := by
  rw [trimmedAssignmentCenter_eq_occupation β d κ R u n D hβ hκ hu C hC e, ← Real.norm_eq_abs]
  exact norm_occIterate_sub_occupation_le _ hu (by positivity)
    (trimmedAssignment_incidentWeightBound hβ hκ hC) k he (Real.exp_pos _)

private theorem sum_center_incident_le_one {β d κ R u : ℝ} {n D : ℕ}
    (hβ : 0 ≤ β) (hκ : 0 ≤ κ) (hu : 0 < u) (C : CostArray)
    (hC : ∀ ij, 0 ≤ C ij) (v : Fin n ⊕ Fin n) :
    (∑ e ∈ OverlapBelief.incidentEdges (trimmedAssignmentGraph β d κ R n D C) v,
      trimmedAssignmentCenter β d κ R u n D hβ hκ hu C e) ≤ 1 := by
  simp_rw [trimmedAssignmentCenter_eq_occupation β d κ R u n D hβ hκ hu C hC]
  have h := occupation_slack (trimmedAssignmentGraph β d κ R n D C) hu
    (show 0 ≤ (D:ℝ)*Real.exp 1 by positivity) (trimmedAssignment_incidentWeightBound hβ hκ hC) v
  have hs : 0 ≤ u * message (trimmedAssignmentGraph β d κ R n D C) hu
      (show 0 ≤ (D:ℝ)*Real.exp 1 by positivity) (trimmedAssignment_incidentWeightBound hβ hκ hC) (v,none) :=
    mul_nonneg hu.le (Real.exp_nonneg _)
  linarith only [h,hs]

/-- The mean of the exact row square sums equals the normalized full edge
square sum, since each retained edge belongs to exactly one row. -/
theorem mean_square_center_eq {β d κ R u : ℝ} {n D : ℕ}
    (hβ : 0 ≤ β) (hκ : 0 ≤ κ) (hu : 0 < u) (C : CostArray) (hC : ∀ ij, 0 ≤ C ij) :
    let G := trimmedAssignmentGraph β d κ R n D C
    let γ := trimmedAssignmentCenter β d κ R u n D hβ hκ hu C
    (∑ i : Fin n, squareRowTest (OverlapBelief.incidentEdges G (Sum.inl i)) γ) / (n:ℝ) =
      (∑ e, (γ e)^2) / (n:ℝ) := by
  let G := trimmedAssignmentGraph β d κ R n D C
  let γ := trimmedAssignmentCenter β d κ R u n D hβ hκ hu C
  have ho : ∀ i : Fin n, squareRowTest (OverlapBelief.incidentEdges G (Sum.inl i)) γ =
      ∑ e ∈ OverlapBelief.incidentEdges G (Sum.inl i), (γ e)^2 := fun i =>
    squareRowTest_eq_of_subprobability _ _
      (fun e _ => (trimmedAssignmentCenter_mem β d κ R u n D hβ hκ hu C e).1)
      (sum_center_incident_le_one hβ hκ hu C hC _)
  change (∑ i : Fin n, squareRowTest (OverlapBelief.incidentEdges G (Sum.inl i)) γ) / (n:ℝ) =
    (∑ e, (γ e)^2) / (n:ℝ)
  simp_rw [ho, OverlapBelief.incidentEdges_eq_incident]
  congr 1
  rw [← show (∑ v ∈ assignmentRows n, ∑ e ∈ Overlap.incidentEdges G v, (γ e)^2) =
      ∑ i : Fin n, ∑ e ∈ Overlap.incidentEdges G (Sum.inl i), (γ e)^2 by
        simp only [assignmentRows, Finset.sum_map]
        rfl]
  rw [sum_incident_comm]
  trans ∑ e ∈ G.edges, (γ e)^2
  · apply sum_congr rfl
    intro e _
    have hrow : assignmentRows n ∩ G.ends e = {Sum.inl e.1} := by
      ext v
      cases v <;> simp [G,assignmentRows,trimmedAssignmentGraph,WeightedGraph.retain,
        assignmentGraph,Tree.Bipartite.ends]
    simp only [hrow,sum_singleton]
  · apply Finset.sum_subset (Finset.subset_univ _)
    intro e _ he
    have hzero : γ e = 0 := trimmedAssignmentCenter_eq_zero_off_edges
      β d κ R u n D hβ hκ hu C hC e he
    simp [hzero]

/-- The row square mean of finite iterates is uniformly close to the
normalized square sum of the exact occupations. -/
theorem abs_trimmedIterate_squareMean_sub_center_le {β d κ R u : ℝ} {n D k : ℕ}
    (hβ : 0 ≤ β) (hκ : 0 ≤ κ) (hu : 0 < u) (C : CostArray) (hC : ∀ ij, 0 ≤ C ij) :
    let γ := trimmedAssignmentCenter β d κ R u n D hβ hκ hu C
    |(∑ i, trimmedIterateRowTest β d κ R u n D k squareRowTest C i) / (n:ℝ) -
      (∑ e, (γ e)^2) / (n:ℝ)| ≤ 2*D*iterateOccupationError u D k := by
  let G := trimmedAssignmentGraph β d κ R n D C
  let γ := trimmedAssignmentCenter β d κ R u n D hβ hκ hu C
  change |(∑ i, trimmedIterateRowTest β d κ R u n D k squareRowTest C i) / (n:ℝ) -
    (∑ e, (γ e)^2) / (n:ℝ)| ≤ 2*D*iterateOccupationError u D k
  have heq : (∑ i : Fin n, squareRowTest (OverlapBelief.incidentEdges G (Sum.inl i)) γ) /
      (n:ℝ) = (∑ e, (γ e)^2) / (n:ℝ) := mean_square_center_eq hβ hκ hu C hC
  rw [← heq]
  apply abs_mean_sub_le _ _ (mul_nonneg (by positivity) (iterateOccupationError_nonneg u D k))
  intro i
  apply (abs_squareRowTest_sub_le (iterateOccupationError_nonneg u D k)
    (fun e _ => incidentOccupationIterate_mem G u k _ e)
    (fun e _ => trimmedAssignmentCenter_mem β d κ R u n D hβ hκ hu C e)
    (fun e he => abs_iterate_sub_center_le hβ hκ hu C hC _ e he)).trans
  have h := card_incident_trimmedAssignment_le β d κ R n D C (Sum.inl i)
  gcongr
  exact iterateOccupationError_nonneg u D k

/-- The majorant of a small third coordinate is also stable under finite
BP iteration, with error divided by its transition width. -/
theorem abs_trimmedIterate_smallMean_sub_center_le {β d κ R u η : ℝ} {n D k : ℕ}
    (hβ : 0 ≤ β) (hκ : 0 ≤ κ) (hu : 0 < u) (hη : 0 < η) (C : CostArray) (hC : ∀ ij, 0 ≤ C ij) :
    let G := trimmedAssignmentGraph β d κ R n D C
    let γ := trimmedAssignmentCenter β d κ R u n D hβ hκ hu C
    let P := fun s a => smallOccupationTest η (thirdOccupation s a)
    |(∑ i, trimmedIterateRowTest β d κ R u n D k P C i) / (n:ℝ) -
      (∑ i : Fin n, P (OverlapBelief.incidentEdges G (Sum.inl i)) γ) / (n:ℝ)| ≤
        iterateOccupationError u D k / η := by
  apply abs_mean_sub_le _ _ (div_nonneg (iterateOccupationError_nonneg u D k) hη.le)
  intro i
  exact abs_smallOccupationTest_sub_le hη
    (abs_thirdOccupation_sub_le (iterateOccupationError_nonneg u D k)
      (fun e he => abs_iterate_sub_center_le hβ hκ hu C hC _ e he))

/-- Counting rows with fewer than three large occupations is dominated
by the empirical mean of the continuous small-occupation test. -/
theorem badRows_fraction_le_smallCenterMean
    {β d κ R u η : ℝ} {n D : ℕ} (hβ : 0 ≤ β) (hκ : 0 ≤ κ)
    (hu : 0 < u) (hη : 0 < η) (C : CostArray) :
    let G := trimmedAssignmentGraph β d κ R n D C
    let γ := trimmedAssignmentCenter β d κ R u n D hβ hκ hu C
    (((assignmentRows n \ goodRows G (assignmentRows n) γ η).card : ℝ) / (n:ℝ)) ≤
      (∑ i : Fin n, smallOccupationTest η
        (thirdOccupation (OverlapBelief.incidentEdges G (Sum.inl i)) γ)) / (n:ℝ) := by
  classical
  let G := trimmedAssignmentGraph β d κ R n D C
  let γ := trimmedAssignmentCenter β d κ R u n D hβ hκ hu C
  let bad := (Finset.univ : Finset (Fin n)).filter
    (fun i => ¬ThreeLargeOn (OverlapBelief.incidentEdges G (Sum.inl i)) γ η)
  have hb : assignmentRows n \ goodRows G (assignmentRows n) γ η =
      bad.map ⟨Sum.inl,Sum.inl_injective⟩ := by
    ext v
    cases v <;>
      simp [assignmentRows, goodRows, bad, OverlapBelief.incidentEdges_eq_incident]
  change (((assignmentRows n \ goodRows G (assignmentRows n) γ η).card : ℝ) / (n:ℝ)) ≤ _
  rw [hb,Finset.card_map]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  calc
    _ = ∑ _i ∈ bad, (1:ℝ) := by simp [nsmul_eq_mul]
    _ = ∑ i ∈ bad, smallOccupationTest η
        (thirdOccupation (OverlapBelief.incidentEdges G (Sum.inl i)) γ) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hbad : ¬ ThreeLargeOn (OverlapBelief.incidentEdges G (Sum.inl i)) γ η :=
        (Finset.mem_filter.mp hi).2
      exact (smallOccupationTest_eq_one hη (le_of_lt (lt_of_not_ge
        (fun h => hbad ((threeLargeOn_iff_le_thirdOccupation hη).mpr h))))).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => (smallOccupationTest_mem _ _).1)

end Certificate.Overlap

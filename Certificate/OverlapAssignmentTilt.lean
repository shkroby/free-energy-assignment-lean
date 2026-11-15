import Certificate.OverlapAssignmentBelief
import Certificate.OverlapBeliefTilt
import Certificate.OverlapBeliefLimit
import Certificate.PressureNegative

/-! The deterministic Bethe tilt bound specialized to the retained
assignment graph and its measurable centers. -/

open Finset Filter MeasureTheory Set
open scoped Topology

namespace Certificate.Overlap
open OverlapBelief

/-- The left vertices of the finite square assignment graph. -/
def assignmentRows (n : ℕ) : Finset (Fin n ⊕ Fin n) :=
  Finset.univ.map ⟨Sum.inl, Sum.inl_injective⟩

@[simp] theorem card_assignmentRows (n : ℕ) : (assignmentRows n).card = n := by
  simp [assignmentRows]

private theorem card_assignmentRows_inter_ends {n : ℕ} (e : Fin n × Fin n) :
    (assignmentRows n ∩ Tree.Bipartite.ends e).card = 1 := by
  have he : assignmentRows n ∩ Tree.Bipartite.ends e = {Sum.inl e.1} := by
    ext v
    cases v <;> simp [assignmentRows, Tree.Bipartite.ends]
  rw [he, Finset.card_singleton]

/-- The canonical set of compatible roots in the degree-trimmed graph. -/
noncomputable def trimmedAssignmentGoodRoots (β d κ R : ℝ) (n D k : ℕ) (C : CostArray) :
    Finset (Fin n ⊕ Fin n) := by
  classical
  let G := trimmedAssignmentGraph β d κ R n D C
  exact G.vertices.filter (fun v => goodRoot G k v)

private theorem trimmedAssignmentGoodRoots_subset (β d κ R : ℝ) (n D k : ℕ) (C : CostArray) :
    trimmedAssignmentGoodRoots β d κ R n D k C ⊆ (trimmedAssignmentGraph β d κ R n D C).vertices := by
  classical
  unfold trimmedAssignmentGoodRoots
  exact Finset.filter_subset _ _

private theorem goodRoot_of_mem_trimmedAssignmentGoodRoots {β d κ R : ℝ} {n D k : ℕ} {C : CostArray}
    {v : Fin n ⊕ Fin n} (h : v ∈ trimmedAssignmentGoodRoots β d κ R n D k C) :
    goodRoot (trimmedAssignmentGraph β d κ R n D C) k v := by
  classical
  unfold trimmedAssignmentGoodRoots at h
  exact (Finset.mem_filter.mp h).2

/-- Local compatibility and a small fraction of rows with fewer than three
large occupations yield the retained soft tilt bound on the actual array. -/
theorem ae_trimmedAssignment_logPartition_tilt_le
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {β d κ R z η δ : ℝ} {D : ℕ}
    (hβ : 0 ≤ β) (hκ : 0 ≤ κ) (hμ : μ (Iio 0) = 0) (hz : 0 < z) (hη : 0 < η)
    (hRoots : ∀ k : ℕ, ∀ᵐ C ∂iidCosts μ,
      Tendsto (fun n : ℕ =>
        let G := trimmedAssignmentGraph β d κ R n D C
        (((G.vertices \ trimmedAssignmentGoodRoots β d κ R n D k C).card : ℝ) / (n : ℝ)))
          atTop (𝓝 0))
    (hRows : ∀ᵐ C ∂iidCosts μ, ∀ᶠ n : ℕ in atTop,
      let G := trimmedAssignmentGraph β d κ R n D C
      let γ := trimmedAssignmentCenter β d κ R z n D hβ hκ hz C
      (((assignmentRows n \ goodRows G (assignmentRows n) γ η).card : ℝ) / (n : ℝ)) ≤ δ/16)
    {a : ℝ} (ha : 0 < a) :
    ∀ᵐ C ∂iidCosts μ, ∀ᶠ n : ℕ in atTop,
      ∀ (f : Fin n × Fin n → ℝ), (∀ e, |f e| ≤ 1) → ∀ t : ℝ, |t| ≤ 1 →
        let G := trimmedAssignmentGraph β d κ R n D C
        let kept := G.edges
        let γ := trimmedAssignmentCenter β d κ R z n D hβ hκ hz C
        let u := Real.log z
        Real.log (((gibbsTiltedAssignmentGraph β d κ t n C f).retain kept
          (Finset.subset_univ _)).Z u) ≤
          Real.log (G.Z u) + t * (∑ e, f e * γ e) +
            (n : ℝ) * (16*t^2/η + 2*|t| * (δ/16) + a) := by
  let u := Real.log z
  let A := (D : ℝ) * Real.exp 1
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  obtain ⟨T,k,b,huT,hb,hBudget⟩ :=
    exists_approximation_parameters u (C := 2) hA (half_pos ha)
  filter_upwards [ae_cost_nonneg μ hμ, hRoots k, hRows] with C hC hRc hRowsC
  filter_upwards [hRc.eventually_lt_const hb, hRowsC, eventually_gt_atTop (0 : ℕ)]
    with n hnRoot hnRows hn f hf t ht
  let G := trimmedAssignmentGraph β d κ R n D C
  let good := trimmedAssignmentGoodRoots β d κ R n D k C
  let γ := trimmedAssignmentCenter β d κ R z n D hβ hκ hz C
  let hW : IncidentWeightBound G A := trimmedAssignment_incidentWeightBound hβ hκ hC
  have hWt : IncidentWeightBound (tilt G t f) A :=
    trimmedAssignment_incidentWeightBound_tilt hβ hκ hC ht hf
  have hw (e : Fin n × Fin n) (_ : e ∈ G.edges) : 0 < G.weight e := Real.exp_pos _
  have hγ : occupation G (Real.exp_pos u) hA hW = γ := by
    funext e
    have h := trimmedAssignmentCenter_eq_occupation β d κ R z n D hβ hκ hz C hC e
    simpa only [u, Real.exp_log hz] using h.symm
  have hsum : (∑ e ∈ G.edges, f e * γ e) = ∑ e, f e * γ e := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro e _ he
    change f e * trimmedAssignmentCenter β d κ R z n D hβ hκ hz C e = 0
    rw [trimmedAssignmentCenter_eq_zero_off_edges β d κ R z n D hβ hκ hz C hC e he,
      mul_zero]
  have hFin := logPartition_tilt_le G hA hW hWt hw huT hη (fun e _ => hf e)
    (assignmentRows n) (Finset.subset_univ _)
    (fun e _ => card_assignmentRows_inter_ends e) k good
    (trimmedAssignmentGoodRoots_subset β d κ R n D k C)
    (fun _ hv => goodRoot_of_mem_trimmedAssignmentGoodRoots hv)
  dsimp only at hFin
  rw [hγ, hsum, card_assignmentRows] at hFin
  have hN : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hSize : (G.vertices.card : ℝ) ≤ (2 : ℝ) * n := by
    change ((Finset.univ : Finset (Fin n ⊕ Fin n)).card : ℝ) ≤ 2 * n
    rw [Finset.card_univ, Fintype.card_sum, Fintype.card_fin, Nat.cast_add]
    linarith
  have hBad : ((G.vertices \ good).card : ℝ) ≤ b * n :=
    (div_le_iff₀ hN).mp hnRoot.le
  have hRowBad : ((assignmentRows n \ goodRows G (assignmentRows n) γ η).card : ℝ) ≤
      (δ/16) * n := (div_le_iff₀ hN).mp hnRows
  have hError := approximation_error_le huT hA k hSize hBad
  have hError' := hError.trans (mul_le_mul_of_nonneg_right hBudget.le hN.le)
  have hRowErr := mul_le_mul_of_nonneg_right hRowBad (show 0 ≤ 2*|t| by positivity)
  change Real.log ((tilt G t f).Z u) ≤ Real.log (G.Z u) + t*(∑ e, f e*γ e) +
    (n : ℝ)*(16*t^2/η + 2*|t| * (δ/16) + a)
  linarith only [hFin, hError', hRowErr]

end Certificate.Overlap

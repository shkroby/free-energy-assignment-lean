import Certificate.CanonicalCutoffPressure
import Certificate.LocalVacancyBounds

/-! The averaged finite-depth brackets for the concrete cutoff assignment graph. -/

open Finset Filter MeasureTheory Set
open scoped Topology

namespace Certificate

namespace Tree

theorem finiteRootBounds_masked_weights {V E : Type*} [DecidableEq V] [DecidableEq E]
    (ends : E → Finset V) {kept edges : Finset E} (hkeep : kept ⊆ edges)
    (w : E → ℝ) (z : ℝ) (k : ℕ) (vertices : Finset V) (v : V) :
    finiteRootBounds ends kept w z k vertices v =
      finiteRootBounds ends edges (fun e => if e ∈ kept then w e else 0) z k vertices v := by
  induction k generalizing vertices v with
  | zero => rfl
  | succ k ih =>
    let w' (e : E) := if e ∈ kept then w e else 0
    let B (e : E) := finiteRootBounds ends kept w z k (vertices.erase v) (otherEnd ends e v)
    let D (e : E) := finiteRootBounds ends edges w' z k (vertices.erase v) (otherEnd ends e v)
    have hsubset : incident ends vertices kept v ⊆ incident ends vertices edges v := by
      intro e he
      obtain ⟨he, hv, hs⟩ := mem_filter.mp he
      exact mem_filter.mpr ⟨hkeep he, hv, hs⟩
    have hsum (p : ℝ × ℝ → ℝ) :
        (∑ e ∈ incident ends vertices kept v, w e * p (B e)) =
          ∑ e ∈ incident ends vertices edges v, w' e * p (D e) := by
      rw [← Finset.sum_subset hsubset]
      · refine Finset.sum_congr rfl fun e he => ?_
        have h : e ∈ kept := (mem_filter.mp he).1
        rw [show B e = D e from ih _ _, show w' e = w e from if_pos h]
      · intro e he hs
        have hn : e ∉ kept := fun hk =>
          hs (mem_filter.mpr ⟨hk, (mem_filter.mp he).2⟩)
        rw [show w' e = 0 from if_neg hn, zero_mul]
    change ((z + ∑ e ∈ incident ends vertices kept v, w e * (B e).2)⁻¹,
        (z + ∑ e ∈ incident ends vertices kept v, w e * (B e).1)⁻¹) =
      ((z + ∑ e ∈ incident ends vertices edges v, w' e * (D e).2)⁻¹,
        (z + ∑ e ∈ incident ends vertices edges v, w' e * (D e).1)⁻¹)
    rw [hsum Prod.snd, hsum Prod.fst]

theorem measurable_finiteRootBounds {Ω V E : Type*} [MeasurableSpace Ω]
    [DecidableEq V]
    (ends : E → Finset V) (edges : Finset E) {w : Ω → E → ℝ}
    (hw : ∀ e, Measurable (fun ω => w ω e)) (z : ℝ)
    (k : ℕ) (vertices : Finset V) (v : V) :
    Measurable (fun ω => finiteRootBounds ends edges (w ω) z k vertices v) := by
  induction k generalizing vertices v with
  | zero => exact measurable_const
  | succ k ih =>
    simp only [finiteRootBounds]
    exact ((measurable_const.add (Finset.measurable_fun_sum _ fun e _ =>
      (hw e).mul (ih (vertices.erase v) (otherEnd ends e v)).snd)).inv).prodMk
      ((measurable_const.add (Finset.measurable_fun_sum _ fun e _ =>
        (hw e).mul (ih (vertices.erase v) (otherEnd ends e v)).fst)).inv)

end Tree

namespace CanonicalTree

private noncomputable def rootMean {n : ℕ} (f : Fin n ⊕ Fin n → ℝ) : ℝ :=
  (∑ v, f v) / (2 * n)

private theorem rootMean_mono {n : ℕ} {f g : Fin n ⊕ Fin n → ℝ} (h : ∀ v, f v ≤ g v) :
    rootMean f ≤ rootMean g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum fun _ _ => h _) (by positivity)

private theorem rootMean_const {n : ℕ} (hn : 0 < n) (c : ℝ) :
    rootMean (fun _ : Fin n ⊕ Fin n => c) = c := by
  unfold rootMean
  simp only [sum_const, card_univ, Fintype.card_sum, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add]
  have hn' : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  field_simp [hn']
  ring

/-- The lower and upper finite-depth cavity brackets, averaged over all roots
of the cutoff graph. -/
noncomputable def cutoffMeanRootBounds (β d κ R z : ℝ) (n k : ℕ) (C : CostArray) : ℝ × ℝ :=
  let G := cutoffAssignmentGraph β d κ R n C
  let B := Tree.finiteRootBounds G.ends G.edges G.weight z k G.vertices
  (rootMean (fun v => (B v).1), rootMean (fun v => (B v).2))

/-- The cavity message averaged over all roots of the cutoff graph. -/
noncomputable def cutoffMeanRootRatio (β d κ R z : ℝ) (n : ℕ) (C : CostArray) : ℝ :=
  let G := cutoffAssignmentGraph β d κ R n C
  rootMean (Tree.deletionRatio G.ends G.vertices G.edges G.weight z)

private theorem measurable_cutoffMeanRootBounds (β d κ R t : ℝ) (n k : ℕ) :
    Measurable (cutoffMeanRootBounds β d κ R (Real.exp t) n k) := by
  let G (C : CostArray) := cutoffAssignmentGraph β d κ R n C
  let B (v : Fin n ⊕ Fin n) (C : CostArray) := Tree.finiteRootBounds (G C).ends (G C).edges
    (G C).weight (Real.exp t) k (G C).vertices v
  have hv (v : Fin n ⊕ Fin n) : Measurable (B v) := by
    let w (C : CostArray) (e : Fin n × Fin n) :=
      if e ∈ retainedEdges d κ R n C then Real.exp (-β * edgeLength d κ n C e) else 0
    have heq : B v =
        fun C => Tree.finiteRootBounds Tree.Bipartite.ends Finset.univ (w C) (Real.exp t) k Finset.univ v :=
      funext fun C => Tree.finiteRootBounds_masked_weights _ (Finset.subset_univ _) _ _ _ _ _
    rw [heq]
    exact Tree.measurable_finiteRootBounds _ _ (measurable_masked_assignment_weight β d κ R n) _ _ _ _
  unfold cutoffMeanRootBounds rootMean
  exact ((Finset.measurable_fun_sum _ fun v _ => (hv v).fst).div_const _).prodMk
    ((Finset.measurable_fun_sum _ fun v _ => (hv v).snd).div_const _)

private theorem measurable_cutoffMeanRootRatio (β d κ R t : ℝ) (n : ℕ) :
    Measurable (cutoffMeanRootRatio β d κ R (Real.exp t) n) := by
  let Z (s : Finset (Fin n ⊕ Fin n)) (C : CostArray) (x : ℝ) :=
    Tree.monomerPartition Tree.Bipartite.ends s (retainedEdges d κ R n C)
      (fun e => Real.exp (-β * edgeLength d κ n C e)) (Real.exp x)
  have hZ (s : Finset (Fin n ⊕ Fin n)) : Measurable (fun C => Z s C t) := by
    have h : Measurable (Function.uncurry (Z s)) :=
      measurable_cutoff_assignment_partition β d κ R n s
    exact h.of_uncurry_right (y := t)
  change Measurable (fun C : CostArray => (∑ v : Fin n ⊕ Fin n, Z (Finset.univ.erase v) C t /
    Z Finset.univ C t) / (2 * n))
  exact (Finset.measurable_fun_sum _ fun v _ => (hZ (Finset.univ.erase v)).div (hZ Finset.univ)).div_const _

private theorem cutoffMeanRoot_bounds {β d κ R z : ℝ} {n : ℕ} (hn : 0 < n) (hz : 0 < z)
    (k : ℕ) (C : CostArray) :
    0 ≤ (cutoffMeanRootBounds β d κ R z n k C).1 ∧
      (cutoffMeanRootBounds β d κ R z n k C).1 ≤ cutoffMeanRootRatio β d κ R z n C ∧
      cutoffMeanRootRatio β d κ R z n C ≤ (cutoffMeanRootBounds β d κ R z n k C).2 ∧
      (cutoffMeanRootBounds β d κ R z n k C).2 ≤ z⁻¹ := by
  let G := cutoffAssignmentGraph β d κ R n C
  have hmem (v : Fin n ⊕ Fin n) : v ∈ G.vertices := Finset.mem_univ v
  have hi (v : Fin n ⊕ Fin n) :=
    Tree.finiteRootBounds_mem G.ends G.edges G.weight G.weight_nonneg hz k G.vertices v
  have hbr (v : Fin n ⊕ Fin n) :=
    Tree.deletionRatio_between_finiteRootBounds G.ends G.edges G.weight G.weight_nonneg hz G.ends_card k (hmem v)
  change 0 ≤ rootMean (fun v => (Tree.finiteRootBounds G.ends G.edges G.weight z k G.vertices v).1) ∧
    _ ∧ _ ∧ rootMean (fun v => (Tree.finiteRootBounds G.ends G.edges G.weight z k G.vertices v).2) ≤ z⁻¹
  refine ⟨?_, rootMean_mono (fun v => (hbr v).1), rootMean_mono (fun v => (hbr v).2), ?_⟩
  · rw [← rootMean_const hn 0]
    exact rootMean_mono fun v => (hi v).1
  · rw [← rootMean_const hn z⁻¹]
    exact rootMean_mono fun v => (hi v).2.2

private theorem cutoff_deficit_eq_rootMean {β d κ R t : ℝ} {n : ℕ} (hn : 0 < n) (C : CostArray) :
    (cutoffAssignmentGraph β d κ R n C).deficit t / n =
      2 * (1 - Real.exp t * cutoffMeanRootRatio β d κ R (Real.exp t) n C) := by
  let G := cutoffAssignmentGraph β d κ R n C
  have hcard : (G.vertices.card : ℝ) = 2 * n := by
    simp [G, cutoffAssignmentGraph, WeightedGraph.retain, assignmentGraph]
    ring
  let f (v : Fin n ⊕ Fin n) := Tree.deletionRatio G.ends G.vertices G.edges G.weight (Real.exp t) v
  change ((G.vertices.card : ℝ) - ∑ v : Fin n ⊕ Fin n, Real.exp t * f v) / n =
    2 * (1 - Real.exp t * ((∑ v, f v) / (2 * n)))
  rw [hcard, ← Finset.mul_sum]
  have hn' : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  field_simp [hn']

/-- For the actual cutoff iid graph, convergence of the two fixed-depth
averages suffices for convergence of its normalized expected deficit. -/
theorem tendsto_expected_cutoff_deficit_of_bracket_limits
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {β d κ : ℝ}
    (hβ : 0 < β) (hd : 0 < d) (R t : ℝ)
    (hL : ∀ k, Tendsto (fun n => ∫ C, (cutoffMeanRootBounds β d κ R (Real.exp t) n k C).1 ∂iidCosts μ)
      atTop (𝓝 (∫ ω, (depthFor (cutoffKernel β R) d (Real.exp t) k [] ω).1 ∂law)))
    (hU : ∀ k, Tendsto (fun n => ∫ C, (cutoffMeanRootBounds β d κ R (Real.exp t) n k C).2 ∂iidCosts μ)
      atTop (𝓝 (∫ ω, (depthFor (cutoffKernel β R) d (Real.exp t) k [] ω).2 ∂law))) :
    Tendsto (fun n => ∫ C, (cutoffAssignmentGraph β d κ R n C).deficit t / n ∂iidCosts μ)
      atTop (𝓝 (2 * (1 - expectedCutoffVacancy β d R t))) := by
  let : IsProbabilityMeasure (iidCosts μ) := by unfold iidCosts; infer_instance
  let z := Real.exp t
  have hz : 0 < z := Real.exp_pos t
  let A (n : ℕ) := cutoffMeanRootRatio β d κ R z (n+1)
  let L (k n : ℕ) (C : CostArray) := (cutoffMeanRootBounds β d κ R z (n+1) k C).1
  let U (k n : ℕ) (C : CostArray) := (cutoffMeanRootBounds β d κ R z (n+1) k C).2
  have hb (k n : ℕ) (C : CostArray) := cutoffMeanRoot_bounds (β := β) (d := d) (κ := κ) (R := R)
    (Nat.succ_pos n) hz k C
  have ha (n : ℕ) : Integrable (A n) (iidCosts μ) := by
    refine (integrable_const z⁻¹).mono'
      (measurable_cutoffMeanRootRatio β d κ R t (n+1)).aestronglyMeasurable (Eventually.of_forall fun C => ?_)
    rw [Real.norm_of_nonneg ((hb 0 n C).1.trans (hb 0 n C).2.1)]
    exact (hb 0 n C).2.2.1.trans (hb 0 n C).2.2.2
  have hiL (k n : ℕ) : Integrable (L k n) (iidCosts μ) := by
    refine (integrable_const z⁻¹).mono'
      (measurable_cutoffMeanRootBounds β d κ R t (n+1) k).fst.aestronglyMeasurable
      (Eventually.of_forall fun C => ?_)
    rw [Real.norm_of_nonneg (hb k n C).1]
    exact (hb k n C).2.1.trans ((hb k n C).2.2.1.trans (hb k n C).2.2.2)
  have hiU (k n : ℕ) : Integrable (U k n) (iidCosts μ) := by
    refine (integrable_const z⁻¹).mono'
      (measurable_cutoffMeanRootBounds β d κ R t (n+1) k).snd.aestronglyMeasurable
      (Eventually.of_forall fun C => ?_)
    rw [Real.norm_of_nonneg ((hb k n C).1.trans ((hb k n C).2.1.trans (hb k n C).2.2.1))]
    exact (hb k n C).2.2.2
  have hA := tendsto_expected_cutoff_ratio_of_depth_brackets (ν := fun _ => iidCosts μ) hβ hd hz R
    ha hiL hiU (fun k => Eventually.of_forall fun n => Eventually.of_forall fun C =>
      ⟨(hb k n C).2.1, (hb k n C).2.2.1⟩)
    (fun k => (hL k).comp (tendsto_add_atTop_nat 1)) (fun k => (hU k).comp (tendsto_add_atTop_nat 1))
  have hm := ((hA.const_mul z).const_sub 1).const_mul 2
  rw [expectedCutoffVacancy, integral_const_mul]
  apply (tendsto_add_atTop_iff_nat 1).mp
  refine hm.congr' ?_
  filter_upwards with n
  simp_rw [cutoff_deficit_eq_rootMean (Nat.succ_pos n)]
  rw [integral_const_mul, integral_sub (integrable_const (1 : ℝ)) ((ha n).const_mul _),
    integral_const, probReal_univ, one_smul, integral_const_mul]

end CanonicalTree
end Certificate

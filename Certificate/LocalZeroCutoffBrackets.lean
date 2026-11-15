import Certificate.LocalAssignmentBracketLimits
import Certificate.LocalExplorationMarks
import Certificate.CavityPrefixTail

/-!
# The zero-length cutoff

The small-cost assumption rules out zero costs almost surely, and the
canonical arrivals have strictly positive lengths. Both zero-cutoff
brackets are therefore the empty-neighborhood brackets.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace Certificate.CanonicalTree

private noncomputable def emptyRootBracket (z : ℝ) : ℕ → ℝ × ℝ
  | 0 => (0, z⁻¹)
  | _ + 1 => (z⁻¹, z⁻¹)

private theorem ae_positive_cost_array {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {d κ : ℝ} (hd : 0 < d) (hκ : 0 < κ) (hμ : SmallCostTail μ κ d) :
    ∀ᵐ C ∂iidCosts μ, ∀ e, 0 < C e := by
  have hZero : μ (Iic 0) = 0 := by
    rw [← ofReal_cdf, LocalExploration.cdf_zero_of_smallCostTail hd hκ hμ, ENNReal.ofReal_zero]
  have hp : ∀ᵐ x ∂μ, 0 < x := by
    apply ae_iff.mpr
    have hSet : {x : ℝ | ¬ 0 < x} = Iic 0 := by ext x; simp
    rwa [hSet]
  apply ae_all_iff.mpr
  intro e
  exact (measurePreserving_eval_infinitePi
    (fun _ : ℕ × ℕ => μ) e).quasiMeasurePreserving.tendsto_ae.eventually hp

private theorem zero_cutoffMeanRootBounds_eq {β d κ z : ℝ} {n : ℕ} (hκ : 0 < κ)
    (hn : 0 < n) (k : ℕ) (C : CostArray) (hC : ∀ e, 0 < C e) :
    cutoffMeanRootBounds β d κ 0 z n k C = emptyRootBracket z k := by
  let G := cutoffAssignmentGraph β d κ 0 n C
  have hs : 0 < lengthScale d κ n :=
    Real.rpow_pos_of_pos (mul_pos hκ (Nat.cast_pos.mpr hn)) _
  have hEdges : G.edges = ∅ := by
    ext e
    change e ∈ retainedEdges d κ 0 n C ↔ e ∈ (∅ : Finset (Fin n × Fin n))
    simp only [Finset.notMem_empty, iff_false]
    intro h
    have hle := (Finset.mem_filter.mp h).2
    exact (not_le.mpr (mul_pos hs (hC (e.1.val,e.2.val)))) hle
  have hBounds (v : Fin n ⊕ Fin n) :
      Tree.finiteRootBounds G.ends G.edges G.weight z k G.vertices v = emptyRootBracket z k := by
    rw [hEdges]
    cases k <;> simp [Tree.finiteRootBounds, Tree.incident, emptyRootBracket]
  change ((∑ v : Fin n ⊕ Fin n, (Tree.finiteRootBounds G.ends G.edges G.weight z k G.vertices v).1) /
      (2 * n),
    (∑ v : Fin n ⊕ Fin n, (Tree.finiteRootBounds G.ends G.edges G.weight z k G.vertices v).2) /
      (2 * n)) = emptyRootBracket z k
  have hcard (a : ℝ) : (∑ _ : Fin n ⊕ Fin n, a) / (2 * n) = a := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_sum, Fintype.card_fin, nsmul_eq_mul,
      ← two_mul]
    have hN : (2 : ℝ) * (n : ℝ) ≠ 0 :=
      mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr hn.ne')
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using mul_div_cancel_left₀ a hN
  simp only [hBounds, hcard]

private theorem ae_zero_depthFor_eq (β d z : ℝ) (k : ℕ) :
    ∀ᵐ ω ∂law, depthFor (cutoffKernel β 0) d z k [] ω = emptyRootBracket z k := by
  let : IsProbabilityMeasure exponentialSpacings := isProbabilityMeasure_exponentialSpacings
  have hp : ∀ᵐ ω ∂law, ∀ v : Vertex, ∀ j, 0 < ω v j := by
    apply ae_all_iff.mpr
    intro v
    exact (measurePreserving_eval_infinitePi
      (fun _ : Vertex => exponentialSpacings) v).quasiMeasurePreserving.tendsto_ae.eventually ae_expSpacing_pos
  filter_upwards [hp] with ω hω
  have hW : weightFor (cutoffKernel β 0) d ω = fun _ _ => 0 := by
    funext v i
    change cutoffKernel β 0 (arrivalLength d (ω v) i) = 0
    exact if_neg (not_le.mpr (arrivalLength_pos_of_positive_spacings (hω v) i))
  rw [depthFor, hW]
  cases k <;> simp [TreeBoundary.bounds, TreeBoundary.update, emptyRootBracket]

/-- At cutoff zero and every finite depth, the expected root brackets
agree with the canonical limit. -/
theorem tendsto_zero_cutoffMeanRootBounds {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {β d κ : ℝ} (hd : 0 < d) (hκ : 0 < κ) (hμ : SmallCostTail μ κ d) (k : ℕ) (t : ℝ) :
    Tendsto (fun n => ∫ C, (cutoffMeanRootBounds β d κ 0 (Real.exp t) n k C).1 ∂iidCosts μ)
        atTop (𝓝 (∫ ω, (depthFor (cutoffKernel β 0) d (Real.exp t) k [] ω).1 ∂law)) ∧
      Tendsto (fun n => ∫ C, (cutoffMeanRootBounds β d κ 0 (Real.exp t) n k C).2 ∂iidCosts μ)
        atTop (𝓝 (∫ ω, (depthFor (cutoffKernel β 0) d (Real.exp t) k [] ω).2 ∂law)) := by
  let : IsProbabilityMeasure law := isProbabilityMeasure_law
  let : IsProbabilityMeasure (iidCosts μ) := by unfold iidCosts; infer_instance
  let z := Real.exp t
  have hOne (pr : ℝ × ℝ → ℝ) :
      Tendsto (fun n => ∫ C, pr (cutoffMeanRootBounds β d κ 0 z n k C) ∂iidCosts μ)
        atTop (𝓝 (∫ ω, pr (depthFor (cutoffKernel β 0) d z k [] ω) ∂law)) := by
    have hEq := integral_congr_ae ((ae_zero_depthFor_eq β d z k).mono fun _ h => congrArg pr h)
    rw [hEq]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hEq' := integral_congr_ae ((ae_positive_cost_array hd hκ hμ).mono
      (fun C hC => congrArg pr (zero_cutoffMeanRootBounds_eq (β := β) (d := d) (z := z) hκ hn k C hC)))
    rw [hEq', integral_const, integral_const, probReal_univ, probReal_univ, one_smul]
  exact ⟨hOne Prod.fst, hOne Prod.snd⟩

end Certificate.CanonicalTree

import Certificate.SoftCutoff
import Certificate.TreeBipartite
import Certificate.CostWeightTail
import Mathlib.Data.ENNReal.BigOperators

/-!
# The scaled array and its length cutoff

The finite omitted-edge pressure bound and the one-edge Stieltjes tail bound
apply to the same complete bipartite cost model. The resulting expected gap
has a bound uniform in graph size.
-/

open Finset Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace Certificate

/-- The concrete scaled length of an edge of the complete bipartite graph. -/
noncomputable def edgeLength (d κ : ℝ) (n : ℕ) (C : CostArray) (ij : Fin n × Fin n) : ℝ :=
  lengthScale d κ n * C (ij.1.val, ij.2.val)

/-- The complete weighted graph for the square random assignment problem. -/
noncomputable def assignmentGraph (β d κ : ℝ) (n : ℕ) (C : CostArray) :
    WeightedGraph (Fin n ⊕ Fin n) (Fin n × Fin n) where
  vertices := univ
  edges := univ
  ends := Tree.Bipartite.ends
  weight := fun ij => Real.exp (-β * edgeLength d κ n C ij)
  weight_nonneg := fun _ => Real.exp_nonneg _
  ends_card := fun e _ => Tree.Bipartite.ends_card e
  ends_subset := fun _ _ => Finset.subset_univ _

/-- The positive-fugacity assignment pressure for the actual, unclamped array. -/
noncomputable def softAssignmentPressure (β d κ t : ℝ) (n : ℕ) (C : CostArray) : ℝ :=
  Real.log ((assignmentGraph β d κ n C).Z t) / n

noncomputable def retainedEdges (d κ R : ℝ) (n : ℕ) (C : CostArray) :
    Finset (Fin n × Fin n) := univ.filter fun e => edgeLength d κ n C e ≤ R

/-- The difference between the log pressure per row and its length-cutoff
counterpart, evaluated at log fugacity `t`. -/
noncomputable def cutoffPressureGap (β d κ R t : ℝ) (n : ℕ) (C : CostArray) : ℝ :=
  let G := assignmentGraph β d κ n C
  let Gcut := G.retain (retainedEdges d κ R n C) (Finset.subset_univ _)
  Real.log (G.Z t) / n - Real.log (Gcut.Z t) / n

private theorem cutoffPressureGap_le (β d κ R t : ℝ) {n : ℕ} (hn : 0 < n) (C : CostArray) :
    0 ≤ cutoffPressureGap β d κ R t n C ∧
      cutoffPressureGap β d κ R t n C ≤
        ((∑ ij : Fin n × Fin n,
          if R < edgeLength d κ n C ij then Real.exp (-β * edgeLength d κ n C ij) else 0) / n) *
          Real.exp (-2 * t) := by
  classical
  let G := assignmentGraph β d κ n C
  let kept := retainedEdges d κ R n C
  have hkept : kept ⊆ G.edges := Finset.subset_univ _
  have hEdges : G.edges \ kept = univ.filter fun e => R < edgeLength d κ n C e := by
    ext e
    simp [G, kept, assignmentGraph, retainedEdges, not_le]
  have h := G.pressure_sub_pressure_retain_le kept hkept t n (Nat.cast_pos.mpr hn)
  rw [hEdges, Finset.sum_filter] at h
  exact h

theorem cutoffPressureGap_nonneg (β d κ R t : ℝ) {n : ℕ} (hn : 0 < n) (C : CostArray) :
    0 ≤ cutoffPressureGap β d κ R t n C :=
  (cutoffPressureGap_le β d κ R t hn C).1

/-- The expectation of the nonnegative cutoff gap is bounded by the gamma
tail at the length cutoff, uniformly over all positive graph sizes. -/
theorem lintegral_cutoffPressureGap_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {κ d β : ℝ} (hκ : 0 < κ) (hd : 0 < d) (hβ : 0 < β) (hμ : SmallCostTail μ κ d) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 0 < n → ∀ R : ℝ, 0 ≤ R → ∀ t : ℝ,
      (∫⁻ C, ENNReal.ofReal (cutoffPressureGap β d κ R t n C) ∂iidCosts μ) ≤
        ENNReal.ofReal (K * Real.exp (-2 * t)) *
          ∫⁻ x : ℝ in Ioi R, ENNReal.ofReal (β * x ^ d * Real.exp (-β * x)) := by
  obtain ⟨K, hK, htail⟩ := scaled_costWeight_tail_le hκ hd hβ hμ
  refine ⟨K, hK, fun n hn R hR t => ?_⟩
  classical
  let long : Set ℝ := {c | R < lengthScale d κ n * c}
  let f : ℝ → ℝ≥0∞ := long.indicator fun c => ENNReal.ofReal (Real.exp (-β * (lengthScale d κ n * c)))
  let I := ∫⁻ x : ℝ in Ioi R, ENNReal.ofReal (β * x ^ d * Real.exp (-β * x))
  let a := Real.exp (-2 * t) / (n : ℝ)
  have hlong : MeasurableSet long := measurableSet_lt measurable_const (by fun_prop)
  have hf : Measurable f := Measurable.indicator (by fun_prop) hlong
  have hbound : (∫⁻ c, f c ∂μ) ≤ ENNReal.ofReal (K / n) * I := by
    dsimp only [f]
    rw [lintegral_indicator hlong]
    refine le_trans ?_ (htail n hn R hR)
    exact lintegral_mono_set (show long ⊆ {c : ℝ | R ≤ lengthScale d κ n * c} from
      fun c hc => (show R < lengthScale d κ n * c from hc).le)
  let idx (e : Fin n × Fin n) : ℕ × ℕ := (e.1.val,e.2.val)
  have hev (e : Fin n × Fin n) : Measurable (fun C : CostArray => C (idx e)) :=
    measurable_pi_apply _
  have hintegral_eval (e : Fin n × Fin n) :
      ∫⁻ C, f (C (idx e)) ∂iidCosts μ = ∫⁻ c, f c ∂μ := by
    rw [← lintegral_map hf (hev e)]
    rw [show (iidCosts μ).map (fun C => C (idx e)) = μ from
      Measure.infinitePi_map_eval (fun _ : ℕ × ℕ => μ) (idx e)]
  have hnorm : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hcalc (C : CostArray) :
      ENNReal.ofReal (cutoffPressureGap β d κ R t n C) ≤
        ENNReal.ofReal a * ∑ e : Fin n × Fin n, f (C (idx e)) := by
    apply (ENNReal.ofReal_le_ofReal ((cutoffPressureGap_le β d κ R t hn C).2)).trans_eq
    let W (e : Fin n × Fin n) :=
      if R < edgeLength d κ n C e then Real.exp (-β * edgeLength d κ n C e) else 0
    have hW (e : Fin n × Fin n) : 0 ≤ W e := by dsimp only [W]; split <;> positivity
    change ENNReal.ofReal ((∑ e, W e) / n * Real.exp (-2 * t)) = _
    rw [show (∑ e, W e) / n * Real.exp (-2 * t) = a * ∑ e, W e by
      dsimp only [a]; ring, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_sum_of_nonneg (fun _ _ => hW _)]
    congr 1
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases he : R < edgeLength d κ n C e
    · have hx : C (idx e) ∈ long := he
      change ENNReal.ofReal (if R < edgeLength d κ n C e
        then Real.exp (-β * edgeLength d κ n C e) else 0) =
        long.indicator _ (C (idx e))
      rw [if_pos he, Set.indicator_of_mem hx]
      rfl
    · have hx : C (idx e) ∉ long := he
      change ENNReal.ofReal (if R < edgeLength d κ n C e
        then Real.exp (-β * edgeLength d κ n C e) else 0) =
        long.indicator _ (C (idx e))
      rw [if_neg he, Set.indicator_of_notMem hx, ENNReal.ofReal_zero]
  calc
    (∫⁻ C, ENNReal.ofReal (cutoffPressureGap β d κ R t n C) ∂iidCosts μ) ≤
        ∫⁻ C, ENNReal.ofReal a * ∑ e : Fin n × Fin n, f (C (idx e)) ∂iidCosts μ :=
      lintegral_mono hcalc
    _ = ENNReal.ofReal a * ∑ e : Fin n × Fin n, ∫⁻ C, f (C (idx e)) ∂iidCosts μ := by
      have hm : Measurable (fun C : CostArray => ∑ e : Fin n × Fin n, f (C (idx e))) :=
        Finset.measurable_fun_sum _ (fun e _ => hf.comp (hev e))
      rw [lintegral_const_mul _ hm]
      exact congrArg (fun q : ℝ≥0∞ => ENNReal.ofReal a * q)
        (lintegral_finsetSum (μ := iidCosts μ) (f := fun e C => f (C (idx e)))
          Finset.univ (fun e _ => hf.comp (hev e)))
    _ ≤ ENNReal.ofReal a * ∑ _e : Fin n × Fin n, ENNReal.ofReal (K / n) * I := by
      gcongr with e
      exact (hintegral_eval e).trans_le hbound
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, ← mul_assoc,
        ← ENNReal.ofReal_natCast (n * n), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      dsimp only [a]
      push_cast
      field_simp [hnorm.ne']

end Certificate

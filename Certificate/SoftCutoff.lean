import Certificate.SoftPressure

/-!
# Removing a cutoff in the monomer pressure

The finite perturbation bound applies to any choice of retained edges.
A uniform omitted-weight estimate then transfers cutoff pressure limits to
the original graphs.
-/

open Finset Filter Set MeasureTheory
open scoped BigOperators Topology

namespace Certificate

namespace WeightedGraph

variable {V E : Type*} (G : WeightedGraph V E)

def retain (kept : Finset E) (hkept : kept ⊆ G.edges) : WeightedGraph V E where
  vertices := G.vertices
  edges := kept
  ends := G.ends
  weight := G.weight
  weight_nonneg := G.weight_nonneg
  ends_card e he := G.ends_card e (hkept he)
  ends_subset e he := G.ends_subset e (hkept he)

/-- The finite log partition changes by at most the omitted edge weight
divided by the square of the monomer factor. -/
theorem logZ_sub_logZ_retain_le [DecidableEq E]
    (kept : Finset E) (hkept : kept ⊆ G.edges) (t : ℝ) :
    0 ≤ Real.log (G.Z t) - Real.log ((G.retain kept hkept).Z t) ∧
      Real.log (G.Z t) - Real.log ((G.retain kept hkept).Z t) ≤
        (∑ e ∈ G.edges \ kept, G.weight e) * Real.exp (-2 * t) := by
  classical
  have h := Tree.log_partition_restore_edges_le G.ends G.vertices kept (G.edges \ kept)
    Finset.disjoint_sdiff (G.activity t) (G.activity_nonneg t)
    (fun e he => G.ends_subset e (mem_sdiff.mp he).1)
    (fun e he => card_pos.mp (by rw [G.ends_card e (mem_sdiff.mp he).1]; decide))
  rw [union_sdiff_of_subset hkept] at h
  have heq : Real.log (G.Z t) - Real.log ((G.retain kept hkept).Z t) =
      G.logCorrected t - (G.retain kept hkept).logCorrected t := by
    simp only [logCorrected, retain]
    ring
  rw [heq, G.logCorrected_eq, WeightedGraph.logCorrected_eq]
  let changeInPressure :=
    Real.log (Tree.partition G.ends G.vertices G.edges (G.activity t)) -
      Real.log (Tree.partition G.ends G.vertices kept (G.activity t))
  change 0 ≤ changeInPressure ∧
    changeInPressure ≤ (∑ e ∈ G.edges \ kept, G.weight e) * Real.exp (-2 * t)
  rw [Finset.sum_mul]
  exact h

/-- The normalized pressure difference satisfies the same bound with edge
weight per unit of size. -/
theorem pressure_sub_pressure_retain_le [DecidableEq E]
    (kept : Finset E) (hkept : kept ⊆ G.edges) (t mass : ℝ) (hmass : 0 < mass) :
    0 ≤ Real.log (G.Z t) / mass - Real.log ((G.retain kept hkept).Z t) / mass ∧
      Real.log (G.Z t) / mass - Real.log ((G.retain kept hkept).Z t) / mass ≤
        ((∑ e ∈ G.edges \ kept, G.weight e) / mass) * Real.exp (-2 * t) := by
  rw [← sub_div, mul_comm (_ / mass), ← mul_div_assoc,
    mul_comm (Real.exp (-2 * t))]
  exact ⟨div_nonneg (G.logZ_sub_logZ_retain_le kept hkept t).1 hmass.le,
    (div_le_div_iff_of_pos_right hmass).mpr (G.logZ_sub_logZ_retain_le kept hkept t).2⟩

end WeightedGraph

/-- Uniform approximation by cutoff pressures transfers their limits to
the original pressure sequence. -/
theorem tendsto_of_uniform_pressure_cutoff
    {p : ℕ → ℝ} {pCut : ℕ → ℕ → ℝ} {lCut error : ℕ → ℝ} {l : ℝ}
    (hCut : ∀ R, Tendsto (pCut R) atTop (𝓝 (lCut R)))
    (hlim : Tendsto lCut atTop (𝓝 l))
    (herror : Tendsto error atTop (𝓝 0))
    (happrox : ∀ R, ∀ᶠ n in atTop, |p n - pCut R n| ≤ error R) :
    Tendsto p atTop (𝓝 l) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hthird : 0 < ε / 3 := by positivity
  obtain ⟨a, ha⟩ := Metric.tendsto_atTop.mp hlim (ε / 3) hthird
  obtain ⟨b, hb⟩ := Metric.tendsto_atTop.mp herror (ε / 3) hthird
  let R := max a b
  obtain ⟨c, hc⟩ := Metric.tendsto_atTop.mp (hCut R) (ε / 3) hthird
  obtain ⟨d, hd⟩ := eventually_atTop.mp (happrox R)
  refine ⟨max c d, fun n hn => ?_⟩
  have h₁ : dist (p n) (pCut R n) < ε / 3 := by
    rw [Real.dist_eq]
    have hbound := hd n ((le_max_right c d).trans hn)
    exact hbound.trans_lt ((le_abs_self (error R)).trans_lt
      (by simpa [Real.dist_eq] using hb R (le_max_right a b)))
  have h₂ : dist (pCut R n) (lCut R) < ε / 3 := hc n ((le_max_left c d).trans hn)
  have h₃ : dist (lCut R) l < ε / 3 := ha R (le_max_left a b)
  have hdist := (dist_triangle (p n) (pCut R n) l).trans
    (add_le_add (le_refl (dist (p n) (pCut R n))) (dist_triangle (pCut R n) (lCut R) l))
  linarith only [h₁, h₂, h₃, hdist]

end Certificate

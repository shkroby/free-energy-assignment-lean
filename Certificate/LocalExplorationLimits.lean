import Certificate.LocalExplorationRoots
import Mathlib.Tactic.FieldSimp

/-!
# Independent Poisson counts at finitely many exposed roots

Removing a fixed number of labels does not change the limiting offspring
count. The count events considered here concern prescribed exposed roots.
-/

open Filter Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators Topology ENNReal

namespace Certificate.LocalExploration

/-- The Poisson limit still holds when a fixed number of trials are excluded. -/
theorem tendsto_shortEdge_binomial_mass_with_exclusions {μ : Measure ℝ}
    {d κ R : ℝ} (k skip : ℕ) (hd : 0 < d) (hκ : 0 < κ) (hR : 0 < R)
    (h : SmallCostTail μ κ d) :
    Tendsto (fun n : ℕ => ((n - skip).choose k : ℝ) *
      (shortEdgeProbability μ d κ R n) ^ k *
      (1 - shortEdgeProbability μ d κ R n) ^ ((n - skip) - k)) atTop
      (𝓝 (Real.exp (-(R ^ d)) * (R ^ d) ^ k / k.factorial)) := by
  let p (m : ℕ) := shortEdgeProbability μ d κ R (m + skip)
  have hsize : Tendsto (fun m : ℕ => ((m + skip : ℕ) : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat skip)
  have hshift : Tendsto (fun m : ℕ => ((m + skip : ℕ) : ℝ) * p m) atTop (𝓝 (R ^ d)) :=
    (tendsto_scaled_shortEdgeProbability hd hκ hR h).comp (tendsto_add_atTop_nat skip)
  have hp : Tendsto p atTop (𝓝 0) := by
    refine (hshift.div_atTop hsize).congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
    change ((↑(m + skip : ℕ) : ℝ) * p m) / (↑(m + skip : ℕ) : ℝ) = p m
    have hn : (m + skip : ℕ) ≠ 0 := by omega
    exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hn)
  have hm : Tendsto (fun m : ℕ => (m : ℝ) * p m) atTop (𝓝 (R ^ d)) := by
    simpa only [Nat.cast_add, mul_zero, sub_zero, ← sub_mul, add_sub_cancel_right] using
      hshift.sub (hp.const_mul (skip : ℝ))
  have hbin := (tendsto_choose_mul_pow_of_tendsto_mul_atTop k hm).comp (tendsto_sub_atTop_nat skip)
  refine hbin.congr' ?_
  filter_upwards [eventually_ge_atTop skip] with n hn
  simp [p, Nat.sub_add_cancel hn]

/-- As the square matrix grows, the joint law of the counts at any fixed
finite family of exposed roots converges on each count vector to the
product of Poisson masses. Each root may exclude a different fixed
number of available neighboring labels. -/
theorem tendsto_measure_rootCounts_eq {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {ρ : Type*} [Fintype ρ] {d κ R : ℝ}
    (hd : 0 < d) (hκ : 0 < κ) (hR : 0 < R) (h : SmallCostTail μ κ d)
    (roots : ρ ↪ Vertex) (skip : ρ → ℕ)
    (labels : ∀ n (u : ρ), Fin (n - skip u) ↪ ℕ)
    (havoid : ∀ n u (i : Fin (n - skip u)) v,
      roots v ≠ oppositeVertex (roots u) (labels n u i)) (k : ρ → ℕ) :
    Tendsto (fun n : ℕ =>
      (iidCosts μ {C | rootCounts roots (labels n) d κ R n C = k}).toReal) atTop
      (𝓝 (∏ u, Real.exp (-(R ^ d)) * (R ^ d) ^ k u / (k u).factorial)) := by
  have hl := tendsto_finsetProd (s := (Finset.univ : Finset ρ))
    (fun u _ => tendsto_shortEdge_binomial_mass_with_exclusions (k u) (skip u) hd hκ hR h)
  refine hl.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  rw [measure_rootCounts_eq μ roots (labels n) (havoid n) d κ R n k]
  let ν := scaledLengthLaw μ d κ n
  let : IsProbabilityMeasure ν := isProbabilityMeasure_scaledLengthLaw μ d κ n
  let p := shortEdgeProbability μ d κ R n
  have hp₀ : 0 ≤ p := cdf_nonneg μ _
  have hp₁ : p ≤ 1 := cdf_le_one μ _
  have hret : ν (Iic R) = ENNReal.ofReal p := scaledLengthLaw_Iic hκ hn R
  have habs : ν (Ioi R) = ENNReal.ofReal (1 - p) := by
    rw [← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, hret,
      ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hp₀]
  change (∏ u, (((n - skip u).choose (k u)) : ℝ) * p ^ k u *
      (1 - p) ^ (n - skip u - k u)) = (∏ u, (↑((Fintype.card (Fin (n - skip u))).choose (k u)) : ℝ≥0∞) *
        ν (Iic R) ^ k u * ν (Ioi R) ^ (Fintype.card (Fin (n - skip u)) - k u)).toReal
  simp [hret, habs, ENNReal.toReal_prod, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hp₀, ENNReal.toReal_ofReal (sub_nonneg.mpr hp₁)]

/-- The first `r` rows and `c` columns are the prescribed roots. -/
def canonicalRoots (r c : ℕ) : (Fin r ⊕ Fin c) ↪ Vertex where
  toFun := Sum.map Fin.val Fin.val
  inj' := by
    rintro (i | j) (i' | j') h
    · exact congrArg Sum.inl (Fin.ext (Sum.inl.inj h))
    · exact (Sum.inl_ne_inr h).elim
    · exact (Sum.inr_ne_inl h).elim
    · exact congrArg Sum.inr (Fin.ext (Sum.inr.inj h))

/-- The number of excluded opposite labels for a canonical root. -/
def canonicalSkip (r c : ℕ) : Fin r ⊕ Fin c → ℕ
  | .inl _ => c
  | .inr _ => r

/-- The available labels, namely all labels in the opposite class after the roots. -/
def canonicalLabels (r c n : ℕ) (u : Fin r ⊕ Fin c) : Fin (n - canonicalSkip r c u) ↪ ℕ where
  toFun := fun i => canonicalSkip r c u + i.val
  inj' := fun _ _ h => Fin.ext (Nat.add_left_cancel h)

theorem canonicalLabels_lt {r c n : ℕ} {u : Fin r ⊕ Fin c}
    (i : Fin (n - canonicalSkip r c u)) : canonicalLabels r c n u i < n := by
  have hi := i.isLt
  change canonicalSkip r c u + i.val < n
  omega

theorem canonicalLabels_avoid (r c n : ℕ) (u : Fin r ⊕ Fin c)
    (i : Fin (n - canonicalSkip r c u)) (v : Fin r ⊕ Fin c) :
    canonicalRoots r c v ≠ oppositeVertex (canonicalRoots r c u) (canonicalLabels r c n u i) := by
  rcases u with u | u <;> rcases v with v | v
  · exact Sum.inl_ne_inr
  · intro he
    have h := Sum.inr.inj he
    change v.val = c + i.val at h
    have hv := v.isLt
    omega
  · intro he
    have h := Sum.inl.inj he
    change v.val = r + i.val at h
    have hv := v.isLt
    omega
  · exact Sum.inr_ne_inl

/-- Counts at fixed row and column roots, with all connecting root-root edges
deleted, converge jointly to independent Poisson counts. -/
theorem tendsto_canonicalRootCounts_eq {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {d κ R : ℝ} (hd : 0 < d) (hκ : 0 < κ) (hR : 0 < R) (h : SmallCostTail μ κ d)
    (r c : ℕ) (k : Fin r ⊕ Fin c → ℕ) :
    Tendsto (fun n : ℕ =>
      (iidCosts μ {C | rootCounts (canonicalRoots r c) (canonicalLabels r c n) d κ R n C = k}).toReal)
      atTop (𝓝 (∏ u, Real.exp (-(R ^ d)) * (R ^ d) ^ k u / (k u).factorial)) :=
  tendsto_measure_rootCounts_eq hd hκ hR h (canonicalRoots r c) (canonicalSkip r c)
    (canonicalLabels r c) (canonicalLabels_avoid r c) k

end Certificate.LocalExploration

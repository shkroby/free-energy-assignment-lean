import Certificate.LocalExplorationHistory

/-!
# Bounds for the number of prescribed short paths

The retention probability of a path with distinct entries is the product
of its edge probabilities. This bounds the expected number of retained
paths uniformly when the number of possible paths has the usual power growth.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

namespace Certificate.LocalExploration

/-- The array event specifying that all entries of a path satisfy one
measurable cost constraint. -/
def retainedPathEvent {k : ℕ} (path : Fin k ↪ ℕ × ℕ) (A : Set ℝ) : Set CostArray :=
  observedCosts path ⁻¹' univ.pi (fun _ ↦ A)

theorem measurableSet_retainedPathEvent {k : ℕ} (path : Fin k ↪ ℕ × ℕ)
    {A : Set ℝ} (hA : MeasurableSet A) :
    MeasurableSet (retainedPathEvent path A) :=
  measurable_observedCosts path (MeasurableSet.univ_pi (fun _ ↦ hA))

theorem measure_retainedPathEvent {k : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (path : Fin k ↪ ℕ × ℕ) {A : Set ℝ} (hA : MeasurableSet A) :
    iidCosts μ (retainedPathEvent path A) = (μ A) ^ k := by
  unfold retainedPathEvent
  rw [← Measure.map_apply (measurable_observedCosts path) (MeasurableSet.univ_pi (fun _ ↦ hA)),
    observedCosts_law μ path, Measure.infinitePi_eq_pi, Measure.pi_pi]
  simp

/-- Count retained paths in a prescribed finite family of paths with
distinct entries. The path events may be strongly dependent. -/
noncomputable def retainedPathFamilyCount {I : Type*} [Fintype I] {k : ℕ}
    (paths : I → (Fin k ↪ ℕ × ℕ)) (A : Set ℝ) (C : CostArray) : ℝ :=
  ∑ i : I, (retainedPathEvent (paths i) A).indicator (fun _ ↦ (1 : ℝ)) C

theorem integral_retainedPathFamilyCount {I : Type*} [Fintype I] {k : ℕ}
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (paths : I → (Fin k ↪ ℕ × ℕ))
    {A : Set ℝ} (hA : MeasurableSet A) :
    (∫ C, retainedPathFamilyCount paths A C ∂iidCosts μ) =
      (Fintype.card I : ℝ) * (μ.real A) ^ k := by
  let : IsProbabilityMeasure (iidCosts μ) := by unfold iidCosts; infer_instance
  unfold retainedPathFamilyCount
  rw [integral_finsetSum (Finset.univ : Finset I) (fun i _ ↦
    (integrable_const (1 : ℝ)).indicator (measurableSet_retainedPathEvent (paths i) hA))]
  calc
    _ = ∑ _i : I, (μ.real A) ^ k := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show (∫ a, (retainedPathEvent (paths i) A).indicator (fun _ ↦ (1 : ℝ)) a ∂iidCosts μ) =
          (iidCosts μ).real (retainedPathEvent (paths i) A) from
        integral_indicator_one (measurableSet_retainedPathEvent (paths i) hA), Measure.real,
        measure_retainedPathEvent μ (paths i) hA, ENNReal.toReal_pow]
      rfl
    _ = _ := by simp

/-- Any family of at most `(2*n)^k` candidate simple length-`k` paths
from a fixed vertex has a bounded expected short-path count at a fixed
positive cutoff, uniformly at large graph sizes. -/
theorem eventually_integral_shortPathFamilyCount_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {d κ R : ℝ} (hd : 0 < d) (hκ : 0 < κ) (hR : 0 < R) (h : SmallCostTail μ κ d)
    (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (I : Type) [Fintype I], Fintype.card I ≤ (2 * n) ^ k →
      ∀ paths : I → (Fin k ↪ ℕ × ℕ),
      (∫ C, retainedPathFamilyCount paths (Iic (R / lengthScale d κ n)) C ∂iidCosts μ) ≤
        (2 * (R ^ d + 1)) ^ k := by
  have ht := (tendsto_scaled_shortEdgeProbability hd hκ hR h).eventually
    (Iio_mem_nhds (lt_add_one (R ^ d)))
  filter_upwards [ht] with n hn
  intro I _ hI paths
  rw [integral_retainedPathFamilyCount μ paths measurableSet_Iic, ← cdf_eq_real]
  have hp : 0 ≤ shortEdgeProbability μ d κ R n := cdf_nonneg μ _
  have hcard : (Fintype.card I : ℝ) ≤ (2 * (n : ℝ)) ^ k := by exact_mod_cast hI
  calc
    _ ≤ (2 * (n : ℝ)) ^ k * (shortEdgeProbability μ d κ R n) ^ k :=
      mul_le_mul_of_nonneg_right hcard (pow_nonneg hp _)
    _ = (2 * ((n : ℝ) * shortEdgeProbability μ d κ R n)) ^ k := by rw [← mul_pow, mul_assoc]
    _ ≤ _ := by
      apply pow_le_pow_left₀ (by positivity)
      exact mul_le_mul_of_nonneg_left hn.le (by norm_num)

private def oppositeSides {n : ℕ} : (Fin n ⊕ Fin n) → (Fin n ⊕ Fin n) → Prop
  | .inl _, .inr _ => True
  | .inr _, .inl _ => True
  | _, _ => False

private def pathCostEntry {n : ℕ} : (Fin n ⊕ Fin n) → (Fin n ⊕ Fin n) → ℕ × ℕ
  | .inl i, .inr j => (i.val, j.val)
  | .inr j, .inl i => (i.val, j.val)
  | _, _ => (0, 0)

private theorem pathCostEntry_determines_endpoints {n : ℕ}
    {v w x y : Fin n ⊕ Fin n} (hv : oppositeSides v w) (hx : oppositeSides x y)
    (h : pathCostEntry v w = pathCostEntry x y) : (v = x ∧ w = y) ∨ (v = y ∧ w = x) := by
  cases v <;> cases w <;> cases x <;> cases y <;>
    simp_all [oppositeSides, pathCostEntry, Prod.mk.injEq, Fin.val_inj]

private def rootedVertices {n k : ℕ} (root : Fin n ⊕ Fin n)
    (rest : Fin k → Fin n ⊕ Fin n) : Fin (k + 1) → Fin n ⊕ Fin n :=
  Fin.cons (α := fun _ ↦ Fin n ⊕ Fin n) root rest

/-- Simple paths of the designated length, starting at one specified
vertex in the full bipartite graph. -/
def RootedSimplePath {n : ℕ} (root : Fin n ⊕ Fin n) (k : ℕ) :=
  {rest : Fin k → (Fin n ⊕ Fin n) //
    Function.Injective (rootedVertices root rest) ∧
    ∀ i : Fin k, oppositeSides (rootedVertices root rest i.castSucc) (rootedVertices root rest i.succ)}

noncomputable instance {n : ℕ} (root : Fin n ⊕ Fin n) (k : ℕ) :
    Fintype (RootedSimplePath root k) := by
  classical
  unfold RootedSimplePath
  infer_instance

/-- The successive edges on a simple path are distinct array entries. -/
def rootedSimplePathEntries {n k : ℕ} {root : Fin n ⊕ Fin n}
    (p : RootedSimplePath root k) : Fin k ↪ ℕ × ℕ where
  toFun i := pathCostEntry (rootedVertices root p.val i.castSucc) (rootedVertices root p.val i.succ)
  inj' := by
    intro i j heq
    rcases pathCostEntry_determines_endpoints (p.property.2 i) (p.property.2 j) heq with
      hd | hr
    · exact Fin.castSucc_injective k (p.property.1 hd.1)
    · have h₁ := congrArg (Fin.val : Fin (k + 1) → ℕ) (p.property.1 hr.1)
      have h₂ := congrArg (Fin.val : Fin (k + 1) → ℕ) (p.property.1 hr.2)
      simp only [Fin.val_castSucc, Fin.val_succ] at h₁ h₂
      omega

theorem card_rootedSimplePath_le {n : ℕ} (root : Fin n ⊕ Fin n) (k : ℕ) :
    Fintype.card (RootedSimplePath root k) ≤ (2 * n) ^ k := by
  have h := Fintype.card_le_of_injective
    (fun p : RootedSimplePath root k ↦ (p.val : Fin k → Fin n ⊕ Fin n))
    Subtype.val_injective
  simpa only [Fintype.card_fun, Fintype.card_sum, Fintype.card_fin, two_mul] using h

/-- The expected number of retained simple length-`k` paths from any
root is bounded at a fixed cutoff, uniformly in large graph sizes. -/
theorem eventually_integral_short_rootedSimplePathCount_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {d κ R : ℝ} (hd : 0 < d) (hκ : 0 < κ) (hR : 0 < R) (h : SmallCostTail μ κ d)
    (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ root : Fin n ⊕ Fin n,
      (∫ C, retainedPathFamilyCount
        (rootedSimplePathEntries (root := root) (k := k))
        (Iic (R / lengthScale d κ n)) C ∂iidCosts μ) ≤
        (2 * (R ^ d + 1)) ^ k := by
  filter_upwards [eventually_integral_shortPathFamilyCount_le hd hκ hR h k] with n hn root
  exact hn _ (card_rootedSimplePath_le root k) rootedSimplePathEntries

end Certificate.LocalExploration

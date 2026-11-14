import Certificate.RootEdgeMarks
import Certificate.LocalExplorationPattern
import Mathlib.Probability.Independence.InfinitePi

/-!
# Several exposed roots

A row root and a column root can share only their connecting matrix entry.
Excluding those cross-root entries makes the entire collection of exposed
stars independent. Root labels and available neighbor labels may vary by
index, so the same law applies after fixed labels have been removed.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Certificate.LocalExploration

/-- A bipartite index: a row is on the left of the sum and a column on the right. -/
abbrev Vertex := ℕ ⊕ ℕ

/-- The matrix position from a root to a label in the opposite class. -/
def rootEntry (v : Vertex) (j : ℕ) : ℕ × ℕ :=
  match v with
  | .inl i => (i, j)
  | .inr i => (j, i)

/-- The vertex in the root's opposite class with the given label. -/
def oppositeVertex (v : Vertex) (j : ℕ) : Vertex :=
  match v with
  | .inl _ => .inr j
  | .inr _ => .inl j

/-- Distinct roots and distinct available labels give distinct matrix entries
after excluding all cross-root entries. -/
theorem exposedEntry_injective {ρ : Type*} {I : ρ → Type*}
    (roots : ρ ↪ Vertex) (labels : ∀ u, I u ↪ ℕ)
    (havoid : ∀ u (i : I u) v, roots v ≠ oppositeVertex (roots u) (labels u i)) :
    Function.Injective (fun p : Sigma I => rootEntry (roots p.1) (labels p.1 p.2)) := by
  have hsame {u v : ρ} (i : I u) (j : I v) (huv : u = v)
      (he : rootEntry (roots u) (labels u i) = rootEntry (roots v) (labels v j)) :
      (⟨u, i⟩ : Sigma I) = ⟨v, j⟩ := by
    subst v
    have hlabel : labels u i = labels u j := by
      cases hu : roots u
      · exact congrArg Prod.snd (by simpa only [hu, rootEntry] using he)
      · exact congrArg Prod.fst (by simpa only [hu, rootEntry] using he)
    rw [(labels u).injective hlabel]
  rintro ⟨u, i⟩ ⟨v, j⟩ he
  change rootEntry (roots u) (labels u i) = rootEntry (roots v) (labels v j) at he
  cases hu : roots u with
  | inl a =>
    cases hv : roots v with
    | inl b =>
      have h : a = b := congrArg Prod.fst (by simpa only [hu, hv, rootEntry] using he)
      apply hsame i j (roots.injective _ ) he
      rw [hu, hv, h]
    | inr b =>
      have h : labels u i = b := congrArg Prod.snd (by simpa only [hu, hv, rootEntry] using he)
      exfalso
      apply havoid u i v
      rw [hv, hu, oppositeVertex, h]
  | inr a =>
    cases hv : roots v with
    | inl b =>
      have h : labels u i = b := congrArg Prod.fst (by simpa only [hu, hv, rootEntry] using he)
      exfalso
      apply havoid u i v
      rw [hv, hu, oppositeVertex, h]
    | inr b =>
      have h : a = b := congrArg Prod.snd (by simpa only [hu, hv, rootEntry] using he)
      apply hsame i j (roots.injective _ ) he
      rw [hu, hv, h]

/-- The raw array entries sampled by one exposure from every root. -/
def rootCosts {ρ : Type*} {I : ρ → Type*} (roots : ρ ↪ Vertex)
    (labels : ∀ u, I u ↪ ℕ) (C : CostArray) (u : ρ) (i : I u) : ℝ :=
  C (rootEntry (roots u) (labels u i))

theorem measurable_rootCosts {ρ : Type*} {I : ρ → Type*} (roots : ρ ↪ Vertex)
    (labels : ∀ u, I u ↪ ℕ) : Measurable (rootCosts roots labels) := by
  unfold rootCosts
  fun_prop

/-- The complete record of exposed stars has the product of iid-entry laws. -/
theorem rootCosts_jointLaw {ρ : Type*} {I : ρ → Type*}
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (roots : ρ ↪ Vertex) (labels : ∀ u, I u ↪ ℕ)
    (havoid : ∀ u (i : I u) v, roots v ≠ oppositeVertex (roots u) (labels u i)) :
    (iidCosts μ).map (rootCosts roots labels) =
      Measure.infinitePi (fun u : ρ => Measure.infinitePi (fun _ : I u => μ)) := by
  let flat : CostArray → (Sigma I → ℝ) :=
    fun C p => C (rootEntry (roots p.1) (labels p.1 p.2))
  have hfm : Measurable flat := by unfold flat; fun_prop
  have hf : (iidCosts μ).map flat = Measure.infinitePi (fun _ : Sigma I => μ) :=
    Measure.map_infinitePi_infinitePi_of_inj (exposedEntry_injective roots labels havoid)
  let cur := MeasurableEquiv.piCurry (fun (u : ρ) (_ : I u) => ℝ)
  have hc : rootCosts roots labels = cur ∘ flat := rfl
  rw [hc, ← Measure.map_map cur.measurable hfm, hf]
  exact Measure.infinitePi_map_piCurry (fun (u : ρ) (_ : I u) => μ)

/-- As in the finite assignment, multiply raw costs by the size-dependent scale. -/
noncomputable def rootLengths {ρ : Type*} {I : ρ → Type*} (roots : ρ ↪ Vertex)
    (labels : ∀ u, I u ↪ ℕ) (d κ : ℝ) (n : ℕ) (C : CostArray) (u : ρ) (i : I u) : ℝ :=
  lengthScale d κ n * rootCosts roots labels C u i

theorem measurable_rootLengths {ρ : Type*} {I : ρ → Type*} (roots : ρ ↪ Vertex)
    (labels : ∀ u, I u ↪ ℕ) (d κ : ℝ) (n : ℕ) :
    Measurable (rootLengths roots labels d κ n) := by
  unfold rootLengths rootCosts
  fun_prop

theorem isProbabilityMeasure_scaledLengthLaw (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (d κ : ℝ) (n : ℕ) : IsProbabilityMeasure (scaledLengthLaw μ d κ n) := by
  unfold scaledLengthLaw
  exact Measure.isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))

/-- The exposed scaled lengths have independent product law across roots and within a root. -/
theorem rootLengths_jointLaw {ρ : Type*} {I : ρ → Type*}
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (roots : ρ ↪ Vertex) (labels : ∀ u, I u ↪ ℕ)
    (havoid : ∀ u (i : I u) v, roots v ≠ oppositeVertex (roots u) (labels u i))
    (d κ : ℝ) (n : ℕ) :
    (iidCosts μ).map (rootLengths roots labels d κ n) =
      Measure.infinitePi (fun u : ρ => Measure.infinitePi
        (fun _ : I u => scaledLengthLaw μ d κ n)) := by
  let scaleAll (f : ∀ u, I u → ℝ) (u : ρ) (i : I u) := lengthScale d κ n * f u i
  have hs : rootLengths roots labels d κ n = scaleAll ∘ rootCosts roots labels := rfl
  have sm (u : ρ) : Measurable (fun (v : I u → ℝ) i => lengthScale d κ n * v i) := by fun_prop
  have hm : Measurable scaleAll := by unfold scaleAll; fun_prop
  rw [hs, ← Measure.map_map hm (measurable_rootCosts roots labels),
    rootCosts_jointLaw μ roots labels havoid]
  change _ = Measure.infinitePi _
  rw [Measure.infinitePi_map_pi _ sm]
  congr 1
  funext u
  exact Measure.infinitePi_map_pi _ (fun _ => by fun_prop)

/-- The count of short edges leaving each exposed root in the probed block. -/
noncomputable def rootCounts {ρ : Type*} {I : ρ → Type*} [∀ u, Fintype (I u)]
    (roots : ρ ↪ Vertex) (labels : ∀ u, I u ↪ ℕ)
    (d κ R : ℝ) (n : ℕ) (C : CostArray) (u : ρ) : ℕ :=
  retainedCount (Iic R) (rootLengths roots labels d κ n C u)

/-- Joint mass of the actual short-edge counts of finitely many exposed roots.
Each component has its own number of available trials. -/
theorem measure_rootCounts_eq {ρ : Type*} [Fintype ρ]
    {I : ρ → Type*} [∀ u, Fintype (I u)]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (roots : ρ ↪ Vertex) (labels : ∀ u, I u ↪ ℕ)
    (havoid : ∀ u (i : I u) v, roots v ≠ oppositeVertex (roots u) (labels u i))
    (d κ R : ℝ) (n : ℕ) (k : ρ → ℕ) :
    iidCosts μ {C | rootCounts roots labels d κ R n C = k} =
      ∏ u, ((Fintype.card (I u)).choose (k u) : ℝ≥0∞) *
        (scaledLengthLaw μ d κ n (Iic R)) ^ k u *
        (scaledLengthLaw μ d κ n (Ioi R)) ^ (Fintype.card (I u) - k u) := by
  let ν := scaledLengthLaw μ d κ n
  let : IsProbabilityMeasure ν := isProbabilityMeasure_scaledLengthLaw μ d κ n
  let g (u : ρ) (x : I u → ℝ) := retainedCount (Iic R) x
  have hg (u : ρ) : Measurable (g u) := measurable_retainedCount measurableSet_Iic
  let : ∀ u : ρ, IsProbabilityMeasure ((Measure.infinitePi (fun _ : I u => ν)).map (g u)) :=
    fun u => Measure.isProbabilityMeasure_map (hg u).aemeasurable
  let allCounts (x : ∀ u, I u → ℝ) (u : ρ) := g u (x u)
  have hall : Measurable allCounts := by unfold allCounts; fun_prop
  have hmap : (iidCosts μ).map (rootCounts roots labels d κ R n) =
      Measure.infinitePi (fun u : ρ => (Measure.infinitePi (fun _ : I u => ν)).map (g u)) := by
    change (iidCosts μ).map (allCounts ∘ rootLengths roots labels d κ n) = _
    rw [← Measure.map_map hall (measurable_rootLengths roots labels d κ n),
      rootLengths_jointLaw μ roots labels havoid]
    exact Measure.infinitePi_map_pi _ hg
  have hmeas : Measurable (rootCounts roots labels d κ R n) :=
    hall.comp (measurable_rootLengths roots labels d κ n)
  change iidCosts μ ((rootCounts roots labels d κ R n) ⁻¹' {k}) = _
  rw [← Measure.map_apply hmeas (measurableSet_singleton k), hmap, Measure.infinitePi_singleton,
    tprod_fintype]
  apply Finset.prod_congr rfl
  intro u _
  rw [Measure.map_apply (hg u) (measurableSet_singleton (k u))]
  simp only [← Set.compl_Iic]
  exact measure_retainedCount_eq ν measurableSet_Iic (k u)

end Certificate.LocalExploration

import Certificate.LocalAssignmentBracketLimits
import Mathlib.Probability.Independence.InfinitePi

/-! Reindexing the iid assignment graph preserves the laws of the root brackets. -/

open Finset Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace Certificate.Tree

section Reindex

variable {V V' E E' : Type*} [DecidableEq V] [DecidableEq V']

private theorem otherEnd_of_erased_singleton (ends : E → Finset V) {e : E} {v u : V}
    (h : (ends e).erase v = {u}) : otherEnd ends e v = u := by
  have hn : ((ends e).erase v).Nonempty := h.symm ▸ singleton_nonempty u
  have hm : otherEnd ends e v ∈ (ends e).erase v := by
    simpa only [otherEnd, dif_pos hn] using hn.choose_spec
  simpa only [h, mem_singleton] using hm

private theorem reindex_otherEnd (φ : V ≃ V') (ψ : E ≃ E')
    (ends : E → Finset V) (ends' : E' → Finset V')
    (hend : ∀ e, (ends e).map φ.toEmbedding = ends' (ψ e))
    {e : E} {v : V} (hv : v ∈ ends e) (hc : (ends e).card = 2) :
    otherEnd ends' (ψ e) (φ v) = φ (otherEnd ends e v) := by
  have hcard : ((ends e).erase v).card = 1 := by rw [card_erase_of_mem hv, hc]
  obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hcard
  have hu' : (ends' (ψ e)).erase (φ v) = {φ u} := by
    rw [← hend e]
    change ((ends e).map φ.toEmbedding).erase (φ.toEmbedding v) = {φ.toEmbedding u}
    rw [← map_erase, hu, map_singleton]
  rw [otherEnd_of_erased_singleton ends hu, otherEnd_of_erased_singleton ends' hu']

private theorem map_incident (φ : V ≃ V') (ψ : E ≃ E')
    (ends : E → Finset V) (ends' : E' → Finset V')
    (hend : ∀ e, (ends e).map φ.toEmbedding = ends' (ψ e))
    (S : Finset V) (D : Finset E) (v : V) :
    (incident ends S D v).map ψ.toEmbedding =
      incident ends' (S.map φ.toEmbedding) (D.map ψ.toEmbedding) (φ v) := by
  ext e'
  obtain ⟨e,rfl⟩ := ψ.surjective e'
  have hv : φ v ∈ (ends e).map φ.toEmbedding ↔ v ∈ ends e := mem_map' _
  simp only [mem_map_equiv, Equiv.symm_apply_apply, incident, mem_filter, ← hend e, hv,
    map_subset_map]

/-- The deletion brackets are unchanged by relabelling all vertices and edges
of a two-endpoint graph along a weight-preserving isomorphism. -/
theorem finiteRootBounds_reindex (φ : V ≃ V') (ψ : E ≃ E')
    (ends : E → Finset V) (ends' : E' → Finset V')
    (hend : ∀ e, (ends e).map φ.toEmbedding = ends' (ψ e))
    (edges : Finset E) (hcard : ∀ e ∈ edges, (ends e).card = 2)
    (w : E → ℝ) (w' : E' → ℝ) (hw : ∀ e, w' (ψ e) = w e)
    (z : ℝ) (k : ℕ) (S : Finset V) (v : V) :
    finiteRootBounds ends' (edges.map ψ.toEmbedding) w' z k
      (S.map φ.toEmbedding) (φ v) = finiteRootBounds ends edges w z k S v := by
  induction k generalizing S v with
  | zero => rfl
  | succ k ih =>
    let B (e : E) := finiteRootBounds ends edges w z k (S.erase v) (otherEnd ends e v)
    let D (e' : E') := finiteRootBounds ends' (edges.map ψ.toEmbedding) w' z k
      ((S.map φ.toEmbedding).erase (φ v)) (otherEnd ends' e' (φ v))
    have hsum (f : ℝ × ℝ → ℝ) :
        (∑ e' ∈ incident ends' (S.map φ.toEmbedding) (edges.map ψ.toEmbedding) (φ v),
          w' e' * f (D e')) = ∑ e ∈ incident ends S edges v, w e * f (B e) := by
      rw [← map_incident φ ψ ends ends' hend S edges v, Finset.sum_map]
      apply Finset.sum_congr rfl
      intro e he
      have he' := Finset.mem_filter.mp he
      have hrec : D (ψ e) = B e := by
        dsimp only [D,B]
        have hErase : (S.map φ.toEmbedding).erase (φ v) = (S.erase v).map φ.toEmbedding :=
          (Finset.map_erase φ.toEmbedding S v).symm
        rw [hErase, reindex_otherEnd φ ψ ends ends' hend he'.2.1 (hcard e he'.1)]
        exact ih (S.erase v) (otherEnd ends e v)
      change w' (ψ e) * f (D (ψ e)) = w e * f (B e)
      rw [hrec, hw e]
    change ((z + ∑ e' ∈ incident ends' (S.map φ.toEmbedding) (edges.map ψ.toEmbedding) (φ v),
      w' e' * (D e').2)⁻¹,
      (z + ∑ e' ∈ incident ends' (S.map φ.toEmbedding) (edges.map ψ.toEmbedding) (φ v),
        w' e' * (D e').1)⁻¹) = _
    rw [hsum Prod.snd, hsum Prod.fst]
    rfl

end Reindex

end Certificate.Tree

namespace Certificate.CanonicalTree

/-- The two actual cutoff graph brackets at a specified vertex. -/
noncomputable def cutoffRootBounds (β d κ R z : ℝ) (n k : ℕ) (v : Fin n ⊕ Fin n)
    (C : CostArray) : ℝ × ℝ :=
  let G := cutoffAssignmentGraph β d κ R n C
  Tree.finiteRootBounds G.ends G.edges G.weight z k G.vertices v

theorem measurable_cutoffRootBounds (β d κ R z : ℝ) (n k : ℕ) (v : Fin n ⊕ Fin n) :
    Measurable (cutoffRootBounds β d κ R z n k v) := by
  let w (C : CostArray) (e : Fin n × Fin n) :=
    if e ∈ retainedEdges d κ R n C then Real.exp (-β * edgeLength d κ n C e) else 0
  have he : cutoffRootBounds β d κ R z n k v =
      fun C => Tree.finiteRootBounds Tree.Bipartite.ends univ (w C) z k univ v := by
    funext C
    exact Tree.finiteRootBounds_masked_weights _ (Finset.subset_univ _) _ _ _ _ _
  rw [he]
  exact Tree.measurable_finiteRootBounds _ _ (measurable_masked_assignment_weight β d κ R n) _ _ _ _

private def reindexCostArray (η : Equiv.Perm (ℕ × ℕ)) (C : CostArray) : CostArray := C ∘ η

private theorem measurePreserving_reindexCostArray (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (η : Equiv.Perm (ℕ × ℕ)) :
    MeasurePreserving (reindexCostArray η) (iidCosts μ) (iidCosts μ) :=
  ⟨measurable_pi_iff.mpr fun i => measurable_pi_apply (η i),
    Measure.map_infinitePi_infinitePi_of_inj η.injective⟩

private theorem cutoffRootBounds_reindex (β d κ R z : ℝ) {n : ℕ} (k : ℕ)
    (η : Equiv.Perm (ℕ × ℕ)) (φ : Equiv.Perm (Fin n ⊕ Fin n)) (ψ : Equiv.Perm (Fin n × Fin n))
    (hend : ∀ e, (Tree.Bipartite.ends e).map φ.toEmbedding = Tree.Bipartite.ends (ψ e))
    (hcoord : ∀ e, η (e.1.val,e.2.val) = ((ψ e).1.val,(ψ e).2.val))
    (v : Fin n ⊕ Fin n) (C : CostArray) :
    cutoffRootBounds β d κ R z n k v (reindexCostArray η C) =
      cutoffRootBounds β d κ R z n k (φ v) C := by
  let C' := reindexCostArray η C
  have hlen (e : Fin n × Fin n) : edgeLength d κ n C' e = edgeLength d κ n C (ψ e) := by
    show lengthScale d κ n * C (η (e.1.val,e.2.val)) = _
    rw [hcoord]
    rfl
  have hedges : (retainedEdges d κ R n C').map ψ.toEmbedding = retainedEdges d κ R n C := by
    ext e'
    obtain ⟨e,rfl⟩ := ψ.surjective e'
    simp only [mem_map_equiv, Equiv.symm_apply_apply, retainedEdges, mem_filter, Finset.mem_univ,
      true_and, hlen]
  have h := Tree.finiteRootBounds_reindex φ ψ Tree.Bipartite.ends Tree.Bipartite.ends hend
    (retainedEdges d κ R n C') (fun e _ => Tree.Bipartite.ends_card e)
    (fun e => Real.exp (-β * edgeLength d κ n C' e))
    (fun e => Real.exp (-β * edgeLength d κ n C e)) (fun e => by rw [hlen])
    z k univ v
  rw [hedges, Finset.map_univ_equiv] at h
  exact h.symm

private theorem map_cutoffRootBounds_eq_of_reindex (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (β d κ R z : ℝ) {n : ℕ} (k : ℕ)
    (η : Equiv.Perm (ℕ × ℕ)) (φ : Equiv.Perm (Fin n ⊕ Fin n)) (ψ : Equiv.Perm (Fin n × Fin n))
    (hend : ∀ e, (Tree.Bipartite.ends e).map φ.toEmbedding = Tree.Bipartite.ends (ψ e))
    (hcoord : ∀ e, η (e.1.val,e.2.val) = ((ψ e).1.val,(ψ e).2.val)) (v : Fin n ⊕ Fin n) :
    (iidCosts μ).map (cutoffRootBounds β d κ R z n k v) =
      (iidCosts μ).map (cutoffRootBounds β d κ R z n k (φ v)) := by
  have hη := measurePreserving_reindexCostArray μ η
  nth_rw 1 [← hη.map_eq]
  rw [Measure.map_map (measurable_cutoffRootBounds β d κ R z n k v) hη.measurable]
  congr 1
  funext C
  exact cutoffRootBounds_reindex β d κ R z k η φ ψ hend hcoord v C

private def extendFinPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) : Equiv.Perm ℕ :=
  σ.extendDomain Fin.equivSubtype

@[simp] private theorem extendFinPerm_val {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    extendFinPerm σ i.val = (σ i).val :=
  Equiv.Perm.extendDomain_apply_image σ Fin.equivSubtype i

/-- Row and column permutations carry a root bracket to the bracket at
the relabelled root in law. -/
theorem map_cutoffRootBounds_eq_of_row_col_perm (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (β d κ R z : ℝ) {n : ℕ} (k : ℕ) (σ τ : Equiv.Perm (Fin n)) (v : Fin n ⊕ Fin n) :
    (iidCosts μ).map (cutoffRootBounds β d κ R z n k v) =
      (iidCosts μ).map (cutoffRootBounds β d κ R z n k ((Equiv.sumCongr σ τ) v)) := by
  apply map_cutoffRootBounds_eq_of_reindex μ β d κ R z k
    (Equiv.prodCongr (extendFinPerm σ) (extendFinPerm τ))
    (Equiv.sumCongr σ τ) (Equiv.prodCongr σ τ)
  · intro e
    simp [Tree.Bipartite.ends]
  · intro e
    simp

/-- Transposing the array exchanges the two root classes in law. -/
theorem map_cutoffRootBounds_eq_of_transpose (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (β d κ R z : ℝ) {n : ℕ} (k : ℕ) (v : Fin n ⊕ Fin n) :
    (iidCosts μ).map (cutoffRootBounds β d κ R z n k v) =
      (iidCosts μ).map (cutoffRootBounds β d κ R z n k v.swap) := by
  apply map_cutoffRootBounds_eq_of_reindex μ β d κ R z k
    (Equiv.prodComm ℕ ℕ) (Equiv.sumComm (Fin n) (Fin n)) (Equiv.prodComm (Fin n) (Fin n))
  · intro e
    simp [Tree.Bipartite.ends]
    exact Finset.pair_comm _ _
  · intro e
    rfl

/-- The lower and upper brackets have the same joint law at every root. -/
theorem map_cutoffRootBounds_eq (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (β d κ R z : ℝ) {n : ℕ} (k : ℕ) (u v : Fin n ⊕ Fin n) :
    (iidCosts μ).map (cutoffRootBounds β d κ R z n k u) =
      (iidCosts μ).map (cutoffRootBounds β d κ R z n k v) := by
  have hleft (i j : Fin n) :
      (iidCosts μ).map (cutoffRootBounds β d κ R z n k (.inl i)) =
        (iidCosts μ).map (cutoffRootBounds β d κ R z n k (.inl j)) := by
    simpa using map_cutoffRootBounds_eq_of_row_col_perm μ β d κ R z k
      (Equiv.swap i j) (Equiv.refl (Fin n)) (Sum.inl i)
  have hflip (i : Fin n) :
      (iidCosts μ).map (cutoffRootBounds β d κ R z n k (.inl i)) =
        (iidCosts μ).map (cutoffRootBounds β d κ R z n k (.inr i)) :=
    map_cutoffRootBounds_eq_of_transpose μ β d κ R z k (.inl i)
  rcases u with i | i <;> rcases v with j | j
  · exact hleft i j
  · exact (hleft i j).trans (hflip j)
  · exact (hflip i).symm.trans (hleft i j)
  · exact (hflip i).symm.trans ((hleft i j).trans (hflip j))

/-- Equality of expectations of any measurable test of the two root bounds. -/
theorem integral_cutoffRootBounds_test_eq (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (β d κ R z : ℝ) {n : ℕ} (k : ℕ) (u v : Fin n ⊕ Fin n)
    {f : ℝ × ℝ → ℝ} (hf : Measurable f) :
    (∫ C, f (cutoffRootBounds β d κ R z n k u C) ∂iidCosts μ) =
      ∫ C, f (cutoffRootBounds β d κ R z n k v C) ∂iidCosts μ := by
  calc
    _ = ∫ x, f x ∂(iidCosts μ).map (cutoffRootBounds β d κ R z n k u) :=
      (integral_map (measurable_cutoffRootBounds β d κ R z n k u).aemeasurable
        hf.aestronglyMeasurable).symm
    _ = ∫ x, f x ∂(iidCosts μ).map (cutoffRootBounds β d κ R z n k v) := by
      rw [map_cutoffRootBounds_eq μ β d κ R z k u v]
    _ = _ := integral_map (measurable_cutoffRootBounds β d κ R z n k v).aemeasurable
      hf.aestronglyMeasurable

theorem cutoffRootBounds_mem (β d κ R : ℝ) {z : ℝ} (hz : 0 < z)
    {n : ℕ} (k : ℕ) (v : Fin n ⊕ Fin n) (C : CostArray) :
    0 ≤ (cutoffRootBounds β d κ R z n k v C).1 ∧
      (cutoffRootBounds β d κ R z n k v C).1 ≤ (cutoffRootBounds β d κ R z n k v C).2 ∧
      (cutoffRootBounds β d κ R z n k v C).2 ≤ z⁻¹ := by
  let G := cutoffAssignmentGraph β d κ R n C
  exact Tree.finiteRootBounds_mem G.ends G.edges G.weight G.weight_nonneg hz k G.vertices v

/-- Averaging over all roots leaves each expected cutoff bracket unchanged. -/
theorem integral_cutoffMeanRootBounds_coordinates_eq (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (β d κ R : ℝ) {z : ℝ} (hz : 0 < z) {n : ℕ} (hn : 0 < n)
    (k : ℕ) (v : Fin n ⊕ Fin n) :
    (∫ C, (cutoffMeanRootBounds β d κ R z n k C).1 ∂iidCosts μ) =
        (∫ C, (cutoffRootBounds β d κ R z n k v C).1 ∂iidCosts μ) ∧
    (∫ C, (cutoffMeanRootBounds β d κ R z n k C).2 ∂iidCosts μ) =
      (∫ C, (cutoffRootBounds β d κ R z n k v C).2 ∂iidCosts μ) := by
  let : IsProbabilityMeasure (iidCosts μ) := by unfold iidCosts; infer_instance
  let B := cutoffRootBounds β d κ R z n k
  have hmeas (u : Fin n ⊕ Fin n) : Measurable (B u) := measurable_cutoffRootBounds β d κ R z n k u
  have hInt (f : ℝ × ℝ → ℝ) (hf : Measurable f)
      (hfb : ∀ b : ℝ × ℝ, 0 ≤ b.1 → b.1 ≤ b.2 → b.2 ≤ z⁻¹ → 0 ≤ f b ∧ f b ≤ z⁻¹)
      (u : Fin n ⊕ Fin n) : Integrable (fun C => f (B u C)) (iidCosts μ) := by
    refine (integrable_const z⁻¹).mono' (hf.comp (hmeas u)).aestronglyMeasurable
      (Eventually.of_forall fun C => ?_)
    have hb := cutoffRootBounds_mem β d κ R hz k u C
    have h' := hfb (B u C) hb.1 hb.2.1 hb.2.2
    rw [Real.norm_of_nonneg h'.1]
    exact h'.2
  have havg (f : ℝ × ℝ → ℝ) (hf : Measurable f)
      (hfb : ∀ b : ℝ × ℝ, 0 ≤ b.1 → b.1 ≤ b.2 → b.2 ≤ z⁻¹ → 0 ≤ f b ∧ f b ≤ z⁻¹) :
      (∫ C, (∑ u, f (B u C)) / (2 * n) ∂iidCosts μ) = ∫ C, f (B v C) ∂iidCosts μ := by
    rw [integral_div, integral_finsetSum _ (fun u _ => hInt f hf hfb u)]
    have hsum : (∑ u, ∫ C, f (B u C) ∂iidCosts μ) = ∑ _u : Fin n ⊕ Fin n,
        ∫ C, f (B v C) ∂iidCosts μ := by
      exact Finset.sum_congr rfl (fun u _ => integral_cutoffRootBounds_test_eq μ β d κ R z k u v hf)
    rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_sum, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_add, show (n : ℝ) + n = 2 * n by ring]
    exact mul_div_cancel_left₀ _ (mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr hn.ne'))
  exact ⟨havg Prod.fst measurable_fst (fun _ h₁ h₂ h₃ => ⟨h₁, h₂.trans h₃⟩),
    havg Prod.snd measurable_snd (fun _ h₁ h₂ h₃ => ⟨h₁.trans h₂,h₃⟩)⟩

theorem integral_cutoffMeanRootBounds_fst_eq (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (β d κ R : ℝ) {z : ℝ} (hz : 0 < z) {n : ℕ} (hn : 0 < n)
    (k : ℕ) (v : Fin n ⊕ Fin n) :
    (∫ C, (cutoffMeanRootBounds β d κ R z n k C).1 ∂iidCosts μ) =
      ∫ C, (cutoffRootBounds β d κ R z n k v C).1 ∂iidCosts μ :=
  (integral_cutoffMeanRootBounds_coordinates_eq μ β d κ R hz hn k v).1

theorem integral_cutoffMeanRootBounds_snd_eq (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (β d κ R : ℝ) {z : ℝ} (hz : 0 < z) {n : ℕ} (hn : 0 < n)
    (k : ℕ) (v : Fin n ⊕ Fin n) :
    (∫ C, (cutoffMeanRootBounds β d κ R z n k C).2 ∂iidCosts μ) =
      ∫ C, (cutoffRootBounds β d κ R z n k v C).2 ∂iidCosts μ :=
  (integral_cutoffMeanRootBounds_coordinates_eq μ β d κ R hz hn k v).2

/-- Expected convergence at any prescribed sequence of roots in positive
sizes implies the convergence of the averaged lower and upper brackets. -/
theorem tendsto_expected_cutoffMeanRootBounds_of_root
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (β d κ R : ℝ) {z : ℝ} (hz : 0 < z)
    (k : ℕ) (roots : ∀ n : ℕ, Fin (n+1) ⊕ Fin (n+1)) {a b : ℝ}
    (hL : Tendsto (fun n => ∫ C, (cutoffRootBounds β d κ R z (n+1) k (roots n) C).1 ∂iidCosts μ)
      atTop (𝓝 a))
    (hU : Tendsto (fun n => ∫ C, (cutoffRootBounds β d κ R z (n+1) k (roots n) C).2 ∂iidCosts μ)
      atTop (𝓝 b)) :
    Tendsto (fun n => ∫ C, (cutoffMeanRootBounds β d κ R z n k C).1 ∂iidCosts μ) atTop (𝓝 a) ∧
      Tendsto (fun n => ∫ C, (cutoffMeanRootBounds β d κ R z n k C).2 ∂iidCosts μ) atTop (𝓝 b) := by
  constructor
  · apply (tendsto_add_atTop_iff_nat 1).mp
    exact hL.congr' (Eventually.of_forall fun n =>
      (integral_cutoffMeanRootBounds_fst_eq μ β d κ R hz (Nat.zero_lt_succ n) k (roots n)).symm)
  · apply (tendsto_add_atTop_iff_nat 1).mp
    exact hU.congr' (Eventually.of_forall fun n =>
      (integral_cutoffMeanRootBounds_snd_eq μ β d κ R hz (Nat.zero_lt_succ n) k (roots n)).symm)

end Certificate.CanonicalTree

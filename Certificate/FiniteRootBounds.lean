import Certificate.Tree

/-!
# Finite-depth message bounds on a graph

Each recursion step deletes the current vertex. Consequently the forward
branches of this unfolding are indexed by paths with no repeated vertex.
-/

open Finset

namespace Certificate.Tree

variable {V E : Type*} [DecidableEq V] [DecidableEq E]

private noncomputable def otherEnd (ends : E → Finset V) (e : E) (v : V) : V :=
  if h : ((ends e).erase v).Nonempty then h.choose else v

omit [DecidableEq E] in
private theorem otherEnd_spec (ends : E → Finset V) {vertices : Finset V}
    {edges : Finset E} {e : E} {v : V} (he : e ∈ incident ends vertices edges v)
    (hcard : (ends e).card = 2) :
    otherEnd ends e v ∈ vertices.erase v ∧
      (vertices.erase v).erase (otherEnd ends e v) = vertices \ ends e := by
  obtain ⟨_, hv, hsub⟩ := Finset.mem_filter.mp he
  have h₁ : ((ends e).erase v).card = 1 := by
    rw [Finset.card_erase_of_mem hv, hcard]
  have hne : ((ends e).erase v).Nonempty := card_pos.mp (by omega)
  have hu : otherEnd ends e v ∈ (ends e).erase v := by
    simpa only [otherEnd, dif_pos hne] using hne.choose_spec
  have hu' := mem_erase.mp hu
  have heq : ends e = {v, otherEnd ends e v} := by
    obtain ⟨a, ha⟩ := card_eq_one.mp h₁
    have hua : otherEnd ends e v = a := by simpa [ha] using hu
    rw [hua, ← Finset.insert_erase hv, ha]
  refine ⟨mem_erase.mpr ⟨hu'.1, hsub hu'.2⟩, ?_⟩
  ext a
  simp only [mem_erase, heq, mem_sdiff, mem_insert, mem_singleton, not_or]
  tauto

/-- The lower and upper depth bounds use terminal values zero and inverse
fugacity, with the bounds reversed at each deletion step. -/
noncomputable def finiteRootBounds (ends : E → Finset V) (edges : Finset E)
    (w : E → ℝ) (z : ℝ) : ℕ → Finset V → V → ℝ × ℝ
  | 0, _, _ => (0, z⁻¹)
  | depth + 1, vertices, v =>
    let B (e : E) := finiteRootBounds ends edges w z depth (vertices.erase v) (otherEnd ends e v)
    ((z + ∑ e ∈ incident ends vertices edges v, w e * (B e).2)⁻¹,
     (z + ∑ e ∈ incident ends vertices edges v, w e * (B e).1)⁻¹)

omit [DecidableEq E] in
private theorem finiteRootBounds_mem (ends : E → Finset V) (edges : Finset E)
    (w : E → ℝ) (hw : ∀ e, 0 ≤ w e) {z : ℝ} (hz : 0 < z)
    (depth : ℕ) (vertices : Finset V) (v : V) :
    0 ≤ (finiteRootBounds ends edges w z depth vertices v).1 ∧
      (finiteRootBounds ends edges w z depth vertices v).1 ≤
        (finiteRootBounds ends edges w z depth vertices v).2 ∧
      (finiteRootBounds ends edges w z depth vertices v).2 ≤ z⁻¹ := by
  induction depth generalizing vertices v with
  | zero => exact ⟨le_rfl, inv_nonneg.mpr hz.le, le_rfl⟩
  | succ depth ih =>
    let B e := finiteRootBounds ends edges w z depth (vertices.erase v) (otherEnd ends e v)
    let S := incident ends vertices edges v
    have hL : 0 ≤ ∑ e ∈ S, w e * (B e).1 :=
      Finset.sum_nonneg fun e _ ↦ mul_nonneg (hw e) (ih _ _).1
    have hU : 0 ≤ ∑ e ∈ S, w e * (B e).2 :=
      Finset.sum_nonneg fun e _ ↦ mul_nonneg (hw e) ((ih _ _).1.trans (ih _ _).2.1)
    have hLU : (∑ e ∈ S, w e * (B e).1) ≤ ∑ e ∈ S, w e * (B e).2 :=
      Finset.sum_le_sum fun e _ ↦ mul_le_mul_of_nonneg_left (ih _ _).2.1 (hw e)
    change 0 ≤ (z + ∑ e ∈ S, w e * (B e).2)⁻¹ ∧
      (z + ∑ e ∈ S, w e * (B e).2)⁻¹ ≤ (z + ∑ e ∈ S, w e * (B e).1)⁻¹ ∧
      (z + ∑ e ∈ S, w e * (B e).1)⁻¹ ≤ z⁻¹
    exact ⟨inv_nonneg.mpr (add_nonneg hz.le hU),
      inv_anti₀ (add_pos_of_pos_of_nonneg hz hL) (add_le_add_right hLU z),
      inv_anti₀ hz (le_add_of_nonneg_right hL)⟩

/-- Unfolding the finite matching recursion to any depth brackets the
deletion ratio between the two terminal boundary choices. -/
theorem deletionRatio_between_finiteRootBounds (ends : E → Finset V) (edges : Finset E)
    (w : E → ℝ) (hw : ∀ e, 0 ≤ w e) {z : ℝ} (hz : 0 < z)
    (hends : ∀ e ∈ edges, (ends e).card = 2) (depth : ℕ)
    {vertices : Finset V} {v : V} (hv : v ∈ vertices) :
    (finiteRootBounds ends edges w z depth vertices v).1 ≤ deletionRatio ends vertices edges w z v ∧
      deletionRatio ends vertices edges w z v ≤
        (finiteRootBounds ends edges w z depth vertices v).2 := by
  induction depth generalizing vertices v with
  | zero =>
    have h := deletionRatio_pos_le ends edges w hw hz hends hv
    exact ⟨h.1.le, h.2⟩
  | succ depth ih =>
    let B e := finiteRootBounds ends edges w z depth (vertices.erase v) (otherEnd ends e v)
    let S := incident ends vertices edges v
    let H e := monomerPartition ends (vertices \ ends e) edges w z /
      monomerPartition ends (vertices.erase v) edges w z
    have hB (e) (he : e ∈ S) : (B e).1 ≤ H e ∧ H e ≤ (B e).2 := by
      have hspec := otherEnd_spec ends he (hends _ (Finset.mem_filter.mp he).1)
      have h := ih hspec.1
      unfold deletionRatio at h
      rw [hspec.2] at h
      exact h
    have hH : 0 ≤ ∑ e ∈ S, w e * H e := by
      apply Finset.sum_nonneg
      intro e he
      exact mul_nonneg (hw e) ((finiteRootBounds_mem ends edges w hw hz depth _ _).1.trans (hB e he).1)
    have hL : 0 ≤ ∑ e ∈ S, w e * (B e).1 :=
      Finset.sum_nonneg fun e _ ↦ mul_nonneg (hw e) (finiteRootBounds_mem ends edges w hw hz depth _ _).1
    rw [deletionRatio_recursion ends edges w hw hz hends hv]
    change (z + ∑ e ∈ S, w e * (B e).2)⁻¹ ≤ (z + ∑ e ∈ S, w e * H e)⁻¹ ∧
      (z + ∑ e ∈ S, w e * H e)⁻¹ ≤ (z + ∑ e ∈ S, w e * (B e).1)⁻¹
    exact ⟨inv_anti₀ (add_pos_of_pos_of_nonneg hz hH) (add_le_add_right
      (Finset.sum_le_sum fun e he ↦ mul_le_mul_of_nonneg_left (hB e he).2 (hw e)) z),
      inv_anti₀ (add_pos_of_pos_of_nonneg hz hL) (add_le_add_right
      (Finset.sum_le_sum fun e he ↦ mul_le_mul_of_nonneg_left (hB e he).1 (hw e)) z)⟩

end Certificate.Tree

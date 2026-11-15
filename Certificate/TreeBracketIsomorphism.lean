import Certificate.FiniteRootBounds
import Certificate.TreeBoundary

/-! The finite-depth recursion is preserved by weighted neighborhood isomorphisms. -/

open Finset

namespace Certificate.Tree

variable {V E A : Type*} [DecidableEq V] [DecidableEq E]

/-- The unfolded finite neighborhood and a child-indexed weighted tree agree
to the given depth. At each step the isomorphism matches incident edges
to a finite set of child labels, with all omitted child weights zero. -/
def matchesTreeToDepth (ends : E → Finset V) (edges : Finset E) (w : E → ℝ)
    (child : A → ℕ → A) (W : A → ℕ → ℝ) : ℕ → Finset V → V → A → Prop
  | 0, _, _, _ => True
  | depth + 1, vertices, v, a =>
    ∃ (S : Finset ℕ) (e : ↥(incident ends vertices edges v) ≃ ↥S),
      (∀ i ∉ S, W a i = 0) ∧
      (∀ f : ↥(incident ends vertices edges v), w f = W a (e f)) ∧
      (∀ f : ↥(incident ends vertices edges v),
        matchesTreeToDepth ends edges w child W depth (vertices.erase v) (otherEnd ends f v) (child a (e f)))

omit [DecidableEq E] in
private theorem sum_eq_tsum_of_equiv {s : Finset E} {S : Finset ℕ} (e : ↥s ≃ ↥S)
    {f : E → ℝ} {g : ℕ → ℝ} (hg : ∀ i ∉ S, g i = 0) (he : ∀ u : ↥s, f u = g (e u)) :
    (∑ u ∈ s, f u) = ∑' i, g i := by
  rw [tsum_eq_sum hg]
  calc
    _ = ∑ u : ↥s, f u := (Finset.sum_attach s f).symm
    _ = ∑ i : ↥S, g i := Fintype.sum_equiv e _ _ he
    _ = _ := Finset.sum_attach S g

omit [DecidableEq E] in
/-- The graph brackets and tree brackets agree for isomorphic weighted
unfoldings. Both boundary values are preserved. -/
theorem finiteRootBounds_eq_treeBounds_of_matchesTreeToDepth
    (ends : E → Finset V) (edges : Finset E) (w : E → ℝ)
    (child : A → ℕ → A) (W : A → ℕ → ℝ) (z : ℝ)
    {k : ℕ} {vertices : Finset V} {v : V} {a : A}
    (h : matchesTreeToDepth ends edges w child W k vertices v a) :
    finiteRootBounds ends edges w z k vertices v = TreeBoundary.bounds z child W k a := by
  induction k generalizing vertices v a with
  | zero => rfl
  | succ k ih =>
    obtain ⟨S, e, hzero, hw, hbelow⟩ := h
    let B (f : E) := finiteRootBounds ends edges w z k (vertices.erase v) (otherEnd ends f v)
    let D (i : ℕ) := TreeBoundary.bounds z child W k (child a i)
    have hsum (p : ℝ × ℝ → ℝ) :
        (∑ f ∈ incident ends vertices edges v, w f * p (B f)) =
          ∑' i, W a i * p (D i) := by
      apply sum_eq_tsum_of_equiv e
      · intro i hi
        rw [hzero i hi, zero_mul]
      · intro f
        rw [hw f, show B f = D (e f) from ih (hbelow f)]
    change ((z + ∑ f ∈ incident ends vertices edges v, w f * (B f).2)⁻¹,
        (z + ∑ f ∈ incident ends vertices edges v, w f * (B f).1)⁻¹) =
      ((z + ∑' i, W a i * (D i).2)⁻¹, (z + ∑' i, W a i * (D i).1)⁻¹)
    rw [hsum Prod.snd, hsum Prod.fst]

end Certificate.Tree

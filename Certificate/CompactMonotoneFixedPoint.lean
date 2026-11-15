import Mathlib.Topology.Sequences

/-!
# A fixed point from monotone iteration on a compact set

A compact set with a closed partial order and a greatest point supports a
fixed point for every continuous order-preserving self-map. The proof extracts
a convergent subsequence from the decreasing sequence of iterates.
-/

open Filter Set
open scoped Topology

namespace Certificate

/-- The decreasing iteration from a greatest point yields a fixed point. -/
theorem exists_fixedPoint_of_compact_order {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] (S : Set X) (hS : IsCompact S)
    (r : X → X → Prop) (hr : IsClosed {p : X × X | r p.1 p.2})
    (hrefl : ∀ a, r a a) (htrans : ∀ a b c, r a b → r b c → r a c) (hanti : ∀ {a b : X}, r a b → r b a → a = b)
    (top : X) (htop : top ∈ S) (hTop : ∀ x ∈ S, r x top)
    (T : X → X) (hTS : MapsTo T S S) (hT : ContinuousOn T S)
    (hMono : ∀ a ∈ S, ∀ b ∈ S, r a b → r (T a) (T b)) :
    ∃ x ∈ S, T x = x := by
  let x (n : ℕ) := (T^[n]) top
  have hx₀ : x 0 = top := rfl
  have hxSucc (n : ℕ) : x (n + 1) = T (x n) := Function.iterate_succ_apply' ..
  have hxS (n : ℕ) : x n ∈ S := by
    induction n with
    | zero => exact htop
    | succ n ih =>
      rw [hxSucc]
      exact hTS ih
  have hxStep (n : ℕ) : r (x (n + 1)) (x n) := by
    induction n with
    | zero => exact hTop _ (hxS 1)
    | succ n ih =>
      have h := hMono _ (hxS (n + 1)) _ (hxS n) ih
      rwa [← hxSucc (n + 1), ← hxSucc n] at h
  have hxMono {a b : ℕ} (h : a ≤ b) : r (x b) (x a) := by
    induction h with
    | refl => exact hrefl _
    | step h ih => exact htrans _ _ _ (hxStep _) ih
  obtain ⟨u, huS, φ, hφm, hφ⟩ := hS.isSeqCompact hxS
  have huLower (m : ℕ) : r u (x m) := by
    apply hr.mem_of_tendsto (hφ.prodMk_nhds tendsto_const_nhds)
    filter_upwards [hφm.tendsto_atTop.eventually (eventually_ge_atTop m)] with n hn
    exact hxMono hn
  have hTuLower (m : ℕ) : r (T u) (x m) := by
    cases m with
    | zero => exact hTop _ (hTS huS)
    | succ m =>
      rw [hxSucc]
      exact hMono _ huS _ (hxS m) (huLower m)
  have hTu_le : r (T u) u :=
    hr.mem_of_tendsto (tendsto_const_nhds.prodMk_nhds hφ)
      (Eventually.of_forall fun n ↦ hTuLower (φ n))
  have hTx : Tendsto (fun n ↦ x (φ n + 1)) atTop (𝓝 (T u)) := by
    simp_rw [hxSucc]
    exact (show Tendsto T (𝓝[S] u) (𝓝 (T u)) from hT u huS).comp
      (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hφ
        (Eventually.of_forall fun n ↦ hxS (φ n)))
  have hu_le : r u (T u) :=
    hr.mem_of_tendsto (tendsto_const_nhds.prodMk_nhds hTx)
      (Eventually.of_forall fun n ↦ huLower (φ n + 1))
  exact ⟨u, huS, hanti hTu_le hu_le⟩

end Certificate

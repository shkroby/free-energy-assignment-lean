import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.Positivity

/-!
# Boundary messages on a deterministic weighted tree

At each vertex the nonnegative outgoing weights must be summable. No
probabilistic hypothesis enters the antitone comparison or the passage from
finite-depth bounds to the two cross-recursions.
-/

open Filter Set
open scoped Topology

namespace Certificate.TreeBoundary

variable {V : Type*}

noncomputable section

/-- Cavity update at a vertex from its countable family of child messages. -/
def update (z : ℝ) (w H : ℕ → ℝ) : ℝ :=
  (z + ∑' i, w i * H i)⁻¹

private theorem summable_weighted {w H : ℕ → ℝ} {B : ℝ}
    (hw : Summable w) (hw₀ : ∀ i, 0 ≤ w i) (hH₀ : ∀ i, 0 ≤ H i)
    (hHB : ∀ i, H i ≤ B) : Summable (fun i => w i * H i) :=
  Summable.of_nonneg_of_le (fun i => mul_nonneg (hw₀ i) (hH₀ i))
    (fun i => mul_le_mul_of_nonneg_left (hHB i) (hw₀ i)) (hw.mul_right B)

theorem update_pos_le {z : ℝ} {w H : ℕ → ℝ}
    (hz : 0 < z) (hw : ∀ i, 0 ≤ w i) (hH : ∀ i, 0 ≤ H i) :
    0 < update z w H ∧ update z w H ≤ z⁻¹ := by
  have hs : 0 ≤ ∑' i, w i * H i := tsum_nonneg (fun i => mul_nonneg (hw i) (hH i))
  exact ⟨inv_pos.mpr (add_pos_of_pos_of_nonneg hz hs),
    inv_le_inv₀ (add_pos_of_pos_of_nonneg hz hs) hz |>.mpr (le_add_of_nonneg_right hs)⟩

theorem update_antitone {z B : ℝ} {w L U : ℕ → ℝ}
    (hz : 0 < z) (hw : Summable w) (hw₀ : ∀ i, 0 ≤ w i)
    (hL : ∀ i, 0 ≤ L i) (hLU : ∀ i, L i ≤ U i) (hU : ∀ i, U i ≤ B) :
    update z w U ≤ update z w L := by
  have hU₀ i := (hL i).trans (hLU i)
  have Lsumm := summable_weighted hw hw₀ hL (fun i => (hLU i).trans (hU i))
  have Usumm := summable_weighted hw hw₀ hU₀ hU
  have hLpos : 0 < z + ∑' i, w i * L i :=
    add_pos_of_pos_of_nonneg hz (tsum_nonneg fun i => mul_nonneg (hw₀ i) (hL i))
  have hUpos : 0 < z + ∑' i, w i * U i :=
    add_pos_of_pos_of_nonneg hz (tsum_nonneg fun i => mul_nonneg (hw₀ i) (hU₀ i))
  exact (inv_le_inv₀ hUpos hLpos).mpr
    (add_le_add (le_refl z)
      (Lsumm.tsum_le_tsum (fun i => mul_le_mul_of_nonneg_left (hLU i) (hw₀ i)) Usumm))

/-- Lower and upper messages at a given truncation depth. Their roles switch
under the cavity update, which reverses order. -/
def bounds (z : ℝ) (child : V → ℕ → V) (w : V → ℕ → ℝ) : ℕ → V → ℝ × ℝ
  | 0, _ => (0, z⁻¹)
  | n+1, v =>
      (update z (w v) (fun i => (bounds z child w n (child v i)).2),
       update z (w v) (fun i => (bounds z child w n (child v i)).1))

theorem bounds_mem (z : ℝ) (child : V → ℕ → V) (w : V → ℕ → ℝ)
    (hz : 0 < z) (hw : ∀ v, Summable (w v)) (hw₀ : ∀ v i, 0 ≤ w v i) (n : ℕ) (v : V) :
    0 ≤ (bounds z child w n v).1 ∧
      (bounds z child w n v).1 ≤ (bounds z child w n v).2 ∧
      (bounds z child w n v).2 ≤ z⁻¹ := by
  induction n generalizing v with
  | zero => exact ⟨le_rfl, inv_nonneg.mpr hz.le, le_rfl⟩
  | succ n ih =>
      simp only [bounds]
      exact
        ⟨(update_pos_le hz (hw₀ v) (fun i =>
            (ih (child v i)).1.trans (ih (child v i)).2.1)).1.le,
          update_antitone hz (hw v) (hw₀ v) (fun i => (ih (child v i)).1)
            (fun i => (ih (child v i)).2.1) (fun i => (ih (child v i)).2.2),
          (update_pos_le hz (hw₀ v) (fun i => (ih (child v i)).1)).2⟩

theorem bounds_step (z : ℝ) (child : V → ℕ → V) (w : V → ℕ → ℝ)
    (hz : 0 < z) (hw : ∀ v, Summable (w v)) (hw₀ : ∀ v i, 0 ≤ w v i) (n : ℕ) (v : V) :
    (bounds z child w n v).1 ≤ (bounds z child w (n+1) v).1 ∧
      (bounds z child w (n+1) v).2 ≤ (bounds z child w n v).2 := by
  induction n generalizing v with
  | zero =>
      exact ⟨(bounds_mem z child w hz hw hw₀ 1 v).1, (bounds_mem z child w hz hw hw₀ 1 v).2.2⟩
  | succ n ih =>
      simp only [bounds]
      refine ⟨?_, ?_⟩
      · apply update_antitone (B := z⁻¹) hz (hw v) (hw₀ v)
        · exact fun i => (bounds_mem z child w hz hw hw₀ (n+1) (child v i)).1.trans
            (bounds_mem z child w hz hw hw₀ (n+1) (child v i)).2.1
        · exact fun i => (ih (child v i)).2
        · exact fun i => (bounds_mem z child w hz hw hw₀ n (child v i)).2.2
      · apply update_antitone (B := z⁻¹) hz (hw v) (hw₀ v)
        · exact fun i => (bounds_mem z child w hz hw hw₀ n (child v i)).1
        · exact fun i => (ih (child v i)).1
        · exact fun i => (bounds_mem z child w hz hw hw₀ (n+1) (child v i)).2.1.trans
            (bounds_mem z child w hz hw hw₀ (n+1) (child v i)).2.2

/-- Finite-depth recursion for any prescribed bounded terminal messages. -/
def fromBoundary (z : ℝ) (child : V → ℕ → V) (w : V → ℕ → ℝ) (terminal : V → ℝ) :
    ℕ → V → ℝ
  | 0, v => terminal v
  | n+1, v => update z (w v) (fun i => fromBoundary z child w terminal n (child v i))

theorem fromBoundary_between (z : ℝ) (child : V → ℕ → V) (w : V → ℕ → ℝ)
    (hz : 0 < z) (hw : ∀ v, Summable (w v)) (hw₀ : ∀ v i, 0 ≤ w v i)
    (terminal : V → ℝ) (ht : ∀ v, 0 ≤ terminal v ∧ terminal v ≤ z⁻¹) (n : ℕ) (v : V) :
    (bounds z child w n v).1 ≤ fromBoundary z child w terminal n v ∧
      fromBoundary z child w terminal n v ≤ (bounds z child w n v).2 := by
  induction n generalizing v with
  | zero => exact ht v
  | succ n ih =>
    let hm i := bounds_mem z child w hz hw hw₀ n (child v i)
    exact
      ⟨update_antitone hz (hw v) (hw₀ v) (fun i => (hm i).1.trans (ih (child v i)).1)
          (fun i => (ih (child v i)).2) (fun i => (hm i).2.2),
        update_antitone hz (hw v) (hw₀ v) (fun i => (hm i).1)
          (fun i => (ih (child v i)).1) (fun i => (ih (child v i)).2.trans (hm i).2.2)⟩

private theorem update_tendsto {z : ℝ} {w H : ℕ → ℝ} {A : ℕ → ℕ → ℝ}
    (hz : 0 < z) (hw : Summable w) (hw₀ : ∀ i, 0 ≤ w i)
    (hA : ∀ n i, 0 ≤ A n i ∧ A n i ≤ z⁻¹)
    (hH : ∀ i, Tendsto (fun n => A n i) atTop (𝓝 (H i))) :
    Tendsto (fun n => update z w (A n)) atTop (𝓝 (update z w H)) := by
  have hs : Tendsto (fun n => ∑' i, w i * A n i) atTop (𝓝 (∑' i, w i * H i)) := by
    apply tendsto_tsum_of_dominated_convergence (hw.mul_right z⁻¹)
    · intro i
      exact tendsto_const_nhds.mul (hH i)
    · apply Eventually.of_forall
      intro n i
      rw [Real.norm_of_nonneg (mul_nonneg (hw₀ i) (hA n i).1)]
      exact mul_le_mul_of_nonneg_left (hA n i).2 (hw₀ i)
  have hnonneg : 0 ≤ ∑' i, w i * H i :=
    tsum_nonneg fun i => mul_nonneg (hw₀ i) (ge_of_tendsto' (hH i) fun n => (hA n i).1)
  exact (tendsto_const_nhds.add hs).inv₀ (add_pos_of_pos_of_nonneg hz hnonneg).ne'

/-- Summable outgoing weights suffice for the two extremal depth sequences to
converge to positive limits and satisfy the cross-recursions. Equality of the
limits on the Poisson tree is a further probabilistic step. -/
theorem exists_boundary_limits (z : ℝ) (child : V → ℕ → V) (w : V → ℕ → ℝ)
    (hz : 0 < z) (hw : ∀ v, Summable (w v)) (hw₀ : ∀ v i, 0 ≤ w v i) :
    ∃ L U : V → ℝ, ∀ v,
      Tendsto (fun n => (bounds z child w n v).1) atTop (𝓝 (L v)) ∧
      Tendsto (fun n => (bounds z child w n v).2) atTop (𝓝 (U v)) ∧
      0 < L v ∧ L v ≤ U v ∧ U v ≤ z⁻¹ ∧
      L v = update z (w v) (fun i => U (child v i)) ∧
      U v = update z (w v) (fun i => L (child v i)) := by
  let L : V → ℝ := fun v => ⨆ n, (bounds z child w n v).1
  let U : V → ℝ := fun v => ⨅ n, (bounds z child w n v).2
  let hmem := bounds_mem z child w hz hw hw₀
  have hL (v : V) : Tendsto (fun n => (bounds z child w n v).1) atTop (𝓝 (L v)) := by
    refine tendsto_atTop_ciSup
      (monotone_nat_of_le_succ fun n => (bounds_step z child w hz hw hw₀ n v).1) ?_
    exact ⟨z⁻¹, fun x ⟨n, hn⟩ => hn ▸ (hmem n v).2.1.trans (hmem n v).2.2⟩
  have hU (v : V) : Tendsto (fun n => (bounds z child w n v).2) atTop (𝓝 (U v)) := by
    refine tendsto_atTop_ciInf
      (antitone_nat_of_succ_le fun n => (bounds_step z child w hz hw hw₀ n v).2) ?_
    exact ⟨0, fun x ⟨n, hn⟩ => hn ▸ (hmem n v).1.trans (hmem n v).2.1⟩
  have hs : Tendsto (fun n : ℕ => n + 1) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_succ n) tendsto_id
  refine ⟨L, U, fun v => ⟨hL v, hU v, ?_, ?_, ?_, ?_, ?_⟩⟩
  · have hstart : 0 < (bounds z child w 1 v).1 :=
      (update_pos_le hz (hw₀ v) (fun _ => inv_nonneg.mpr hz.le)).1
    have hstart_le : (bounds z child w 1 v).1 ≤ L v := by
      apply ge_of_tendsto' ((hL v).comp hs)
      intro n
      exact (monotone_nat_of_le_succ fun k => (bounds_step z child w hz hw hw₀ k v).1)
        (Nat.succ_le_succ (Nat.zero_le n))
    exact hstart.trans_le hstart_le
  · exact le_of_tendsto_of_tendsto' (hL v) (hU v) fun n => (hmem n v).2.1
  · exact le_of_tendsto' (hU v) fun n => (hmem n v).2.2
  · refine tendsto_nhds_unique ((hL v).comp hs) ?_
    exact update_tendsto hz (hw v) (hw₀ v)
      (fun n i => ⟨(hmem n (child v i)).1.trans (hmem n (child v i)).2.1,
        (hmem n (child v i)).2.2⟩) (fun i => hU (child v i))
  · refine tendsto_nhds_unique ((hU v).comp hs) ?_
    exact update_tendsto hz (hw v) (hw₀ v)
      (fun n i => ⟨(hmem n (child v i)).1,
        (hmem n (child v i)).2.1.trans (hmem n (child v i)).2.2⟩) (fun i => hL (child v i))

end
end Certificate.TreeBoundary

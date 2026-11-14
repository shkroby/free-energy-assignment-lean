import Certificate.CanonicalTree

/-!
# Stability of the finite-depth tree bounds under length cutoffs

On the same tree, the truncated weights converge pointwise and are bounded
by the summable untruncated weights. This controls the full infinite series
at each depth without any monotonicity of the root message in the cutoff.
-/

open Filter Set
open scoped Topology

namespace Certificate.TreeBoundary

variable {V : Type*}

private theorem update_tendsto_of_weight_cutoff {z : ℝ} {w H : ℕ → ℝ}
    {W A : ℕ → ℕ → ℝ} (hz : 0 < z) (hw : Summable w)
    (hW : ∀ R i, 0 ≤ W R i ∧ W R i ≤ w i)
    (hA : ∀ R i, 0 ≤ A R i ∧ A R i ≤ z⁻¹)
    (hWlim : ∀ i, Tendsto (fun R ↦ W R i) atTop (𝓝 (w i)))
    (hAlim : ∀ i, Tendsto (fun R ↦ A R i) atTop (𝓝 (H i))) :
    Tendsto (fun R ↦ update z (W R) (A R)) atTop (𝓝 (update z w H)) := by
  have hsum : Tendsto (fun R ↦ ∑' i, W R i * A R i) atTop (𝓝 (∑' i, w i * H i)) := by
    apply tendsto_tsum_of_dominated_convergence (hw.mul_right z⁻¹)
    · intro i
      exact (hWlim i).mul (hAlim i)
    · refine Eventually.of_forall fun R i ↦ ?_
      rw [Real.norm_of_nonneg (mul_nonneg (hW R i).1 (hA R i).1)]
      exact mul_le_mul (hW R i).2 (hA R i).2 (hA R i).1 ((hW R i).1.trans (hW R i).2)
  have hnonneg : 0 ≤ ∑' i, w i * H i :=
    ge_of_tendsto' hsum fun R ↦ tsum_nonneg fun i ↦ mul_nonneg (hW R i).1 (hA R i).1
  exact (tendsto_const_nhds.add hsum).inv₀ (add_pos_of_pos_of_nonneg hz hnonneg).ne'

/-- Both finite-depth boundary approximations converge when outgoing
weights are approximated pointwise under their summable majorant. -/
theorem tendsto_bounds_of_weight_cutoff {z : ℝ} {child : V → ℕ → V}
    {W : ℕ → V → ℕ → ℝ} {w : V → ℕ → ℝ}
    (hz : 0 < z) (hw : ∀ v, Summable (w v))
    (hW : ∀ R v i, 0 ≤ W R v i ∧ W R v i ≤ w v i)
    (hlim : ∀ v i, Tendsto (fun R ↦ W R v i) atTop (𝓝 (w v i)))
    (depth : ℕ) (v : V) :
    Tendsto (fun R ↦ bounds z child (W R) depth v) atTop
      (𝓝 (bounds z child w depth v)) := by
  have hS (R : ℕ) (v : V) : Summable (W R v) :=
    Summable.of_nonneg_of_le (fun i ↦ (hW R v i).1) (fun i ↦ (hW R v i).2) (hw v)
  have hB (R : ℕ) (k : ℕ) (v : V) := bounds_mem z child (W R) hz (hS R)
    (fun v i ↦ (hW R v i).1) k v
  induction depth generalizing v with
  | zero => exact tendsto_const_nhds
  | succ depth ih =>
    refine Tendsto.prodMk_nhds ?_ ?_
    · exact update_tendsto_of_weight_cutoff hz (hw v) (fun R i ↦ hW R v i)
        (fun R i ↦ ⟨(hB R depth (child v i)).1.trans (hB R depth (child v i)).2.1,
          (hB R depth (child v i)).2.2⟩) (hlim v) (fun i ↦ (continuous_snd.tendsto _).comp (ih (child v i)))
    · exact update_tendsto_of_weight_cutoff hz (hw v) (fun R i ↦ hW R v i)
        (fun R i ↦ ⟨(hB R depth (child v i)).1,
          (hB R depth (child v i)).2.1.trans (hB R depth (child v i)).2.2⟩)
        (hlim v) (fun i ↦ (continuous_fst.tendsto _).comp (ih (child v i)))

/-- When the full-tree lower and upper limits agree, any messages between
the truncated lower and upper bounds at every depth converge to that limit. -/
theorem tendsto_of_between_weight_cutoff_bounds {z H : ℝ} {child : V → ℕ → V}
    {W : ℕ → V → ℕ → ℝ} {w : V → ℕ → ℝ} (v : V) (g : ℕ → ℝ)
    (hz : 0 < z) (hw : ∀ v, Summable (w v))
    (hW : ∀ R v i, 0 ≤ W R v i ∧ W R v i ≤ w v i)
    (hlim : ∀ v i, Tendsto (fun R ↦ W R v i) atTop (𝓝 (w v i)))
    (hL : Tendsto (fun k ↦ (bounds z child w k v).1) atTop (𝓝 H))
    (hU : Tendsto (fun k ↦ (bounds z child w k v).2) atTop (𝓝 H))
    (hg : ∀ R k, (bounds z child (W R) k v).1 ≤ g R ∧
      g R ≤ (bounds z child (W R) k v).2) :
    Tendsto g atTop (𝓝 H) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨k, hk⟩ := (hL.eventually (Ioi_mem_nhds ha)).exists
    have ht := (continuous_fst.tendsto _).comp (tendsto_bounds_of_weight_cutoff (child := child) hz hw hW hlim k v)
    filter_upwards [ht.eventually (Ioi_mem_nhds hk)] with R hR
    exact (show a < (bounds z child (W R) k v).1 from hR).trans_le (hg R k).1
  · intro a ha
    obtain ⟨k, hk⟩ := (hU.eventually (Iio_mem_nhds ha)).exists
    have ht := (continuous_snd.tendsto _).comp (tendsto_bounds_of_weight_cutoff (child := child) hz hw hW hlim k v)
    filter_upwards [ht.eventually (Iio_mem_nhds hk)] with R hR
    exact (hg R k).2.trans_lt (show (bounds z child (W R) k v).2 < a from hR)

end Certificate.TreeBoundary

namespace Certificate.CanonicalTree

/-- Weights on the same canonical tree with edges above length `R` set to zero. -/
noncomputable def cutoffWeight (β d : ℝ) (ω : Environment) (R : ℕ) (v : Vertex) (i : ℕ) : ℝ :=
  if arrivalLength d (ω v) i ≤ R then weight β d ω v i else 0

/-- Every finite-depth pair of cutoff bounds converges on the canonical
exponential tree as the cutoff grows. -/
theorem ae_tendsto_cutoff_bounds {β d z : ℝ} (hβ : 0 < β) (hd : 0 < d) (hz : 0 < z) :
    ∀ᵐ ω ∂law, ∀ k v,
      Tendsto (fun R ↦ TreeBoundary.bounds z child (cutoffWeight β d ω R) k v) atTop
        (𝓝 (depth β d z k v ω)) := by
  filter_upwards [ae_summable_weight hβ hd] with ω hω
  have hW (R : ℕ) (v : Vertex) (i : ℕ) :
      0 ≤ cutoffWeight β d ω R v i ∧ cutoffWeight β d ω R v i ≤ weight β d ω v i := by
    unfold cutoffWeight
    split
    · exact ⟨weight_nonneg β d ω v i, le_rfl⟩
    · exact ⟨le_rfl, weight_nonneg β d ω v i⟩
  have hlim (v : Vertex) (i : ℕ) :
      Tendsto (fun R ↦ cutoffWeight β d ω R v i) atTop (𝓝 (weight β d ω v i)) := by
    apply tendsto_const_nhds.congr'
    obtain ⟨R, hR⟩ := exists_nat_ge (arrivalLength d (ω v) i)
    filter_upwards [eventually_ge_atTop R] with N hN
    exact (if_pos (hR.trans (Nat.cast_le.mpr hN))).symm
  exact TreeBoundary.tendsto_bounds_of_weight_cutoff hz hω hW hlim

end Certificate.CanonicalTree

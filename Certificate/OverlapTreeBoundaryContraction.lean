import Certificate.TreeBoundary
import Certificate.OverlapBeliefContraction

/-! Uniformly bounded outgoing mass forces the two tree boundaries to agree. -/

open Filter Set Finset
open scoped Topology

namespace Certificate.TreeBoundary

variable {V : Type*}

/-- For a tree with finite outgoing support and a common bound on its total
outgoing weight, the two extremal depth recursions converge to one message. -/
theorem exists_common_boundary_limit_of_bounded_mass
    (child : V → ℕ → V) (w : V → ℕ → ℝ) (s : V → Finset ℕ)
    {z A : ℝ} (hz : 0 < z) (hA : 0 ≤ A)
    (hw : ∀ v i, 0 ≤ w v i) (hs : ∀ v i, i ∉ s v → w v i = 0)
    (hMass : ∀ v, ∑ i ∈ s v, w v i ≤ A) :
    ∃ H : V → ℝ, ∀ v,
      Tendsto (fun n => (bounds z child w n v).1) atTop (𝓝 (H v)) ∧
      Tendsto (fun n => (bounds z child w n v).2) atTop (𝓝 (H v)) ∧
      0 < H v ∧ H v ≤ z⁻¹ ∧
      H v = update z (w v) (fun i => H (child v i)) := by
  have hS (v : V) : Summable (w v) := (hasSum_sum_of_ne_finset_zero (hs v)).summable
  let L (n : ℕ) (v : V) := (bounds z child w n v).1
  let U (n : ℕ) (v : V) := (bounds z child w n v).2
  let r : ℝ := OverlapBelief.contractionRate z A
  let M := Real.log (z + A / z) - Real.log z
  have hr₀ : 0 ≤ r := (OverlapBelief.contractionRate z A).coe_nonneg
  have hr₁ : r < 1 :=
    NNReal.coe_lt_coe.mpr (OverlapBelief.contractionRate_lt_one hz hA)
  have hm : 0 < z + A / z := add_pos_of_pos_of_nonneg hz (div_nonneg hA hz.le)
  have hM : 0 ≤ M :=
    sub_nonneg.mpr (Real.log_le_log hz (le_add_of_nonneg_right (div_nonneg hA hz.le)))
  have hmem (n : ℕ) (v : V) : 0 ≤ L n v ∧ L n v ≤ U n v ∧ U n v ≤ z⁻¹ :=
    bounds_mem z child w hz hS hw n v
  have hMin (n : ℕ) (v : V) : (z + A/z)⁻¹ ≤ L (n+1) v := by
    change (z + A/z)⁻¹ ≤ (z + ∑' i, w v i * U n (child v i))⁻¹
    have hsum : (∑' i, w v i * U n (child v i)) ≤ A/z := by
      rw [tsum_eq_sum (s := s v) (fun i hi => by rw [hs v i hi, zero_mul]), div_eq_mul_inv]
      calc
        _ ≤ ∑ i ∈ s v, w v i * z⁻¹ :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hmem n (child v i)).2.2 (hw v i)
        _ ≤ _ := by rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (hMass v) (inv_nonneg.mpr hz.le)
    have hpos : 0 < z + ∑' i, w v i * U n (child v i) :=
      add_pos_of_pos_of_nonneg hz (tsum_nonneg fun i => mul_nonneg (hw v i)
        ((hmem n (child v i)).1.trans (hmem n (child v i)).2.1))
    exact inv_anti₀ hpos (add_le_add_right hsum z)
  have hPosL (n : ℕ) (v : V) : 0 < L (n+1) v := (inv_pos.mpr hm).trans_le (hMin n v)
  have hPosU (n : ℕ) (v : V) : 0 < U (n+1) v :=
    (hPosL n v).trans_le (hmem (n+1) v).2.1
  have hlogEq (v : V) (f : ℕ → ℝ) (hf : ∀ i, 0 < f i) :
      Real.log (update z (w v) f) =
        OverlapBelief.logUpdate z (s v) (w v) (fun i => Real.log (f i)) := by
    unfold update OverlapBelief.logUpdate
    rw [Real.log_inv, tsum_eq_sum (s := s v) (fun i hi => by rw [hs v i hi, zero_mul])]
    simp only [Real.exp_log (hf _)]
  have hrate : Real.exp (-Real.log z) * A / (z + Real.exp (-Real.log z) * A) = r := by
    dsimp only [r]
    rw [Real.exp_neg, Real.exp_log hz, OverlapBelief.coe_contractionRate hz hA]
    have hpos : 0 < z + z⁻¹ * A := add_pos_of_pos_of_nonneg hz (by positivity)
    have hpos₂ : 0 < z^2+A := add_pos_of_pos_of_nonneg (sq_pos_of_pos hz) hA
    field_simp [hz.ne', hpos.ne', hpos₂.ne']
  have hGap (n : ℕ) (v : V) :
      ‖Real.log (U (n+1) v) - Real.log (L (n+1) v)‖ ≤ r^n * M := by
    induction n generalizing v with
    | zero =>
      simp only [pow_zero, one_mul]
      have hlo := Real.log_le_log (inv_pos.mpr hm) (hMin 0 v)
      have hup := Real.log_le_log (hPosU 0 v) (hmem 1 v).2.2
      have hord := Real.log_le_log (hPosL 0 v) (hmem 1 v).2.1
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hord)]
      rw [Real.log_inv] at hlo hup
      dsimp only [M]
      linarith only [hlo, hup]
    | succ n ih =>
      change ‖Real.log (update z (w v) (fun i => L (n+1) (child v i))) -
        Real.log (update z (w v) (fun i => U (n+1) (child v i)))‖ ≤ _
      rw [hlogEq v _ (fun i => hPosL n (child v i)),
        hlogEq v _ (fun i => hPosU n (child v i))]
      have hx (u : V) : Real.log (L (n+1) u) ≤ -Real.log z := by
        rw [← Real.log_inv]
        exact Real.log_le_log (hPosL n u) ((hmem (n+1) u).2.1.trans (hmem (n+1) u).2.2)
      have hy (u : V) : Real.log (U (n+1) u) ≤ -Real.log z := by
        rw [← Real.log_inv]
        exact Real.log_le_log (hPosU n u) (hmem (n+1) u).2.2
      have hb := OverlapBelief.norm_logUpdate_sub_le (s v) hz hA
        (mul_nonneg (pow_nonneg hr₀ n) hM) (w v)
        (fun i => Real.log (L (n+1) (child v i))) (fun i => Real.log (U (n+1) (child v i)))
        (fun i _ => hw v i) (hMass v) (fun i _ => hx (child v i)) (fun i _ => hy (child v i))
        (fun i _ => by rw [norm_sub_rev]; exact ih (child v i))
      rw [hrate] at hb
      exact hb.trans_eq (by rw [pow_succ]; ring)
  obtain ⟨ℓ,u,h⟩ := exists_boundary_limits z child w hz hS hw
  have heq (v : V) : ℓ v = u v := by
    obtain ⟨hL,hU,hL₀,hLU,_,_,_⟩ := h v
    have hU₀ := hL₀.trans_le hLU
    have hShift : Tendsto (fun n : ℕ => n+1) atTop atTop := tendsto_add_atTop_nat 1
    have ha := (Real.continuousAt_log hL₀.ne').tendsto.comp (hL.comp hShift)
    have hb := (Real.continuousAt_log hU₀.ne').tendsto.comp (hU.comp hShift)
    have hD : Tendsto (fun n => ‖Real.log (U (n+1) v) - Real.log (L (n+1) v)‖)
        atTop (𝓝 ‖Real.log (u v) - Real.log (ℓ v)‖) := (hb.sub ha).norm
    have hZero : Tendsto (fun n => r^n*M) atTop (𝓝 0) := by
      simpa only [zero_mul] using (tendsto_pow_atTop_nhds_zero_of_lt_one hr₀ hr₁).mul_const M
    have hZ : Tendsto (fun n => ‖Real.log (U (n+1) v) - Real.log (L (n+1) v)‖)
        atTop (𝓝 0) := tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hZero
          (fun _ => norm_nonneg _) (fun n => hGap n v)
    have hLog : Real.log (u v) = Real.log (ℓ v) :=
      sub_eq_zero.mp (norm_eq_zero.mp (tendsto_nhds_unique hD hZ))
    exact (Real.strictMonoOn_log.injOn hU₀ hL₀ hLog).symm
  refine ⟨ℓ, fun v => ?_⟩
  obtain ⟨hL,hU,hL₀,_,hU₁,hRec,_⟩ := h v
  rw [← heq v] at hU hU₁
  refine ⟨hL,hU,hL₀,hU₁,?_⟩
  simpa only [← heq] using hRec

end Certificate.TreeBoundary

import Certificate.OverlapBeliefApproximation

/-! The Bethe pressure approximation for sequences of locally compatible
bounded-degree graphs. -/

open Filter Finset
open scoped Topology

namespace Certificate.OverlapBelief

/-- Select the common high-fugacity cutoff, depth and bad-root tolerance
to guarantee a specified error per vertex scale. -/
theorem exists_approximation_parameters (t : ℝ) {A C ε : ℝ}
    (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ (T : ℝ) (k : ℕ) (b : ℝ), t ≤ T ∧ 0 < b ∧
      (T-t) * (b + C * ((contractionRate (Real.exp t) A : ℝ)^k * (A/(Real.exp t)^2))) +
        2*C*(A/(Real.exp T)^2) < ε := by
  let r : ℝ := contractionRate (Real.exp t) A
  let B : ℝ := A / (Real.exp t)^2
  have hr : 0 ≤ r := (contractionRate (Real.exp t) A).coe_nonneg
  have hr₁ : r < 1 := NNReal.coe_lt_coe.mpr (contractionRate_lt_one (Real.exp_pos t) hA)
  have hP : Tendsto (fun s : ℝ => 2*C*(A/(Real.exp s)^2)) atTop (𝓝 0) := by
    have ht : Tendsto (fun s : ℝ => -2*s) atTop atBot := by
      simpa using tendsto_id.const_mul_atTop_of_neg (show (-2 : ℝ) < 0 by norm_num)
    have h := (Real.tendsto_exp_atBot.comp ht).const_mul (2*C*A)
    have hf : (fun s : ℝ => 2*C*(A/(Real.exp s)^2)) =
        fun s : ℝ => 2*C*A*Real.exp (-2*s) := by
      funext s
      rw [pow_two, ← Real.exp_add, div_eq_mul_inv, ← Real.exp_neg, mul_assoc (2*C)]
      congr 3
      ring
    rw [hf]
    simpa only [Function.comp_apply, mul_zero] using h
  have hthird : 0 < ε/3 := by positivity
  obtain ⟨T, htT, htail⟩ := ((eventually_ge_atTop t).and (hP.eventually_lt_const hthird)).exists
  have hG : Tendsto (fun k : ℕ => (T-t)*C*(r^k*B)) atTop (𝓝 0) := by
    have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one hr hr₁).mul_const B).const_mul ((T-t)*C)
    simpa only [zero_mul, mul_zero] using h
  obtain ⟨k,hgeo⟩ := (hG.eventually_lt_const hthird).exists
  let b := (ε/3)/(1+T-t)
  have hgap : 0 < 1+T-t := by linarith only [htT]
  have hb : 0 < b := div_pos hthird hgap
  have hbd : (T-t)*b ≤ ε/3 := by
    dsimp only [b]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hgap).mpr
    have h : T-t ≤ 1+T-t := by linarith
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right h hthird.le
  refine ⟨T,k,b,htT,hb,?_⟩
  change (T-t)*(b+C*(r^k*B)) + 2*C*(A/(Real.exp T)^2) < ε
  calc
    _ = (T-t)*b + (T-t)*C*(r^k*B) + 2*C*(A/(Real.exp T)^2) := by ring
    _ < ε := by linarith only [hbd,hgeo,htail]

/-- Substitute the vertex and bad-root count bounds into the pressure
approximation remainder before normalization. -/
theorem approximation_error_le {t T A C b mass N bad : ℝ} (htT : t ≤ T) (hA : 0 ≤ A)
    (k : ℕ) (hSize : N ≤ C*mass) (hBad : bad ≤ b*mass) :
    (T-t)*(bad+N*((contractionRate (Real.exp t) A : ℝ)^k*(A/(Real.exp t)^2))) +
      2*N*(A/(Real.exp T)^2) ≤
    ((T-t)*(b+C*((contractionRate (Real.exp t) A : ℝ)^k*(A/(Real.exp t)^2))) +
      2*C*(A/(Real.exp T)^2))*mass := by
  let D := (contractionRate (Real.exp t) A : ℝ)^k*(A/(Real.exp t)^2)
  let B := A/(Real.exp T)^2
  have hD : 0 ≤ D := mul_nonneg
    (pow_nonneg (contractionRate (Real.exp t) A).coe_nonneg _) (div_nonneg hA (sq_nonneg _))
  have hB : 0 ≤ B := div_nonneg hA (sq_nonneg _)
  change (T-t)*(bad+N*D)+2*N*B ≤ ((T-t)*(b+C*D)+2*C*B)*mass
  calc
    _ ≤ (T-t)*(b*mass+(C*mass)*D)+2*(C*mass)*B := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (add_le_add hBad (mul_le_mul_of_nonneg_right hSize hD))
          (sub_nonneg.mpr htT))
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSize (by norm_num)) hB)
    _ = _ := by ring

/-- An (o(n)) deterministic Bethe error for every sequence of positive
weights with the same incident weight bound. Only the fraction of roots
with compatible neighborhoods is required to converge at each fixed depth. -/
theorem tendsto_logPartition_sub_betheLog_div
    {V E : ℕ → Type*} [∀ n, DecidableEq (V n)] [∀ n, DecidableEq (E n)]
    [∀ n, Fintype (V n)] [∀ n, Fintype (E n)]
    (G : ∀ n, WeightedGraph (V n) (E n)) (t : ℝ)
    {A C : ℝ} (hA : 0 ≤ A) (hW : ∀ n, IncidentWeightBound (G n) A)
    (hw : ∀ n e, e ∈ (G n).edges → 0 < (G n).weight e)
    (hSize : ∀ n > 0, ((G n).vertices.card : ℝ) / (n : ℝ) ≤ C)
    (good : ∀ (_k : ℕ) (n : ℕ), Finset (V n))
    (hgood : ∀ k n, good k n ⊆ (G n).vertices)
    (hcompat : ∀ k n v, v ∈ good k n → goodRoot (G n) k v)
    (hBad : ∀ k, Tendsto (fun n : ℕ => (((G n).vertices \ good k n).card : ℝ) / (n : ℝ))
      atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (Real.log ((G n).Z t) - betheLog (G n) hA (hW n) t) / (n : ℝ))
      atTop (𝓝 0) := by
  let r : ℝ := contractionRate (Real.exp t) A
  let B : ℝ := A/(Real.exp t)^2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hr : 0 ≤ r := (contractionRate (Real.exp t) A).coe_nonneg
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨T,k,b,htT,hb,hbudget⟩ := exists_approximation_parameters t (C := C) hA hε
  filter_upwards [eventually_gt_atTop (0 : ℕ), (hBad k).eventually_lt_const hb] with n hn hbad
  have hN : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hs := hSize n hn
  have he := norm_logPartition_sub_betheLog_le (G n) hA (hW n) (hw n) htT k
    (good k n) (hgood k n) (fun v => hcompat k n v)
  rw [dist_zero_right, norm_div, Real.norm_of_nonneg hN.le]
  refine (div_le_div_of_nonneg_right he hN.le).trans_lt ?_
  let N := ((G n).vertices.card : ℝ)
  let nb := (((G n).vertices \ good k n).card : ℝ)
  let D := A/(Real.exp T)^2
  change ((T-t)*(nb+N*(r^k*B))+2*N*D)/(n : ℝ) < ε
  calc
    _ = (T-t)*(nb/(n : ℝ)) + (T-t)*(N/(n : ℝ))*(r^k*B) + 2*(N/(n : ℝ))*D := by ring
    _ ≤ (T-t)*(nb/(n : ℝ)) + (T-t)*C*(r^k*B) + 2*C*D := by
      have hD : 0 ≤ D := div_nonneg hA (sq_nonneg _)
      exact add_le_add
        (add_le_add le_rfl
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (sub_nonneg.mpr htT))
            (mul_nonneg (pow_nonneg hr _) hB)))
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by norm_num)) hD)
    _ ≤ (T-t)*(b+C*(r^k*B)) + 2*C*D := by
      have h := mul_le_mul_of_nonneg_left hbad.le (sub_nonneg.mpr htT)
      linarith only [h]
    _ < ε := hbudget

end Certificate.OverlapBelief

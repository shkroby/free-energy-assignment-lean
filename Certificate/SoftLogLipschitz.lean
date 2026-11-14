import Certificate.TreeBoundary
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Log-fugacity regularity of the tree messages

The cavity update sends multiplicatively comparable child messages to
multiplicatively comparable parent messages when fugacity is varied.
The comparison survives the depth limit and proves the pathwise Lipschitz
bound used to differentiate the Bethe pressure.
-/

open Filter
open scoped Topology

namespace Certificate.TreeBoundary

variable {V : Type*}

private theorem inverse_le_mul_inverse {a b c : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : b ≤ c * a) : a⁻¹ ≤ c * b⁻¹ := by
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ hb).mpr
  rw [mul_comm, ← div_eq_mul_inv]
  exact (div_le_iff₀ ha).mpr h

private theorem summable_mul_of_bounded {w a : ℕ → ℝ} {B : ℝ} (hw : Summable w)
    (hw₀ : ∀ i, 0 ≤ w i) (h₀ : ∀ i, 0 ≤ a i) (hB : ∀ i, a i ≤ B) :
    Summable (fun i => w i * a i) :=
  Summable.of_nonneg_of_le (fun i => mul_nonneg (hw₀ i) (h₀ i))
    (fun i => mul_le_mul_of_nonneg_left (hB i) (hw₀ i)) (hw.mul_right B)

private theorem weighted_sum_le_scaled {w a b : ℕ → ℝ} {c : ℝ}
    (hw : ∀ i, 0 ≤ w i) (ha : Summable (fun i => w i * a i))
    (hb : Summable (fun i => w i * b i)) (hab : ∀ i, a i ≤ c * b i) :
    (∑' i, w i * a i) ≤ c * ∑' i, w i * b i := by
  rw [← hb.tsum_mul_left]
  exact ha.tsum_le_tsum (fun i => by
    calc
      _ ≤ w i * (c * b i) := mul_le_mul_of_nonneg_left (hab i) (hw i)
      _ = c * (w i * b i) := by ring) (hb.mul_left c)

/-- The cavity update respects a simultaneous (c)-factor change in fugacity
and in all child messages, measured in both directions. -/
theorem update_scaled_comparison {z c A B : ℝ} {w a b : ℕ → ℝ}
    (hz : 0 < z) (hc : 1 ≤ c) (hw : Summable w) (hw₀ : ∀ i, 0 ≤ w i)
    (ha₀ : ∀ i, 0 ≤ a i) (hb₀ : ∀ i, 0 ≤ b i)
    (haB : ∀ i, a i ≤ A) (hbB : ∀ i, b i ≤ B)
    (h : ∀ i, a i ≤ c * b i ∧ b i ≤ c * a i) :
    update z w a ≤ c * update (c * z) w b ∧
      update (c * z) w b ≤ c * update z w a := by
  have hc₀ : 0 < c := zero_lt_one.trans_le hc
  have ha := summable_mul_of_bounded hw hw₀ ha₀ haB
  have hb := summable_mul_of_bounded hw hw₀ hb₀ hbB
  have hA : 0 < z + ∑' i, w i * a i := by
    exact add_pos_of_pos_of_nonneg hz (tsum_nonneg fun i => mul_nonneg (hw₀ i) (ha₀ i))
  have hB : 0 < c * z + ∑' i, w i * b i := by
    exact add_pos_of_pos_of_nonneg (mul_pos hc₀ hz)
      (tsum_nonneg fun i => mul_nonneg (hw₀ i) (hb₀ i))
  unfold update
  constructor
  · apply inverse_le_mul_inverse hA hB
    rw [mul_add]
    exact add_le_add le_rfl (weighted_sum_le_scaled hw₀ hb ha fun i => (h i).2)
  · apply inverse_le_mul_inverse hB hA
    rw [mul_add]
    have hz₁ : z ≤ c * z := le_mul_of_one_le_left hz.le hc
    have hz₂ : c * z ≤ c * (c * z) := mul_le_mul_of_nonneg_left hz₁ hc₀.le
    exact add_le_add (hz₁.trans hz₂) (weighted_sum_le_scaled hw₀ ha hb fun i => (h i).1)

/-- The two extremal depth approximations on a fixed tree obey the same
multiplicative comparison. -/
theorem bounds_scaled_comparison (z c : ℝ) (child : V → ℕ → V) (w : V → ℕ → ℝ)
    (hz : 0 < z) (hc : 1 ≤ c) (hw : ∀ v, Summable (w v)) (hw₀ : ∀ v i, 0 ≤ w v i)
    (n : ℕ) (v : V) :
    ((bounds z child w n v).1 ≤ c * (bounds (c * z) child w n v).1 ∧
      (bounds (c * z) child w n v).1 ≤ c * (bounds z child w n v).1) ∧
    ((bounds z child w n v).2 ≤ c * (bounds (c * z) child w n v).2 ∧
      (bounds (c * z) child w n v).2 ≤ c * (bounds z child w n v).2) := by
  have hc₀ : 0 < c := zero_lt_one.trans_le hc
  have hz' := mul_pos hc₀ hz
  induction n generalizing v with
  | zero =>
    have h₁ : z ≤ c * z := le_mul_of_one_le_left hz.le hc
    have h₂ : c * z ≤ c * (c * z) := mul_le_mul_of_nonneg_left h₁ hc₀.le
    exact ⟨by simp [bounds], inverse_le_mul_inverse hz hz' le_rfl,
      inverse_le_mul_inverse hz' hz (h₁.trans h₂)⟩
  | succ n ih =>
    let K i := bounds_mem z child w hz hw hw₀ n (child v i)
    let K' i := bounds_mem (c * z) child w hz' hw hw₀ n (child v i)
    exact ⟨
      update_scaled_comparison hz hc (hw v) (hw₀ v)
        (fun i => (K i).1.trans (K i).2.1) (fun i => (K' i).1.trans (K' i).2.1)
        (fun i => (K i).2.2) (fun i => (K' i).2.2) (fun i => (ih (child v i)).2),
      update_scaled_comparison hz hc (hw v) (hw₀ v)
        (fun i => (K i).1) (fun i => (K' i).1)
        (fun i => (K i).2.1.trans (K i).2.2) (fun i => (K' i).2.1.trans (K' i).2.2)
        (fun i => (ih (child v i)).1)⟩

private theorem lipschitz_log_of_scaled_comparison {H : ℝ → ℝ} (hp : ∀ t, 0 < H t)
    (h : ∀ t s, t ≤ s → H t ≤ Real.exp (s - t) * H s ∧ H s ≤ Real.exp (s - t) * H t) :
    LipschitzWith 1 (fun t => Real.log (H t)) := by
  have hab (t s : ℝ) (hts : t ≤ s) : dist (Real.log (H t)) (Real.log (H s)) ≤ dist t s := by
    have h₁ := Real.log_le_log (hp t) (h t s hts).1
    have h₂ := Real.log_le_log (hp s) (h t s hts).2
    rw [Real.log_mul (Real.exp_pos _).ne' (hp s).ne', Real.log_exp] at h₁
    rw [Real.log_mul (Real.exp_pos _).ne' (hp t).ne', Real.log_exp] at h₂
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hts)]
    apply abs_le.mpr
    constructor <;> linarith only [h₁, h₂]
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro t s
  simp only [NNReal.coe_one, one_mul]
  rcases le_total t s with hts | hst
  · exact hab t s hts
  · rw [dist_comm t s, dist_comm (Real.log (H t)) (Real.log (H s))]
    exact hab s t hst

/-- The logarithms of both limiting extremal messages are 1-Lipschitz in log
fugacity on any deterministic tree with summable outgoing weights. -/
theorem exists_logLipschitz_boundary (child : V → ℕ → V) (w : V → ℕ → ℝ)
    (hw : ∀ v, Summable (w v)) (hw₀ : ∀ v i, 0 ≤ w v i) :
    ∃ L U : ℝ → V → ℝ,
      (∀ t v, Tendsto (fun n => (bounds (Real.exp t) child w n v).1) atTop (𝓝 (L t v)) ∧
        Tendsto (fun n => (bounds (Real.exp t) child w n v).2) atTop (𝓝 (U t v))) ∧
      (∀ t v, 0 < L t v ∧ 0 < U t v) ∧
      (∀ v, LipschitzWith 1 (fun t => Real.log (L t v))) ∧
      (∀ v, LipschitzWith 1 (fun t => Real.log (U t v))) := by
  choose L U h using (fun t : ℝ =>
    exists_boundary_limits (Real.exp t) child w (Real.exp_pos t) hw hw₀)
  have hk (t s : ℝ) (hts : t ≤ s) (n : ℕ) (v : V) :
      ((bounds (Real.exp t) child w n v).1 ≤ Real.exp (s-t) * (bounds (Real.exp s) child w n v).1 ∧
        (bounds (Real.exp s) child w n v).1 ≤ Real.exp (s-t) * (bounds (Real.exp t) child w n v).1) ∧
      ((bounds (Real.exp t) child w n v).2 ≤ Real.exp (s-t) * (bounds (Real.exp s) child w n v).2 ∧
        (bounds (Real.exp s) child w n v).2 ≤ Real.exp (s-t) * (bounds (Real.exp t) child w n v).2) := by
    have hscale : Real.exp (s - t) * Real.exp t = Real.exp s := by
      rw [← Real.exp_add, sub_add_cancel]
    have hh := bounds_scaled_comparison (Real.exp t) (Real.exp (s - t))
      child w (Real.exp_pos t) (Real.one_le_exp (sub_nonneg.mpr hts)) hw hw₀ n v
    rwa [hscale] at hh
  have hpos (t : ℝ) (v : V) : 0 < L t v ∧ 0 < U t v :=
    ⟨(h t v).2.2.1, (h t v).2.2.1.trans_le (h t v).2.2.2.1⟩
  refine ⟨L, U, fun t v => ⟨(h t v).1, (h t v).2.1⟩, hpos, ?_, ?_⟩
  · intro v
    apply lipschitz_log_of_scaled_comparison (fun t => (hpos t v).1)
    intro t s hts
    exact ⟨
      le_of_tendsto_of_tendsto' (h t v).1 ((h s v).1.const_mul _)
        (fun n => (hk t s hts n v).1.1),
      le_of_tendsto_of_tendsto' (h s v).1 ((h t v).1.const_mul _)
        (fun n => (hk t s hts n v).1.2)⟩
  · intro v
    apply lipschitz_log_of_scaled_comparison (fun t => (hpos t v).2)
    intro t s hts
    exact ⟨
      le_of_tendsto_of_tendsto' (h t v).2.1 ((h s v).2.1.const_mul _)
        (fun n => (hk t s hts n v).2.1),
      le_of_tendsto_of_tendsto' (h s v).2.1 ((h t v).2.1.const_mul _)
        (fun n => (hk t s hts n v).2.2)⟩

end Certificate.TreeBoundary

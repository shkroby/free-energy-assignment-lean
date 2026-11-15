import Certificate.LocalTreeShapeMass
import Mathlib.Data.Fintype.CardEmbedding

/-!
# Distinct placements of a finite rooted bipartite shape

Prescribing the root label excludes it from one class. The remaining
symbolic vertices have injective placements in the two classes, with
the expected falling-factorial counts.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace Certificate.LocalExploration

/-- Place the non-root vertices of a finite symbolic bipartite shape.
The excluded label is the prescribed root in the left class. -/
abbrev RootedBipartitePlacement (a b n : ℕ) :=
  (Fin a ↪ Fin (n - 1)) × (Fin b ↪ Fin n)

theorem card_rootedBipartitePlacement (a b n : ℕ) :
    Fintype.card (RootedBipartitePlacement a b n) =
      (n - 1).descFactorial a * n.descFactorial b := by
  simp [RootedBipartitePlacement]

private theorem tendsto_descFactorial_div_pow (k : ℕ) :
    Tendsto (fun n : ℕ => (n.descFactorial k : ℝ) / (n : ℝ)^k) atTop (𝓝 1) := by
  let p (n : ℕ) : ℝ := (n : ℝ)⁻¹
  have hp : Tendsto (fun n : ℕ => (n : ℝ)*p n) atTop (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact (mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hn.ne')).symm
  have ht := (tendsto_choose_mul_pow_atTop k hp).const_mul (k.factorial : ℝ)
  have hf : (k.factorial : ℝ) * ((1 : ℝ)^k / k.factorial) = 1 := by
    rw [one_pow, one_div, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k))]
  rw [hf] at ht
  simpa only [p, Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, div_eq_mul_inv,
    inv_pow, mul_assoc] using ht

private theorem tendsto_cast_sub_div_natCast (s : ℕ) :
    Tendsto (fun n : ℕ => ((n - s : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 1) := by
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hx := (hi.const_mul (s : ℝ)).const_sub (1 : ℝ)
  simp only [mul_zero, sub_zero] at hx
  refine hx.congr' ?_
  filter_upwards [eventually_ge_atTop s, eventually_gt_atTop (0 : ℕ)] with n hn hn₀
  rw [Nat.cast_sub hn, sub_div, div_self (Nat.cast_ne_zero.mpr hn₀.ne'), div_eq_mul_inv]

private theorem tendsto_shifted_descFactorial_div_pow (k s : ℕ) :
    Tendsto (fun n : ℕ => ((n - s).descFactorial k : ℝ) / (n : ℝ)^k) atTop (𝓝 1) := by
  have h := ((tendsto_descFactorial_div_pow k).comp (tendsto_sub_atTop_nat s)).mul
    ((tendsto_cast_sub_div_natCast s).pow k)
  simp only [one_pow, mul_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop s] with n hn
  change (((n - s).descFactorial k : ℝ) / ((n - s : ℕ) : ℝ)^k) *
    (((n - s : ℕ) : ℝ) / (n : ℝ))^k = ((n - s).descFactorial k : ℝ) / (n : ℝ)^k
  have hden : ((n - s : ℕ) : ℝ)^k ≠ 0 := pow_ne_zero k
    (Nat.cast_ne_zero.mpr (Nat.sub_ne_zero_of_lt hn))
  rw [div_pow, div_mul_div_comm]
  rw [mul_comm (((n - s : ℕ) : ℝ)^k) ((n : ℝ)^k)]
  exact mul_div_mul_right _ _ hden

/-- The number of injective labelled placements, divided by the
corresponding power of the class size, tends to one. -/
theorem tendsto_normalized_card_rootedBipartitePlacement (a b : ℕ) :
    Tendsto (fun n : ℕ => (Fintype.card (RootedBipartitePlacement a b n) : ℝ) /
      (n : ℝ)^(a+b)) atTop (𝓝 1) := by
  have h := (tendsto_shifted_descFactorial_div_pow a 1).mul (tendsto_descFactorial_div_pow b)
  simp only [mul_one] at h
  refine h.congr' (.of_forall fun n => ?_)
  change ((n - 1).descFactorial a : ℝ) / (n : ℝ)^a * ((n.descFactorial b : ℝ) / (n : ℝ)^b) =
    (Fintype.card (RootedBipartitePlacement a b n) : ℝ) / (n : ℝ)^(a+b)
  rw [card_rootedBipartitePlacement, Nat.cast_mul, pow_add, div_mul_div_comm]

end Certificate.LocalExploration

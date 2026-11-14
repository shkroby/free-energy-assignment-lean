import Certificate.CompletionProbability

/-!
# Summing logarithmic augmentation costs

A power of the logarithm is bounded by a square root in the deficit ratio.
The resulting inverse square roots telescope after a simple comparison.
-/

open Finset
open scoped BigOperators

namespace Certificate.Completion

private theorem log_add_one_rpow_le_sqrt {y b : ℝ} (hy : 1 ≤ y) (hb : 0 < b) :
    (1 + Real.log y) ^ b ≤ (1 + 2 * b) ^ b * Real.sqrt y := by
  have hy₀ : 0 < y := zero_lt_one.trans_le hy
  let a : ℝ := 1 / (2 * b)
  have ha : 0 < a := div_pos zero_lt_one (by positivity)
  have hya : 1 ≤ y ^ a := Real.one_le_rpow hy ha.le
  have hlog := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hy₀ a)
  rw [Real.log_rpow hy₀] at hlog
  have hmul := mul_le_mul_of_nonneg_right hlog (show 0 ≤ 2 * b by positivity)
  have hcan : (a * Real.log y) * (2 * b) = Real.log y := by dsimp [a]; field_simp
  rw [hcan] at hmul
  have hup : 1 + Real.log y ≤ (1 + 2 * b) * y ^ a := by nlinarith
  calc
    _ ≤ ((1 + 2 * b) * y ^ a) ^ b :=
      Real.rpow_le_rpow (by linarith [Real.log_nonneg hy]) hup hb.le
    _ = _ := by
      rw [Real.mul_rpow (by positivity : 0 ≤ 1 + 2 * b) (Real.rpow_nonneg hy₀.le _),
        ← Real.rpow_mul hy₀.le, Real.sqrt_eq_rpow]
      have ha' : a * b = 1 / 2 := by dsimp [a]; field_simp
      rw [ha']

private theorem sum_inv_sqrt_succ_le (k : ℕ) :
    ∑ j ∈ range k, 1 / Real.sqrt ((j : ℝ) + 1) ≤ 2 * Real.sqrt (k : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    let a := Real.sqrt ((k : ℝ) + 1)
    let b := Real.sqrt (k : ℝ)
    have ha : 0 < a := Real.sqrt_pos.2 (by positivity)
    have hba : b ≤ a := Real.sqrt_le_sqrt (by linarith)
    have hbal : (a - b) * (a + b) = 1 := by
      dsimp [a, b]
      nlinarith [Real.sq_sqrt (by positivity : 0 ≤ (k : ℝ) + 1), Real.sq_sqrt (by positivity : 0 ≤ (k : ℝ))]
    have hterm : 1 / a ≤ 2 * (a - b) := by
      apply (div_le_iff₀ ha).2
      calc
        _ = (a - b) * (a + b) := hbal.symm
        _ ≤ (a - b) * (2 * a) := mul_le_mul_of_nonneg_left (by linarith) (sub_nonneg.mpr hba)
        _ = _ := by ring
    rw [Finset.sum_range_succ, Nat.cast_succ]
    change _ + 1 / a ≤ 2 * a
    linarith

private theorem sum_sqrt_ratio_le (k : ℕ) :
    ∑ j ∈ range k, Real.sqrt ((k : ℝ) / ((j : ℝ) + 1)) ≤ 2 * (k : ℝ) := by
  calc
    _ = Real.sqrt (k : ℝ) * ∑ j ∈ range k, 1 / Real.sqrt ((j : ℝ) + 1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [Real.sqrt_div (by positivity : 0 ≤ (k : ℝ))]
      ring
    _ ≤ Real.sqrt (k : ℝ) * (2 * Real.sqrt (k : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_inv_sqrt_succ_le k) (Real.sqrt_nonneg _)
    _ = _ := by nlinarith [Real.sq_sqrt (by positivity : 0 ≤ (k : ℝ))]

/-- Uniformly for a final deficit `k ≤ n`, summing positive powers of the
logarithmic cost over all intermediate deficits costs only a constant times
`k * log(e n/k)^b`. -/
theorem sum_expansionLog_rpow_le {n k : ℕ} {b : ℝ}
    (hk : 0 < k) (hkn : k ≤ n) (hb : 0 < b) :
    ∑ j ∈ range k, expansionLog n (j + 1) ^ b ≤
      (2 * (1 + 2 * b) ^ b) * k * expansionLog n k ^ b := by
  have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
  have hn' : 0 < (n : ℝ) := hk'.trans_le (by exact_mod_cast hkn)
  let L := expansionLog n k
  let F := (1 + 2 * b) ^ b
  have hL : 1 ≤ L := expansionLog_ge_one hk hkn
  have hterm (j : ℕ) (hj : j ∈ range k) :
      expansionLog n (j + 1) ^ b ≤ (L ^ b * F) * Real.sqrt ((k : ℝ) / ((j : ℝ) + 1)) := by
    let z : ℝ := (j : ℝ) + 1
    have hz : 0 < z := by dsimp [z]; positivity
    have hzk : z ≤ (k : ℝ) := by
      have hjk : j + 1 ≤ k := Finset.mem_range.mp hj
      dsimp [z]
      exact_mod_cast hjk
    let y := (k : ℝ) / z
    have hy : 1 ≤ y := (one_le_div hz).2 hzk
    have hlog := Real.log_nonneg hy
    have hsplit : expansionLog n (j + 1) = L + Real.log y := by
      change 1 + Real.log ((n : ℝ) / ((j + 1 : ℕ) : ℝ)) =
        (1 + Real.log ((n : ℝ) / k)) + Real.log ((k : ℝ) / z)
      rw [Nat.cast_add, Nat.cast_one, Real.log_div hn'.ne' hz.ne',
        Real.log_div hn'.ne' hk'.ne', Real.log_div hk'.ne' hz.ne']
      ring
    have hm : L + Real.log y ≤ L * (1 + Real.log y) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hL) hlog]
    calc
      _ ≤ (L * (1 + Real.log y)) ^ b := by
        rw [hsplit]
        exact Real.rpow_le_rpow (by linarith) hm hb.le
      _ = L ^ b * (1 + Real.log y) ^ b := Real.mul_rpow (by linarith) (by linarith)
      _ ≤ L ^ b * (F * Real.sqrt y) := mul_le_mul_of_nonneg_left
        (log_add_one_rpow_le_sqrt hy hb) (Real.rpow_nonneg (by linarith) _)
      _ = _ := by rw [mul_assoc]
  calc
    _ ≤ ∑ j ∈ range k, (L ^ b * F) * Real.sqrt ((k : ℝ) / ((j : ℝ) + 1)) :=
      Finset.sum_le_sum hterm
    _ = (L ^ b * F) * ∑ j ∈ range k, Real.sqrt ((k : ℝ) / ((j : ℝ) + 1)) :=
      (Finset.mul_sum ..).symm
    _ ≤ (L ^ b * F) * (2 * (k : ℝ)) := mul_le_mul_of_nonneg_left (sum_sqrt_ratio_le k)
      (mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by positivity) _))
    _ = _ := by dsimp [L, F]; ring

end Certificate.Completion

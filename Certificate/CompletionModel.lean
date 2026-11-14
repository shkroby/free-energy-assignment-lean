import Certificate.Completion
import Certificate.CompletionPath
import Certificate.Model
import Certificate.Removal

/-!
# Completion bounds for the assignment model

This connects the deterministic weighted completion bound to the actual finite
partition functions. The probability estimate for the existence of suitable
completion maps is a separate step.
-/

open scoped BigOperators
open Finset

namespace Certificate.Completion

/-- The cost matrix after the pseudodimension scaling of the manuscript. -/
noncomputable def scaledCost (d κ : ℝ) (n : ℕ) (C : CostArray) : Fin n → Fin n → ℝ :=
  fun i j => lengthScale d κ n * C (i.val, j.val)

/-- The partial matchings with exactly `k` free rows. -/
noncomputable def matchingsAtDeficit (n k : ℕ) : Finset (Fin n → Option (Fin n)) :=
  open Classical in
  univ.filter fun m => IsMatching m ∧ (AugmentingPath.matchedRows m).card + k = n

@[simp] theorem mem_matchingsAtDeficit {n k : ℕ} {m : Fin n → Option (Fin n)} :
    m ∈ matchingsAtDeficit n k ↔
      IsMatching m ∧ (AugmentingPath.matchedRows m).card + k = n := by
  classical
  simp [matchingsAtDeficit]

/-- The sum of the weights of all partial matchings at a fixed deficit. -/
noncomputable def deficitPartition (β d κ : ℝ) (n k : ℕ) (C : CostArray) : ℝ :=
  ∑ m ∈ matchingsAtDeficit n k, partialWeight β (scaledCost d κ n C) m

theorem deficitPartition_nonneg (β d κ : ℝ) (n k : ℕ) (C : CostArray) :
    0 ≤ deficitPartition β d κ n k C :=
  Finset.sum_nonneg fun m _ => (partialWeight_pos β (scaledCost d κ n C) m).le

theorem assignmentPartition_eq_sum_perfectWeight (β d κ : ℝ) (n : ℕ) (C : CostArray) :
    assignmentPartition β d κ n C =
      ∑ p : Equiv.Perm (Fin n), perfectWeight β (scaledCost d κ n C) p := by
  unfold assignmentPartition permanent perfectWeight partialWeight
  refine Finset.sum_congr rfl fun p _ => Finset.prod_congr rfl fun i _ => ?_
  simp only [rowWeight_some, scaledCost]
  congr 1
  ring

/-- A zero-deficit partial matching is a permutation. -/
theorem mem_matchingsAtDeficit_zero_iff_permutation {n : ℕ} (m : Fin n → Option (Fin n)) :
    m ∈ matchingsAtDeficit n 0 ↔ ∃ p : Equiv.Perm (Fin n), (fun i => some (p i)) = m := by
  classical
  constructor
  · intro h
    rcases mem_matchingsAtDeficit.mp h with ⟨hm, hc⟩
    have hs : AugmentingPath.matchedRows m = univ :=
      Finset.eq_univ_of_card _ (by simpa using hc)
    have hex (i : Fin n) : ∃ j, m i = some j := by
      have hi : m i ≠ none := AugmentingPath.mem_matchedRows.mp (hs.symm ▸ Finset.mem_univ i)
      cases hmi : m i with
      | none => exact (hi hmi).elim
      | some j => exact ⟨j, rfl⟩
    let f : Fin n → Fin n := fun i => Classical.choose (hex i)
    have hf (i : Fin n) : m i = some (f i) := Classical.choose_spec (hex i)
    have hfinj : Function.Injective f := fun i j hij => hm (hf i) ((hf j).trans (congrArg some hij.symm))
    let p : Equiv.Perm (Fin n) := Equiv.ofBijective f
      ⟨hfinj, (Finite.injective_iff_surjective (f := f)).mp hfinj⟩
    exact ⟨p, funext fun i => (hf i).symm⟩
  · rintro ⟨p, rfl⟩
    apply mem_matchingsAtDeficit.mpr
    constructor
    · intro i j c hi hj
      exact p.injective (Option.some.inj (hi.trans hj.symm))
    · have hu : AugmentingPath.matchedRows (fun i => some (p i)) = univ := by
        ext i
        simp
      simp [hu]

/-- The zero-deficit partition function is the perfect assignment permanent. -/
theorem deficitPartition_zero (β d κ : ℝ) (n : ℕ) (C : CostArray) :
    deficitPartition β d κ n 0 C = assignmentPartition β d κ n C := by
  classical
  let rows (p : Equiv.Perm (Fin n)) : Fin n → Option (Fin n) := fun i => some (p i)
  have hinj : Function.Injective rows := by
    intro p q hpq
    exact Equiv.ext fun i => Option.some.inj (congrFun hpq i)
  have heq : matchingsAtDeficit n 0 = univ.image rows := by
    ext m
    rw [mem_matchingsAtDeficit_zero_iff_permutation, Finset.mem_image]
    simp [rows]
  rw [deficitPartition, assignmentPartition_eq_sum_perfectWeight, heq, Finset.sum_image hinj.injOn]
  rfl

/-- The deterministic form of the weighted completion bound for the genuine
partial and perfect assignment partition functions. -/
theorem deficitPartition_le_of_rowSum_bound
    (β d κ : ℝ) (hβ : 0 ≤ β) (n k r : ℕ) (C : CostArray)
    (complete : (Fin n → Option (Fin n)) → Equiv.Perm (Fin n))
    (B K₁ : ℝ) (hr : 0 < r) (hrn : r ≤ n)
    (hrows : ∀ m ∈ matchingsAtDeficit n k, (changedRows (complete m) m).card ≤ r)
    (hlength : ∀ m ∈ matchingsAtDeficit n k, insertedLength (scaledCost d κ n C) (complete m) m ≤ B)
    (hrowSum : ∑ i, rowSum β (scaledCost d κ n C) i ≤ K₁ * n) :
    deficitPartition β d κ n k C ≤ assignmentPartition β d κ n C *
      Real.exp (β * B + (r : ℝ) * Real.log ((n : ℝ) / r) + (1 + K₁) * r) := by
  rw [deficitPartition, assignmentPartition_eq_sum_perfectWeight]
  simpa using partialPartition_le_of_rowSum_bound β hβ (scaledCost d κ n C)
    (matchingsAtDeficit n k) complete r B K₁ hr (by simpa using hrn) hrows hlength
    (by simpa using hrowSum)

private theorem logDeficit_ge_one {n k : ℝ} (hk : 0 < k) (hkn : k ≤ n) :
    1 ≤ Real.log (Real.exp 1 * n / k) := by
  have hn := hk.trans_le hkn
  rw [mul_div_assoc, Real.log_mul (Real.exp_pos _).ne' (div_pos hn hk).ne',
    Real.log_exp]
  have hlog := Real.log_nonneg ((le_div_iff₀ hk).2 (by simpa using hkn))
  linarith

/-- The weighted completion inequality of the manuscript, given the deterministic
row and inserted length budgets and a bound on the total of all row weights. -/
theorem weightedCompletion_bound
    (β d κ : ℝ) (hβ : 0 ≤ β) (n k r : ℕ) (C : CostArray)
    (complete : (Fin n → Option (Fin n)) → Equiv.Perm (Fin n))
    (K₀ K₁ : ℝ) (hK₀ : 0 ≤ K₀) (hK₁ : 0 ≤ K₁)
    (hk : 0 < k) (hkr : k ≤ r) (hrn : r ≤ n)
    (hr : (r : ℝ) ≤ K₀ * k * Real.log (Real.exp 1 * n / k))
    (hrows : ∀ m ∈ matchingsAtDeficit n k, (changedRows (complete m) m).card ≤ r)
    (hlength : ∀ m ∈ matchingsAtDeficit n k,
      insertedLength (scaledCost d κ n C) (complete m) m ≤
        K₀ * k * Real.log (Real.exp 1 * n / k) ^ (1 + 1 / d : ℝ))
    (hrowSum : ∑ i, rowSum β (scaledCost d κ n C) i ≤ K₁ * n) :
    deficitPartition β d κ n k C ≤ assignmentPartition β d κ n C *
      Real.exp ((β * K₀ + K₀ * (2 + K₁)) * k *
        Real.log (Real.exp 1 * n / k) ^ (max 2 (1 + 1 / d) : ℝ)) := by
  have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
  have hkr' : (k : ℝ) ≤ (r : ℝ) := by exact_mod_cast hkr
  have hrn' : (r : ℝ) ≤ (n : ℝ) := by exact_mod_cast hrn
  let L : ℝ := Real.log (Real.exp 1 * n / k)
  let b : ℝ := 1 + 1 / d
  let α : ℝ := max 2 b
  have hL : 1 ≤ L := logDeficit_ge_one hk' (hkr'.trans hrn')
  have hB : β * (K₀ * k * L ^ b) ≤ (β * K₀) * k * L ^ α := by
    have hpow := Real.rpow_le_rpow_of_exponent_le hL (le_max_right (2 : ℝ) b)
    calc
      _ = (β * K₀) * k * L ^ b := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (mul_nonneg (mul_nonneg hβ hK₀) hk'.le)
  have hE : (r : ℝ) * Real.log ((n : ℝ) / r) + (1 + K₁) * r ≤
      K₀ * (2 + K₁) * k * L ^ α := by
    apply (entropyPenalty_le_log_sq n k r K₀ K₁ hk' hkr' hrn' hK₁ hr).trans
    have hpow : L ^ (2 : ℕ) ≤ L ^ α := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hL (le_max_left (2 : ℝ) b)
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  apply (deficitPartition_le_of_rowSum_bound β d κ hβ n k r C complete
    (K₀ * k * L ^ b) K₁ (hk.trans_le hkr) hrn hrows hlength hrowSum).trans
  apply mul_le_mul_of_nonneg_left _ (assignmentPartition_pos β d κ n C).le
  apply Real.exp_le_exp.mpr
  change β * (K₀ * k * L ^ b) + (r : ℝ) * Real.log ((n : ℝ) / r) + (1 + K₁) * r ≤
    (β * K₀ + K₀ * (2 + K₁)) * k * L ^ α
  calc
    _ ≤ (β * K₀) * k * L ^ α + K₀ * (2 + K₁) * k * L ^ α := by linarith
    _ = _ := by ring

/-- The count assumption may be the real-valued budget of the augmentation lemma.
The proof chooses the integer cutoff by flooring and truncating at the number of rows. -/
theorem weightedCompletion_bound_of_real_budget
    (β d κ : ℝ) (hβ : 0 ≤ β) (n k : ℕ) (C : CostArray)
    (complete : (Fin n → Option (Fin n)) → Equiv.Perm (Fin n))
    (K₀ K₁ : ℝ) (hK₀ : 1 ≤ K₀) (hK₁ : 0 ≤ K₁)
    (hk : 0 < k) (hkn : k ≤ n)
    (hrows : ∀ m ∈ matchingsAtDeficit n k,
      ((changedRows (complete m) m).card : ℝ) ≤ K₀ * k * Real.log (Real.exp 1 * n / k))
    (hlength : ∀ m ∈ matchingsAtDeficit n k,
      insertedLength (scaledCost d κ n C) (complete m) m ≤
        K₀ * k * Real.log (Real.exp 1 * n / k) ^ (1 + 1 / d : ℝ))
    (hrowSum : ∑ i, rowSum β (scaledCost d κ n C) i ≤ K₁ * n) :
    deficitPartition β d κ n k C ≤ assignmentPartition β d κ n C *
      Real.exp ((β * K₀ + K₀ * (2 + K₁)) * k *
        Real.log (Real.exp 1 * n / k) ^ (max 2 (1 + 1 / d) : ℝ)) := by
  let L : ℝ := Real.log (Real.exp 1 * n / k)
  let budget := K₀ * k * L
  let r : ℕ := min n ⌊budget⌋₊
  have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
  have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hL : 1 ≤ L := logDeficit_ge_one hk' hkn'
  have hbudget : (k : ℝ) ≤ budget := by
    dsimp [budget]
    calc
      (k : ℝ) = 1 * (k : ℝ) * 1 := by ring
      _ ≤ _ := by gcongr
  have hr₁ : k ≤ r := le_min hkn (Nat.le_floor hbudget)
  have hr₂ : r ≤ n := min_le_left _ _
  have hr₃ : (r : ℝ) ≤ budget :=
    (Nat.cast_le.mpr (min_le_right _ _)).trans (Nat.floor_le (hk'.le.trans hbudget))
  have hrows' : ∀ m ∈ matchingsAtDeficit n k, (changedRows (complete m) m).card ≤ r := by
    intro m hm
    apply le_min
    · simpa using Finset.card_le_univ (changedRows (complete m) m)
    · exact Nat.le_floor (hrows m hm)
  exact weightedCompletion_bound β d κ hβ n k r C complete K₀ K₁
    (zero_le_one.trans hK₀) hK₁ hk hr₁ hr₂ hr₃ hrows' hlength hrowSum

/-- The pressure with monomers, formed from the actual partial assignment coefficients. -/
noncomputable def monomerPressure (β d κ : ℝ) (n : ℕ) (C : CostArray) (z : ℝ) : ℝ :=
  Real.log (monomerPartition n (fun k => deficitPartition β d κ n k C) z) / n

/-- A uniform choice of the monomer fugacity bounds the pressure gap on every
array and size for which the weighted coefficient bounds hold. -/
theorem concrete_monomer_pressure_gap (β d κ : ℝ) {K α ε : ℝ}
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hε : 0 < ε) :
    ∃ z₀ : ℝ, 0 < z₀ ∧ z₀ ≤ 1 ∧ ∀ (n : ℕ) (C : CostArray),
      0 < n →
      (∀ k : ℕ, 0 < k → k ≤ n →
        deficitPartition β d κ n k C ≤ assignmentPartition β d κ n C *
          Real.exp (K * k * Real.log (Real.exp 1 * n / k) ^ α)) →
      ∀ z : ℝ, 0 < z → z ≤ z₀ →
        0 ≤ monomerPressure β d κ n C z - pressure β d κ n C ∧
        monomerPressure β d κ n C z - pressure β d κ n C ≤
          Real.log ((n : ℝ) + 1) / n + ε := by
  obtain ⟨z₀, hz₀, hz₀₁, hgap⟩ := monomer_pressure_gap_of_completion hK hα hε
  refine ⟨z₀, hz₀, hz₀₁, ?_⟩
  intro n C hn hcoefficient z hz hzz
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hZ₀ : 0 < deficitPartition β d κ n 0 C := by
    rw [deficitPartition_zero]
    exact assignmentPartition_pos β d κ n C
  have hcoeff (k : ℕ) (hk : 0 < k) (hkn : k ≤ n) :
      deficitPartition β d κ n k C ≤ deficitPartition β d κ n 0 C *
        Real.exp ((n : ℝ) * deficitProfile K α ((k : ℝ) / n)) := by
    have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
    have hratio : Real.exp 1 / ((k : ℝ) / n) = Real.exp 1 * n / k := by field_simp
    have he : (n : ℝ) * deficitProfile K α ((k : ℝ) / n) =
        K * k * Real.log (Real.exp 1 * n / k) ^ α := by
      rw [deficitProfile, hratio]
      field_simp
    rw [deficitPartition_zero, he]
    exact hcoefficient k hk hkn
  simpa only [monomerPressure, pressure, deficitPartition_zero] using
    (hgap hz hzz hn hZ₀ (fun k => deficitPartition_nonneg β d κ n k C) hcoeff)

end Certificate.Completion

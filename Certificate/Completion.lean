import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.Tactic

/-!
# Weighted counting for a deterministic completion map

This proves the counting step in "Weighted completion" of the manuscript.
The input is a map to perfect assignments with bounds on the number and total length of
the inserted edges. No independence or column constraints are needed for the counting step.
-/

open scoped BigOperators
open Finset

namespace Certificate.Completion

variable {ι : Type*}

/-- The Boltzmann contribution of a single row, with contribution one for an unmatched row. -/
noncomputable def rowWeight (β : ℝ) (x : ι → ι → ℝ) (i : ι) : Option ι → ℝ
  | none => 1
  | some j => Real.exp (-β * x i j)

@[simp] theorem rowWeight_none (β : ℝ) (x : ι → ι → ℝ) (i : ι) :
    rowWeight β x i none = 1 := rfl

@[simp] theorem rowWeight_some (β : ℝ) (x : ι → ι → ℝ) (i j : ι) :
    rowWeight β x i (some j) = Real.exp (-β * x i j) := rfl

theorem rowWeight_pos (β : ℝ) (x : ι → ι → ℝ) (i : ι) (a : Option ι) :
    0 < rowWeight β x i a := by
  cases a <;> simp [Real.exp_pos]

variable [Fintype ι]

/-- The weight of a partial assignment specified by the column used in each row. -/
noncomputable def partialWeight (β : ℝ) (x : ι → ι → ℝ) (m : ι → Option ι) : ℝ :=
  ∏ i, rowWeight β x i (m i)

/-- The weight of a perfect assignment. -/
noncomputable def perfectWeight (β : ℝ) (x : ι → ι → ℝ) (p : Equiv.Perm ι) : ℝ :=
  partialWeight β x (fun i => some (p i))

/-- The rows where the completed assignment inserts an edge that was absent. -/
noncomputable def changedRows (p : Equiv.Perm ι) (m : ι → Option ι) : Finset ι :=
  haveI := Classical.decEq ι
  univ.filter fun i => m i ≠ some (p i)

/-- The total length of the inserted edges. -/
noncomputable def insertedLength (x : ι → ι → ℝ) (p : Equiv.Perm ι) (m : ι → Option ι) : ℝ :=
  ∑ i ∈ changedRows p m, x i (p i)

/-- The sum of the weights of all possible columns in a row. -/
noncomputable def rowSum (β : ℝ) (x : ι → ι → ℝ) (i : ι) : ℝ :=
  ∑ j, Real.exp (-β * x i j)

theorem partialWeight_pos (β : ℝ) (x : ι → ι → ℝ) (m : ι → Option ι) :
    0 < partialWeight β x m :=
  Finset.prod_pos fun i _ => rowWeight_pos β x i (m i)

theorem perfectWeight_pos (β : ℝ) (x : ι → ι → ℝ) (p : Equiv.Perm ι) :
    0 < perfectWeight β x p :=
  partialWeight_pos β x _

@[simp] theorem mem_changedRows (p : Equiv.Perm ι) (m : ι → Option ι) (i : ι) :
    i ∈ changedRows p m ↔ m i ≠ some (p i) := by
  classical
  simp [changedRows]

theorem perfectWeight_exp (β : ℝ) (x : ι → ι → ℝ) (p : Equiv.Perm ι) :
    perfectWeight β x p = Real.exp (-β * ∑ i, x i (p i)) := by
  rw [Finset.mul_sum, Real.exp_sum]
  rfl

/-- Unchanged rows cancel in the weight ratio. Written without division. -/
theorem partialWeight_eq_completion_mul (β : ℝ) (x : ι → ι → ℝ)
    (p : Equiv.Perm ι) (m : ι → Option ι) :
    partialWeight β x m =
      perfectWeight β x p * Real.exp (β * insertedLength x p m) *
        ∏ i ∈ changedRows p m, rowWeight β x i (m i) := by
  classical
  let s := changedRows p m
  let w := fun i => rowWeight β x i (m i)
  let v := fun i => Real.exp (-β * x i (p i))
  have hsame : ∏ i ∈ univ \ s, w i = ∏ i ∈ univ \ s, v i := by
    refine Finset.prod_congr rfl fun i hi => ?_
    have heq : m i = some (p i) :=
      not_not.mp (fun h => (Finset.mem_sdiff.mp hi).2 ((mem_changedRows p m i).2 h))
    simp [w, v, heq]
  have hcancel : (∏ i ∈ s, v i) * Real.exp (β * insertedLength x p m) = 1 := by
    have hexp : Real.exp (β * insertedLength x p m) =
        ∏ i ∈ s, Real.exp (β * x i (p i)) := by
      simp only [insertedLength, Finset.mul_sum, Real.exp_sum, s]
    rw [hexp, ← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro i _
    rw [show v i = Real.exp (-β * x i (p i)) by rfl, ← Real.exp_add]
    rw [show -β * x i (p i) + β * x i (p i) = 0 by ring, Real.exp_zero]
  change (∏ i, w i) = ((∏ i, v i) * Real.exp (β * insertedLength x p m)) * ∏ i ∈ s, w i
  rw [← Finset.prod_sdiff (Finset.subset_univ s) (f := w),
      ← Finset.prod_sdiff (Finset.subset_univ s) (f := v), hsame,
      mul_assoc (∏ i ∈ univ \ s, v i), hcancel, mul_one]

/-- For fixed changed rows, assignments inject into all independent choices in those rows.
Allowing every column and an unmatched row gives the product of $1+S_i$. -/
theorem changedWeight_sum_le (β : ℝ) (x : ι → ι → ℝ) (p : Equiv.Perm ι)
    (s : Finset ι) (A : Finset (ι → Option ι))
    (hA : ∀ m ∈ A, changedRows p m = s) :
    (∑ m ∈ A, ∏ i ∈ s, rowWeight β x i (m i)) ≤ ∏ i ∈ s, (1 + rowSum β x i) := by
  classical
  let restrict : (ι → Option ι) → (s → Option ι) := fun m i => m i
  have hinj : Set.InjOn restrict A := by
    intro m hm n hn hmn
    funext i
    by_cases hi : i ∈ s
    · exact congrFun hmn ⟨i, hi⟩
    · have heq (a : ι → Option ι) (ha : a ∈ A) : a i = some (p i) :=
        not_not.mp (fun h => hi (hA a ha ▸ (mem_changedRows p a i).2 h))
      rw [heq m hm, heq n hn]
  let f : (s → Option ι) → ℝ := fun a => ∏ i : s, rowWeight β x i (a i)
  calc
    (∑ m ∈ A, ∏ i ∈ s, rowWeight β x i (m i)) = ∑ m ∈ A, f (restrict m) := by
      apply Finset.sum_congr rfl
      intro m _
      rw [← Finset.prod_attach]
      rfl
    _ = ∑ a ∈ A.image restrict, f a := (Finset.sum_image hinj).symm
    _ ≤ ∑ a, f a := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun a _ _ => Finset.prod_nonneg fun i _ =>
        (rowWeight_pos β x i (a i)).le)
    _ = ∏ i ∈ s, (1 + rowSum β x i) := by
      calc
        (∑ a, f a) = ∏ i : s, ∑ c : Option ι, rowWeight β x i c :=
          (Fintype.prod_sum (fun (i : s) (c : Option ι) => rowWeight β x i c)).symm
        _ = ∏ i : s, (1 + rowSum β x i) := by
          apply Finset.prod_congr rfl
          intro i _
          simp [rowSum, Fintype.sum_option]
        _ = _ := Finset.prod_coe_sort s (fun i => 1 + rowSum β x i)

/-- The generating-function bound for choosing at most $r$ changed rows. -/
theorem boundedPowerset_prod_le (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (r : ℕ) {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    (∑ s ∈ (univ : Finset ι).powerset.filter (fun s => s.card ≤ r), ∏ i ∈ s, a i)
      ≤ Real.exp (-(r : ℝ) * Real.log θ + θ * ∑ i, a i) := by
  classical
  let A := (univ : Finset ι).powerset.filter (fun s => s.card ≤ r)
  have hpow : 0 < θ ^ r := pow_pos hθ _
  have hscale : Real.exp (θ * ∑ i, a i) / θ ^ r =
      Real.exp (-(r : ℝ) * Real.log θ + θ * ∑ i, a i) := by
    rw [Real.exp_add, neg_mul, Real.exp_neg, mul_comm ((Real.exp _ )⁻¹),
      div_eq_mul_inv, Real.exp_nat_mul, Real.exp_log hθ]
  rw [← hscale]
  apply (le_div_iff₀ hpow).2
  change (∑ s ∈ A, ∏ i ∈ s, a i) * θ ^ r ≤ _
  calc
    (∑ s ∈ A, ∏ i ∈ s, a i) * θ ^ r
      = ∑ s ∈ A, θ ^ r * ∏ i ∈ s, a i := by rw [mul_comm, Finset.mul_sum]
    _ ≤ ∑ s ∈ A, ∏ i ∈ s, (θ * a i) := by
      refine Finset.sum_le_sum fun s hs => ?_
      rw [Finset.prod_mul_distrib, Finset.prod_const]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_of_le_one hθ.le hθ1 (Finset.mem_filter.mp hs).2)
        (Finset.prod_nonneg fun i _ => ha i)
    _ ≤ ∑ s ∈ (univ : Finset ι).powerset, ∏ i ∈ s, (θ * a i) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun s _ _ => Finset.prod_nonneg fun i _ => mul_nonneg hθ.le (ha i))
    _ = ∏ i, (1 + θ * a i) := (Finset.prod_one_add _).symm
    _ ≤ Real.exp (θ * ∑ i, a i) := by
      rw [Finset.mul_sum]
      exact Real.prod_one_add_le_exp_sum _ (fun i => mul_nonneg hθ.le (ha i))

variable [DecidableEq ι]

/-- A deterministic completion estimate. The input certifies that every chosen completion
changes at most `r` rows and inserts edges of total length at most `B`. The conclusion
controls their total weight by the full perfect-assignment partition function. -/
theorem partialPartition_le_of_completion
    (β : ℝ) (hβ : 0 ≤ β) (x : ι → ι → ℝ)
    (A : Finset (ι → Option ι)) (complete : (ι → Option ι) → Equiv.Perm ι)
    (r : ℕ) (B : ℝ)
    (hrows : ∀ m ∈ A, (changedRows (complete m) m).card ≤ r)
    (hlength : ∀ m ∈ A, insertedLength x (complete m) m ≤ B)
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    (∑ m ∈ A, partialWeight β x m) ≤
      (∑ p : Equiv.Perm ι, perfectWeight β x p) *
        Real.exp (β * B - (r : ℝ) * Real.log θ + θ * ∑ i, (1 + rowSum β x i)) := by
  classical
  let goodRows := (univ : Finset ι).powerset.filter fun s => s.card ≤ r
  have hfiber (p : Equiv.Perm ι) :
      (∑ m ∈ A.filter (fun m => complete m = p), partialWeight β x m) ≤
        perfectWeight β x p *
          Real.exp (β * B - (r : ℝ) * Real.log θ + θ * ∑ i, (1 + rowSum β x i)) := by
    let fiber := A.filter fun m => complete m = p
    have hmaps : ∀ m ∈ fiber, changedRows p m ∈ goodRows := by
      intro m hm
      obtain ⟨hmA, hp⟩ := Finset.mem_filter.mp hm
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), hp ▸ hrows m hmA⟩
    have hfixed (s : Finset ι) :
        (∑ m ∈ fiber.filter (fun m => changedRows p m = s), partialWeight β x m) ≤
          (perfectWeight β x p * Real.exp (β * B)) * ∏ i ∈ s, (1 + rowSum β x i) := by
      let G := fiber.filter fun m => changedRows p m = s
      have hcancel (m : ι → Option ι) (hm : m ∈ G) :
          partialWeight β x m ≤
            (perfectWeight β x p * Real.exp (β * B)) * ∏ i ∈ s, rowWeight β x i (m i) := by
        obtain ⟨hf, hs⟩ := Finset.mem_filter.mp hm
        obtain ⟨hA, hp⟩ := Finset.mem_filter.mp hf
        have hB : insertedLength x p m ≤ B := hp ▸ hlength m hA
        rw [partialWeight_eq_completion_mul β x p m, hs]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hB hβ))
            (perfectWeight_pos β x p).le)
          (Finset.prod_nonneg fun i _ => (rowWeight_pos β x i (m i)).le)
      exact calc
        (∑ m ∈ G, partialWeight β x m) ≤
            ∑ m ∈ G, (perfectWeight β x p * Real.exp (β * B)) *
              ∏ i ∈ s, rowWeight β x i (m i) :=
          Finset.sum_le_sum hcancel
        _ = (perfectWeight β x p * Real.exp (β * B)) *
              ∑ m ∈ G, ∏ i ∈ s, rowWeight β x i (m i) := (Finset.mul_sum ..).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (changedWeight_sum_le β x p s G (fun m hm => (Finset.mem_filter.mp hm).2))
          (mul_nonneg (perfectWeight_pos β x p).le (Real.exp_pos _).le)
    have ha (i : ι) : 0 ≤ 1 + rowSum β x i := by unfold rowSum; positivity
    calc
      (∑ m ∈ fiber, partialWeight β x m) =
          ∑ s ∈ goodRows, ∑ m ∈ fiber.filter (fun m => changedRows p m = s),
              partialWeight β x m := (Finset.sum_fiberwise_of_maps_to hmaps _).symm
      _ ≤ (perfectWeight β x p * Real.exp (β * B)) *
          ∑ s ∈ goodRows, ∏ i ∈ s, (1 + rowSum β x i) := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun s _ => hfixed s
      _ ≤ (perfectWeight β x p * Real.exp (β * B)) *
          Real.exp (-(r : ℝ) * Real.log θ + θ * ∑ i, (1 + rowSum β x i)) :=
        mul_le_mul_of_nonneg_left (boundedPowerset_prod_le _ ha r hθ hθ1)
          (mul_nonneg (perfectWeight_pos β x p).le (Real.exp_pos _).le)
      _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  calc
    (∑ m ∈ A, partialWeight β x m) =
        ∑ p : Equiv.Perm ι, ∑ m ∈ A.filter (fun m => complete m = p), partialWeight β x m :=
      (Finset.sum_fiberwise_of_maps_to (t := univ) (fun _ _ => Finset.mem_univ _) _).symm
    _ ≤ _ := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun p _ => hfiber p

/-- Specializing the generating-function parameter to the fraction of changed rows
gives the entropy term in the manuscript. -/
theorem partialPartition_le_of_rowSum_bound
    (β : ℝ) (hβ : 0 ≤ β) (x : ι → ι → ℝ)
    (A : Finset (ι → Option ι)) (complete : (ι → Option ι) → Equiv.Perm ι)
    (r : ℕ) (B K₁ : ℝ) (hr : 0 < r) (hrn : r ≤ Fintype.card ι)
    (hrows : ∀ m ∈ A, (changedRows (complete m) m).card ≤ r)
    (hlength : ∀ m ∈ A, insertedLength x (complete m) m ≤ B)
    (hrowSum : ∑ i, rowSum β x i ≤ K₁ * (Fintype.card ι : ℝ)) :
    (∑ m ∈ A, partialWeight β x m) ≤
      (∑ p : Equiv.Perm ι, perfectWeight β x p) *
        Real.exp (β * B + (r : ℝ) * Real.log ((Fintype.card ι : ℝ) / r) + (1 + K₁) * r) := by
  let n : ℝ := Fintype.card ι
  have hr' : 0 < (r : ℝ) := by exact_mod_cast hr
  have hrn' : (r : ℝ) ≤ n := by
    dsimp [n]
    exact_mod_cast hrn
  have hn : 0 < n := hr'.trans_le hrn'
  let θ : ℝ := r / n
  have hθ : 0 < θ := div_pos hr' hn
  have hθ1 : θ ≤ 1 := (div_le_one hn).2 hrn'
  have hsum : (∑ i, (1 + rowSum β x i)) ≤ (1 + K₁) * n := by
    have hk : (∑ i, rowSum β x i) ≤ K₁ * n := hrowSum
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    change n + (∑ i, rowSum β x i) ≤ (1 + K₁) * n
    linarith
  have he : θ * (∑ i, (1 + rowSum β x i)) ≤ (1 + K₁) * r :=
    calc
      _ ≤ θ * ((1 + K₁) * n) := mul_le_mul_of_nonneg_left hsum hθ.le
      _ = _ := by dsimp [θ]; field_simp
  have hlog : -(r : ℝ) * Real.log θ = (r : ℝ) * Real.log (n / r) := by
    dsimp [θ]
    rw [Real.log_div hr'.ne' hn.ne', Real.log_div hn.ne' hr'.ne']
    ring
  apply (partialPartition_le_of_completion β hβ x A complete r B hrows hlength hθ hθ1).trans
  apply mul_le_mul_of_nonneg_left
  · apply Real.exp_le_exp.mpr
    linarith
  · exact Finset.sum_nonneg fun p _ => (perfectWeight_pos β x p).le

/-- The row selection term grows at most like `k * log(e * n / k)^2`
when the number of changed rows is controlled by `k * log(e * n / k)`. -/
theorem entropyPenalty_le_log_sq (n k r K₀ K₁ : ℝ)
    (hk : 0 < k) (hkr : k ≤ r) (hrn : r ≤ n) (hK₁ : 0 ≤ K₁)
    (hrows : r ≤ K₀ * k * Real.log (Real.exp 1 * n / k)) :
    r * Real.log (n / r) + (1 + K₁) * r ≤
      K₀ * (2 + K₁) * k * Real.log (Real.exp 1 * n / k) ^ 2 := by
  have hr : 0 < r := hk.trans_le hkr
  have hn : 0 < n := hr.trans_le hrn
  let L := Real.log (Real.exp 1 * n / k)
  have hL_eq : L = 1 + Real.log (n / k) := by
    dsimp [L]
    rw [mul_div_assoc, Real.log_mul (Real.exp_pos _).ne' (div_pos hn hk).ne',
      Real.log_exp]
  have hL : 1 ≤ L := by
    rw [hL_eq]
    have h : 0 ≤ Real.log (n / k) := Real.log_nonneg ((le_div_iff₀ hk).2 (by linarith))
    linarith
  have hlog : Real.log (n / r) ≤ Real.log (n / k) :=
    Real.log_le_log (div_pos hn hr) (div_le_div_of_nonneg_left hn.le hk hkr)
  have hfactor : Real.log (n / r) + (1 + K₁) ≤ (2 + K₁) * L := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 + K₁) (sub_nonneg.mpr hL)]
  calc
    r * Real.log (n / r) + (1 + K₁) * r = r * (Real.log (n / r) + (1 + K₁)) := by ring
    _ ≤ r * ((2 + K₁) * L) := mul_le_mul_of_nonneg_left hfactor hr.le
    _ ≤ (K₀ * k * L) * ((2 + K₁) * L) := by
      apply mul_le_mul_of_nonneg_right hrows
      exact mul_nonneg (by linarith) (by linarith)
    _ = _ := by dsimp [L]; ring

end Certificate.Completion

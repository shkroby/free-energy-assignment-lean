import Certificate.CompletionExpansionGrowth
import Certificate.CompletionExpansionScale
import Mathlib.Data.Nat.Log

/-!
# Iterating cheap augmentations

Each augmentation contributes a count and a length budget. An edge of the
final assignment that was absent originally must occur in one of the individual
insertions. This permits summing both budgets over the deficits.
-/

open Finset
open scoped BigOperators

namespace Certificate.Completion

/-- A doubling-round budget sufficient to reach the cut size. -/
def augmentationRounds (n j : ℕ) : ℕ :=
  Nat.log 2 (n / j) + 1

theorem le_pow_augmentationRounds {n j : ℕ} (hj : 0 < j) :
    n ≤ 2 ^ augmentationRounds n j * j := by
  have hmod := Nat.mod_lt n hj
  have hdec := Nat.mod_add_div n j
  have hpow : n / j + 1 ≤ 2 ^ augmentationRounds n j :=
    Nat.lt_pow_succ_log_self (by decide) (n / j)
  calc
    n = n % j + j * (n / j) := hdec.symm
    _ ≤ (n / j + 1) * j := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (n / j) j]
      omega
    _ ≤ _ := Nat.mul_le_mul_right j hpow

theorem augmentationRounds_le_expansionLog {n j : ℕ} (hj : 0 < j) (hjn : j ≤ n) :
    ((2 * augmentationRounds n j + 1 : ℕ) : ℝ) ≤ 4 * expansionLog n j := by
  have hj' : 0 < (j : ℝ) := by exact_mod_cast hj
  have hdiv : 0 < n / j := Nat.div_pos hjn hj
  have hpowN : 2 ^ Nat.log 2 (n / j) ≤ n / j := Nat.pow_log_le_self 2 hdiv.ne'
  have hpowR : (2 : ℝ) ^ Nat.log 2 (n / j) ≤ (n : ℝ) / j := by
    calc
      _ ≤ ((n / j : ℕ) : ℝ) := by exact_mod_cast hpowN
      _ ≤ _ := (le_div_iff₀ hj').2 (by exact_mod_cast Nat.div_mul_le_self n j)
  have hlog := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) _) hpowR
  rw [Real.log_pow] at hlog
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.log_le_sub_one_of_pos (inv_pos.mpr (by norm_num : (0 : ℝ) < 2))
    rw [Real.log_inv] at h
    norm_num at h
    linarith
  have hnonneg : 0 ≤ (Nat.log 2 (n / j) : ℝ) := by positivity
  have hb := mul_nonneg hnonneg (sub_nonneg.mpr hlog2)
  unfold augmentationRounds expansionLog
  push_cast
  nlinarith only [hlog, hb]

/-- The edges of an optional row assignment. -/
noncomputable def chosenEdges {n : ℕ} (m : Fin n → Option (Fin n)) : Finset (Fin n × Fin n) :=
  univ.filter fun p => m p.1 = some p.2

/-- The edges inserted in changing from one assignment to another. -/
noncomputable def insertedEdges {n : ℕ} (m m' : Fin n → Option (Fin n)) : Finset (Fin n × Fin n) :=
  chosenEdges m' \ chosenEdges m

@[simp] theorem mem_insertedEdges {n : ℕ} {m m' : Fin n → Option (Fin n)}
    (p : Fin n × Fin n) :
    p ∈ insertedEdges m m' ↔ m' p.1 = some p.2 ∧ m p.1 ≠ some p.2 := by
  simp [insertedEdges, chosenEdges]

private theorem insertedEdges_subset_union {n : ℕ} (m m' m'' : Fin n → Option (Fin n)) :
    insertedEdges m m'' ⊆ insertedEdges m m' ∪ insertedEdges m' m'' := by
  intro p hp
  rcases (mem_insertedEdges p).mp hp with ⟨hf, ho⟩
  by_cases h : m' p.1 = some p.2
  · exact Finset.mem_union_left _ ((mem_insertedEdges p).mpr ⟨h, ho⟩)
  · exact Finset.mem_union_right _ ((mem_insertedEdges p).mpr ⟨hf, h⟩)

private theorem card_insertedEdges_triangle {n : ℕ} (m m' m'' : Fin n → Option (Fin n)) :
    (insertedEdges m m'').card ≤ (insertedEdges m m').card + (insertedEdges m' m'').card :=
  (Finset.card_le_card (insertedEdges_subset_union m m' m'')).trans (Finset.card_union_le _ _)

private theorem sum_insertedEdges_triangle {n : ℕ} (m m' m'' : Fin n → Option (Fin n))
    (x : Fin n × Fin n → ℝ) (hx : ∀ p, 0 ≤ x p) :
    ∑ p ∈ insertedEdges m m'', x p ≤
      (∑ p ∈ insertedEdges m m', x p) + ∑ p ∈ insertedEdges m' m'', x p := by
  let S := insertedEdges m m'
  let T := insertedEdges m' m''
  calc
    _ ≤ ∑ p ∈ S ∪ T, x p :=
      Finset.sum_le_sum_of_subset_of_nonneg (insertedEdges_subset_union m m' m'')
        (fun p _ _ => hx p)
    _ = (∑ p ∈ S \ T, x p) + ∑ p ∈ T, x p := by
      have hd : Disjoint (S \ T) T := Finset.disjoint_left.mpr
        (fun p hp hT => (Finset.mem_sdiff.mp hp).2 hT)
      rw [← Finset.sdiff_union_self_eq_union, Finset.sum_union hd]
    _ ≤ _ := add_le_add
      (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun p _ _ => hx p)) le_rfl

private theorem insertedEdges_flip_card {n k : ℕ} {m : Fin n → Option (Fin n)}
    (p : AugmentingPath m k) : (insertedEdges m p.flip).card ≤ k + 1 := by
  let e : Fin (k + 1) ↪ (Fin n × Fin n) :=
    ⟨fun i => (p.rows i, p.cols i), fun _ _ h => p.rows.injective (congrArg Prod.fst h)⟩
  have hsub : insertedEdges m p.flip ⊆ univ.map e := by
    intro z hz
    rcases (mem_insertedEdges z).mp hz with ⟨hflip, hold⟩
    by_cases hr : ∃ i, p.rows i = z.1
    · obtain ⟨i, hi⟩ := hr
      have hj : p.cols i = z.2 := by
        rw [← hi, p.flip_on_path] at hflip
        exact Option.some.inj hflip
      exact Finset.mem_map.mpr ⟨i, Finset.mem_univ _, Prod.ext hi hj⟩
    · rw [p.flip_off_path hr] at hflip
      exact (hold hflip).elim
  simpa using Finset.card_le_card hsub

private theorem insertedEdges_flip_cheap {n k : ℕ} {m : Fin n → Option (Fin n)}
    (p : AugmentingPath m k) {C : CostArray} {t : ℝ} (hc : p.IsCheap C t)
    {z : Fin n × Fin n} (hz : z ∈ insertedEdges m p.flip) : C (z.1.val, z.2.val) ≤ t := by
  rcases (mem_insertedEdges z).mp hz with ⟨hflip, hold⟩
  by_cases hr : ∃ i, p.rows i = z.1
  · obtain ⟨i, hi⟩ := hr
    have hj : p.cols i = z.2 := by
      rw [← hi, p.flip_on_path] at hflip
      exact Option.some.inj hflip
    simpa only [hi, hj] using hc i
  · rw [p.flip_off_path hr] at hflip
    exact (hold hflip).elim

private theorem insertedEdges_eq_changedRows_map {n : ℕ} (m : Fin n → Option (Fin n))
    (p : Equiv.Perm (Fin n)) :
    insertedEdges m (fun i => some (p i)) =
      (changedRows p m).map ⟨fun i => (i, p i), fun _ _ h => congrArg Prod.fst h⟩ := by
  ext z
  rcases z with ⟨i, j⟩
  constructor
  · intro h
    obtain ⟨hp, hn⟩ := (mem_insertedEdges (i, j)).mp h
    have hj : p i = j := Option.some.inj hp
    exact Finset.mem_map.mpr ⟨i, (mem_changedRows p m i).mpr (by rwa [hj]), Prod.ext rfl hj⟩
  · intro h
    obtain ⟨a, ha, e⟩ := Finset.mem_map.mp h
    have hai : a = i := congrArg Prod.fst e
    have haj : p a = j := congrArg Prod.snd e
    subst a
    exact (mem_insertedEdges (i, j)).mpr ⟨congrArg some haj,
      (by rw [← haj]; exact (mem_changedRows p m i).mp ha)⟩

private theorem exists_augmentation_bounded {n : ℕ} {m : Fin n → Option (Fin n)}
    {A d κ : ℝ} {C : CostArray}
    (hA : 0 < A) (hκ : 0 < κ)
    (hC : C ∉ commonExpansionFailure n (expansionCutoff A d κ n))
    (hm : IsMatching m) {j : ℕ} (hj : 0 < j) (hjn : j ≤ n)
    (hdeficit : n - (AugmentingPath.matchedRows m).card = j) :
    ∃ m' : Fin n → Option (Fin n), IsMatching m' ∧
      n - (AugmentingPath.matchedRows m').card = j - 1 ∧
      ((insertedEdges m m').card : ℝ) ≤ 4 * expansionLog n j ∧
      (∑ p ∈ insertedEdges m m', scaledCost d κ n C p.1 p.2) ≤
        4 * A * expansionLog n j ^ (1 + 1 / d : ℝ) := by
  have hbud : n / 40 ≤ 2 ^ augmentationRounds n j * j :=
    (Nat.div_le_self _ _).trans (le_pow_augmentationRounds hj)
  obtain ⟨k, hk, p, hcheap⟩ := exists_cheap_augmentingPath_of_not_mem_commonFailure
    hC hm hj hjn hdeficit hbud
  have hcntN := (insertedEdges_flip_card p).trans hk
  have hcnt : ((insertedEdges m p.flip).card : ℝ) ≤ 4 * expansionLog n j :=
    (Nat.cast_le.mpr hcntN).trans (augmentationRounds_le_expansionLog hj hjn)
  refine ⟨p.flip, p.isMatching_flip hm, by rw [p.matchedRows_card_flip]; omega, hcnt, ?_⟩
  let L := expansionLog n j
  have hL : 0 < L := zero_lt_one.trans_le (expansionLog_ge_one hj hjn)
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hj.trans_le hjn
  have hscale : 0 < lengthScale d κ n := Real.rpow_pos_of_pos (mul_pos hκ hn') _
  have he (z : Fin n × Fin n) (hz : z ∈ insertedEdges m p.flip) :
      scaledCost d κ n C z.1 z.2 ≤ A * L ^ (1 / d : ℝ) := by
    calc
      _ ≤ lengthScale d κ n * expansionCutoff A d κ n j :=
        mul_le_mul_of_nonneg_left (insertedEdges_flip_cheap p hcheap hz) hscale.le
      _ = _ := by
        rw [expansionCutoff_eq_scaled A hκ hj hjn, mul_div_assoc']
        change (lengthScale d κ n * (A * L ^ (1 / d : ℝ))) / lengthScale d κ n =
          A * L ^ (1 / d : ℝ)
        field_simp
  calc
    _ ≤ ∑ _z ∈ insertedEdges m p.flip, A * L ^ (1 / d : ℝ) := Finset.sum_le_sum he
    _ = ((insertedEdges m p.flip).card : ℝ) * (A * L ^ (1 / d : ℝ)) := by simp [nsmul_eq_mul]
    _ ≤ (4 * L) * (A * L ^ (1 / d : ℝ)) :=
      mul_le_mul_of_nonneg_right hcnt (mul_nonneg hA.le (Real.rpow_nonneg hL.le _))
    _ = _ := by
      rw [show (4 * L) * (A * L ^ (1 / d : ℝ)) = 4 * A * (L * L ^ (1 / d : ℝ)) by ring,
        Real.rpow_add hL, Real.rpow_one]

/-- Iterating the short augmentations gives a perfect matching, with separate
bounds on the count and scaled length of all inserted edges. -/
theorem exists_completion_summed_bounds {n k : ℕ} {C : CostArray} {m : Fin n → Option (Fin n)}
    {A d κ : ℝ} (hA : 0 < A) (hκ : 0 < κ)
    (hC : C ∉ commonExpansionFailure n (expansionCutoff A d κ n))
    (hcost : ∀ p, 0 ≤ C p) (hm : m ∈ matchingsAtDeficit n k) :
    ∃ p : Equiv.Perm (Fin n),
      ((changedRows p m).card : ℝ) ≤ ∑ j ∈ range k, 4 * expansionLog n (j + 1) ∧
      insertedLength (scaledCost d κ n C) p m ≤
        ∑ j ∈ range k, 4 * A * expansionLog n (j + 1) ^ (1 + 1 / d : ℝ) := by
  induction k generalizing m with
  | zero =>
    obtain ⟨p, hp⟩ := (mem_matchingsAtDeficit_zero_iff_permutation m).mp hm
    subst m
    have he : changedRows p (fun i => some (p i)) = ∅ := by ext i; simp
    exact ⟨p, by simp [he], by simp [insertedLength, he]⟩
  | succ k ih =>
    obtain ⟨hM, hMcard⟩ := mem_matchingsAtDeficit.mp hm
    have hdef : n - (AugmentingPath.matchedRows m).card = k + 1 := by omega
    obtain ⟨m', hm', hdef', hcount', hlen'⟩ := exists_augmentation_bounded hA hκ
      hC hM (by omega) (by omega : k + 1 ≤ n) hdef
    have hm'en : m' ∈ matchingsAtDeficit n k := by
      apply mem_matchingsAtDeficit.mpr
      refine ⟨hm', ?_⟩
      have hu := Finset.card_le_univ (AugmentingPath.matchedRows m')
      simp only [Fintype.card_fin] at hu
      omega
    obtain ⟨p, hcnt, hp⟩ := ih hm'en
    let f : Fin n → Option (Fin n) := fun i => some (p i)
    let x (z : Fin n × Fin n) := scaledCost d κ n C z.1 z.2
    have hx (z : Fin n × Fin n) : 0 ≤ x z := by
      exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (hcost _)
    have haux (v : Fin n → Option (Fin n)) :
        (insertedEdges v f).card = (changedRows p v).card := by
      rw [insertedEdges_eq_changedRows_map, Finset.card_map]
    have haux' (v : Fin n → Option (Fin n)) :
        ∑ z ∈ insertedEdges v f, x z = insertedLength (scaledCost d κ n C) p v := by
      rw [insertedEdges_eq_changedRows_map, Finset.sum_map]
      rfl
    have hc := card_insertedEdges_triangle m m' f
    have hl := sum_insertedEdges_triangle m m' f x hx
    rw [haux m, haux m'] at hc
    rw [haux' m, haux' m'] at hl
    refine ⟨p, ?_, ?_⟩
    · rw [Finset.sum_range_succ]
      have hc' : ((changedRows p m).card : ℝ) ≤
          ((insertedEdges m m').card : ℝ) + ((changedRows p m').card : ℝ) := by exact_mod_cast hc
      linarith
    · rw [Finset.sum_range_succ]
      change (∑ z ∈ insertedEdges m m', x z) ≤ _ at hlen'
      linarith

end Certificate.Completion

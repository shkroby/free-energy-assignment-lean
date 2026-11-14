import Certificate.CompletionModel
import Certificate.ShortEdges
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.FieldSimp

/-!
# Cheap-edge expansion of the random cost array

The two bad events are a small set with too few neighbors and a large cut with
no cheap edge. A cutoff in this file is in the original cost units.
-/

open Finset Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal Topology MeasureTheory

namespace Certificate.Completion

/-- Interpret the first coordinate of a rectangle as a row (`true`) or column
(`false`). This lets the identical expansion argument apply to both classes. -/
def orientedEntry {n : ℕ} (byRow : Bool) (p : Fin n × Fin n) : ℕ × ℕ :=
  if byRow then (p.1.val, p.2.val) else (p.2.val, p.1.val)

theorem orientedEntry_injective {n : ℕ} (byRow : Bool) :
    Function.Injective (orientedEntry byRow : Fin n × Fin n → ℕ × ℕ) := by
  intro a b h
  cases byRow
  · exact Prod.ext (Fin.ext (congrArg Prod.snd h)) (Fin.ext (congrArg Prod.fst h))
  · exact Prod.ext (Fin.ext (congrArg Prod.fst h)) (Fin.ext (congrArg Prod.snd h))

/-- No matrix entry in the specified rectangle is cheap. -/
def emptyRectangle {n : ℕ} (byRow : Bool) (t : ℝ) (S T : Finset (Fin n)) : Set CostArray :=
  ⋂ p ∈ S ×ˢ T, (fun C : CostArray => C (orientedEntry byRow p)) ⁻¹' Ioi t

@[simp] theorem mem_emptyRectangle {n : ℕ} (byRow : Bool) (t : ℝ)
    (S T : Finset (Fin n)) (C : CostArray) :
    C ∈ emptyRectangle byRow t S T ↔
      ∀ i ∈ S, ∀ j ∈ T, t < C (orientedEntry byRow (i, j)) := by
  simp only [emptyRectangle, Set.mem_iInter, Set.mem_preimage, Set.mem_Ioi]
  constructor
  · intro h i hi j hj
    exact h (i, j) (mem_product.mpr ⟨hi, hj⟩)
  · rintro h ⟨i, j⟩ hp
    exact h i (mem_product.mp hp).1 j (mem_product.mp hp).2

/-- An empty rectangle has exactly the product of its edge absence probabilities. -/
theorem measure_emptyRectangle {n : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (byRow : Bool) (t : ℝ) (S T : Finset (Fin n)) :
    iidCosts μ (emptyRectangle byRow t S T) = μ (Ioi t) ^ (S.card * T.card) := by
  let E (p : Fin n × Fin n) (C : CostArray) := C (orientedEntry byRow p)
  have hid : iIndepFun (fun i : ℕ × ℕ => fun C : CostArray => C i) (iidCosts μ) :=
    iIndepFun_infinitePi (P := fun _ : ℕ × ℕ => μ) (X := fun _ => id) (fun _ => measurable_id)
  have hE : iIndepFun E (iidCosts μ) := hid.precomp (orientedEntry_injective byRow)
  have hA (p : Fin n × Fin n) :
      MeasurableSet[MeasurableSpace.comap (E p) inferInstance] ((E p) ⁻¹' Ioi t) :=
    ⟨Ioi t, measurableSet_Ioi, rfl⟩
  have hprob (p : Fin n × Fin n) : iidCosts μ ((E p) ⁻¹' Ioi t) = μ (Ioi t) := by
    let j := orientedEntry byRow p
    change iidCosts μ ((fun C : CostArray => C j) ⁻¹' Ioi t) = _
    rw [← Measure.map_apply (measurable_pi_apply j) measurableSet_Ioi]
    exact congrArg (fun ν : Measure ℝ => ν (Ioi t))
      (Measure.infinitePi_map_eval (fun _ : ℕ × ℕ => μ) j)
  change iidCosts μ (⋂ p ∈ S ×ˢ T, (E p) ⁻¹' Ioi t) = _
  rw [hE.meas_biInter (fun p _ => hA p)]
  simp only [hprob, Finset.prod_const, Finset.card_product]

/-- The vertices reached by a cheap edge from the specified side of a rectangle. -/
noncomputable def cheapNeighbors {n : ℕ} (byRow : Bool) (t : ℝ) (S : Finset (Fin n))
    (C : CostArray) : Finset (Fin n) :=
  open Classical in
  univ.filter fun j => ∃ i ∈ S, C (orientedEntry byRow (i, j)) ≤ t

@[simp] theorem mem_cheapNeighbors {n : ℕ} (byRow : Bool) (t : ℝ)
    (S : Finset (Fin n)) (C : CostArray) (j : Fin n) :
    j ∈ cheapNeighbors byRow t S C ↔ ∃ i ∈ S, C (orientedEntry byRow (i, j)) ≤ t := by
  classical
  simp [cheapNeighbors]

/-- Failure to expand tenfold for some set of size `s` on the given side. -/
def badExpansionAtSize (n : ℕ) (byRow : Bool) (t : ℝ) (s : ℕ) : Set CostArray :=
  {C | ∃ S : Finset (Fin n), S.card = s ∧ (cheapNeighbors byRow t S C).card < 10 * s}

/-- Failure to have any cheap edge between a pair of opposite sets of size `h`. -/
def badCutAtSize (n : ℕ) (t : ℝ) (h : ℕ) : Set CostArray :=
  {C | ∃ S T : Finset (Fin n), S.card = h ∧ T.card = h ∧ C ∈ emptyRectangle true t S T}

private abbrev SizedSubset (n s : ℕ) := ↥((univ : Finset (Fin n)).powersetCard s)

private theorem sizedSubset_card {n s : ℕ} (S : SizedSubset n s) : S.val.card = s :=
  (Finset.mem_powersetCard.mp S.property).2

/-- The union bound for a failing expansion at one size and on one side.
The count is `choose n s * choose n (10 * s)`, with each witness excluding all
`s * (n - 10 * s)` edges to the outside of a possible neighbor set. -/
theorem measure_badExpansionAtSize_le (n : ℕ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (byRow : Bool) (t : ℝ) (s : ℕ) (hs : 10 * s ≤ n) :
    iidCosts μ (badExpansionAtSize n byRow t s) ≤
      (n.choose s : ℝ≥0∞) * (n.choose (10 * s) : ℝ≥0∞) *
        μ (Ioi t) ^ (s * (n - 10 * s)) := by
  classical
  let A (p : SizedSubset n s × SizedSubset n (10 * s)) :=
    emptyRectangle byRow t p.1.val (univ \ p.2.val)
  have hsub : badExpansionAtSize n byRow t s ⊆ ⋃ p, A p := by
    rintro C ⟨S, hS, hN⟩
    obtain ⟨T, hNT, _, hT⟩ := Finset.exists_subsuperset_card_eq
      (Finset.subset_univ (cheapNeighbors byRow t S C)) hN.le (by simpa using hs)
    let pair : SizedSubset n s × SizedSubset n (10 * s) :=
      (⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hS⟩⟩,
       ⟨T, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hT⟩⟩)
    refine mem_iUnion.mpr ⟨pair, (mem_emptyRectangle byRow t S (univ \ T) C).mpr ?_⟩
    intro i hi j hj
    apply lt_of_not_ge
    intro hx
    exact (Finset.mem_sdiff.mp hj).2 (hNT ((mem_cheapNeighbors byRow t S C j).mpr ⟨i, hi, hx⟩))
  have hA (p : SizedSubset n s × SizedSubset n (10 * s)) :
      iidCosts μ (A p) = μ (Ioi t) ^ (s * (n - 10 * s)) := by
    change iidCosts μ (emptyRectangle byRow t p.1.val (univ \ p.2.val)) = _
    rw [measure_emptyRectangle, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp [sizedSubset_card]
  calc
    _ ≤ iidCosts μ (⋃ p, A p) := measure_mono hsub
    _ ≤ ∑' p, iidCosts μ (A p) := measure_iUnion_le A
    _ = _ := by
      rw [tsum_fintype]
      simp [hA, nsmul_eq_mul, Fintype.card_prod, Nat.cast_mul]

/-- The union bound for a failing cut at one size. -/
theorem measure_badCutAtSize_le (n : ℕ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (t : ℝ) (h : ℕ) :
    iidCosts μ (badCutAtSize n t h) ≤
      (n.choose h : ℝ≥0∞) * (n.choose h : ℝ≥0∞) * μ (Ioi t) ^ (h * h) := by
  classical
  let A (p : SizedSubset n h × SizedSubset n h) := emptyRectangle true t p.1.val p.2.val
  have hsub : badCutAtSize n t h ⊆ ⋃ p, A p := by
    rintro C ⟨S, T, hS, hT, hC⟩
    exact mem_iUnion.mpr ⟨(⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hS⟩⟩,
      ⟨T, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hT⟩⟩), hC⟩
  have hA (p : SizedSubset n h × SizedSubset n h) :
      iidCosts μ (A p) = μ (Ioi t) ^ (h * h) := by
    change iidCosts μ (emptyRectangle true t p.1.val p.2.val) = _
    simp [measure_emptyRectangle, sizedSubset_card]
  calc
    _ ≤ iidCosts μ (⋃ p, A p) := measure_mono hsub
    _ ≤ ∑' p, iidCosts μ (A p) := measure_iUnion_le A
    _ = _ := by
      rw [tsum_fintype]
      simp [hA, nsmul_eq_mul, Fintype.card_prod, Nat.cast_mul]

/-- The logarithm `log(e n/s)` in the completion cutoff. -/
noncomputable def expansionLog (n s : ℕ) : ℝ :=
  1 + Real.log ((n : ℝ) / s)

theorem expansionLog_ge_one {n s : ℕ} (hs : 0 < s) (hsn : s ≤ n) :
    1 ≤ expansionLog n s := by
  have hs' : 0 < (s : ℝ) := by exact_mod_cast hs
  have hsn' : (s : ℝ) ≤ n := by exact_mod_cast hsn
  unfold expansionLog
  linarith [Real.log_nonneg ((one_le_div hs').2 hsn')]

theorem expansionLog_antitone {n s t : ℕ} (hn : 0 < n) (hs : 0 < s) (hst : s ≤ t) :
    expansionLog n t ≤ expansionLog n s := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hs' : 0 < (s : ℝ) := by exact_mod_cast hs
  have hst' : (s : ℝ) ≤ t := by exact_mod_cast hst
  unfold expansionLog
  exact add_le_add_right (Real.log_le_log (div_pos hn' (hs'.trans_le hst'))
    (div_le_div_of_nonneg_left hn'.le hs' hst')) _

theorem log_n_le_size_mul_expansionLog {n s : ℕ} (hs : 0 < s) (hsn : s ≤ n) :
    Real.log (n : ℝ) ≤ (s : ℝ) * expansionLog n s := by
  have hs' : 0 < (s : ℝ) := by exact_mod_cast hs
  have hs₁ : 1 ≤ (s : ℝ) := by exact_mod_cast hs
  have hsn' : (s : ℝ) ≤ n := by exact_mod_cast hsn
  have hn' : 0 < (n : ℝ) := hs'.trans_le hsn'
  have hlo : 0 ≤ Real.log ((n : ℝ) / s) := Real.log_nonneg ((one_le_div hs').2 hsn')
  have hd : Real.log ((n : ℝ) / s) = Real.log n - Real.log s :=
    Real.log_div hn'.ne' hs'.ne'
  have hslog := Real.log_le_sub_one_of_pos hs'
  unfold expansionLog
  nlinarith [mul_nonneg (sub_nonneg.mpr hs₁) hlo]

/-- A single term in the binomial expansion of `(1+s/n)^n` bounds the
number of choices by `exp(s log(e n/s))`. -/
theorem choose_le_exp_expansionLog {n s : ℕ} (hs : 0 < s) (hsn : s ≤ n) :
    (n.choose s : ℝ) ≤ Real.exp ((s : ℝ) * expansionLog n s) := by
  have hs' : 0 < (s : ℝ) := by exact_mod_cast hs
  have hsn' : (s : ℝ) ≤ n := by exact_mod_cast hsn
  have hn' : 0 < (n : ℝ) := hs'.trans_le hsn'
  let a : ℝ := (s : ℝ) / n
  have ha : 0 < a := div_pos hs' hn'
  have hbin : a ^ s * (n.choose s : ℝ) ≤ (a + 1) ^ n := by
    rw [add_pow]
    simpa only [one_pow, mul_one] using
      (Finset.single_le_sum (s := range (n + 1))
        (f := fun m : ℕ => a ^ m * (1 : ℝ) ^ (n - m) * n.choose m)
        (fun m _ => by positivity) (mem_range.mpr (Nat.lt_succ_of_le hsn)))
  have hpow : (a + 1) ^ n ≤ Real.exp (s : ℝ) := by
    calc
      _ ≤ (Real.exp a) ^ n := pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp a) _
      _ = _ := by
        rw [← Real.exp_nat_mul]
        congr 1
        dsimp [a]
        field_simp
  have hcancel : a ^ s * Real.exp ((s : ℝ) * expansionLog n s) = Real.exp (s : ℝ) := by
    unfold expansionLog
    rw [mul_add, mul_one, Real.exp_add, Real.exp_nat_mul, Real.exp_log (div_pos hn' hs')]
    rw [mul_left_comm, ← mul_pow]
    have hab : a * ((n : ℝ) / s) = 1 := by
      dsimp [a]
      field_simp
    simp [hab]
  exact le_of_mul_le_mul_left ((hbin.trans hpow).trans_eq hcancel.symm) (pow_pos ha _)

private theorem measure_Ioi_eq_ofReal_one_sub_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (t : ℝ) : μ (Ioi t) = ENNReal.ofReal (1 - cdf μ t) := by
  rw [← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic,
    ENNReal.ofReal_sub _ (cdf_nonneg _ _), ofReal_cdf, ENNReal.ofReal_one]

private theorem absence_pow_le_exp (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ)
    (m : ℕ) : (1 - cdf μ t) ^ m ≤ Real.exp (-((m : ℝ) * cdf μ t)) := by
  rw [← mul_neg, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (sub_nonneg.mpr (cdf_le_one _ _))
    (Real.one_sub_le_exp_neg _) _

/-- Exponential bound for one size and one side, given the lower retention probability.
With `c = A^d / 2` this is the corresponding bound in the manuscript. -/
theorem measure_badExpansionAtSize_le_exp (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (n s : ℕ) (byRow : Bool) (t c : ℝ) (hs : 0 < s) (hsn : 40 * s ≤ n)
    (hc : 0 ≤ c) (hretention : c / n * expansionLog n s ≤ cdf μ t) :
    iidCosts μ (badExpansionAtSize n byRow t s) ≤
      ENNReal.ofReal (Real.exp (-(3 * c / 4 - 11) * s * expansionLog n s)) := by
  have hsₙ : s ≤ n := by omega
  have hs₁₀ : 0 < 10 * s := by omega
  have h10ₙ : 10 * s ≤ n := by omega
  have hs' : 0 < (s : ℝ) := by exact_mod_cast hs
  have hn' : 0 < (n : ℝ) := hs'.trans_le (by exact_mod_cast hsₙ)
  let L := expansionLog n s
  have hL : 0 ≤ L := zero_le_one.trans (expansionLog_ge_one hs hsₙ)
  have hquarter : 3 * (n : ℝ) / 4 ≤ ((n - 10 * s : ℕ) : ℝ) := by
    have hh : (40 : ℝ) * s ≤ n := by exact_mod_cast hsn
    rw [Nat.cast_sub h10ₙ]
    push_cast
    linarith
  have hexponent : 3 * c / 4 * (s : ℝ) * L ≤ (↑(s * (n - 10 * s)) : ℝ) * cdf μ t := by
    have hb := mul_le_mul (mul_le_mul_of_nonneg_left hquarter hs'.le) hretention
      (mul_nonneg (div_nonneg hc hn'.le) hL) (by positivity : 0 ≤ (s : ℝ) * ↑(n - 10 * s))
    calc
      _ = ((s : ℝ) * (3 * n / 4)) * (c / n * L) := by field_simp
      _ ≤ _ := by push_cast; exact hb
  have hchoose₁ := choose_le_exp_expansionLog hs hsₙ
  have hchoose₂ : (n.choose (10 * s) : ℝ) ≤ Real.exp ((10 : ℝ) * s * L) := by
    apply (choose_le_exp_expansionLog hs₁₀ h10ₙ).trans
    apply Real.exp_le_exp.mpr
    push_cast
    exact mul_le_mul_of_nonneg_left
      (expansionLog_antitone (hs.trans_le hsₙ) hs (by omega : s ≤ 10 * s)) (by positivity)
  have habs : (1 - cdf μ t) ^ (s * (n - 10 * s)) ≤ Real.exp (-(3 * c / 4 * (s : ℝ) * L)) :=
    (absence_pow_le_exp μ t _).trans (Real.exp_le_exp.mpr (neg_le_neg hexponent))
  have hbound :
      (n.choose s : ℝ) * (n.choose (10 * s) : ℝ) * (1 - cdf μ t) ^ (s * (n - 10 * s)) ≤
        Real.exp (-(3 * c / 4 - 11) * s * L) := by
    calc
      _ ≤ Real.exp ((s : ℝ) * L) * Real.exp ((10 : ℝ) * s * L) *
            Real.exp (-(3 * c / 4 * (s : ℝ) * L)) :=
        mul_le_mul (mul_le_mul hchoose₁ hchoose₂ (by positivity) (by positivity))
          habs (pow_nonneg (sub_nonneg.mpr (cdf_le_one μ t)) _) (by positivity)
      _ = _ := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
  refine (measure_badExpansionAtSize_le n μ byRow t s h10ₙ).trans ?_
  have hh := ENNReal.ofReal_le_ofReal hbound
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_pow (sub_nonneg.mpr (cdf_le_one μ t)),
    ← measure_Ioi_eq_ofReal_one_sub_cdf] at hh
  simp only [ENNReal.ofReal_natCast] at hh
  exact hh

/-- Exponential bound for the large cuts, with the factor corresponding to
the manuscript's `h ≥ n / 80`. -/
theorem measure_badCutAtSize_le_exp (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (n h : ℕ) (t c : ℝ) (hn : 0 < n) (hh : (n : ℝ) / 80 ≤ h)
    (hc : 0 ≤ c) (hretention : c / n ≤ cdf μ t) :
    iidCosts μ (badCutAtSize n t h) ≤
      ENNReal.ofReal (Real.exp ((n : ℝ) * Real.log 4 - c * n / 6400)) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hpow : ((n : ℝ) / 80) * ((n : ℝ) / 80) ≤ (h : ℝ) * h :=
    mul_le_mul hh hh (by positivity) (by positivity)
  have hcredits : c * (n : ℝ) / 6400 ≤ (↑(h * h) : ℝ) * cdf μ t := by
    calc
      _ = (((n : ℝ) / 80) * ((n : ℝ) / 80)) * (c / n) := by field_simp; norm_num
      _ ≤ _ := by
        push_cast
        exact mul_le_mul hpow hretention (div_nonneg hc hn'.le) (by positivity)
  have habs : (1 - cdf μ t) ^ (h * h) ≤ Real.exp (-(c * (n : ℝ) / 6400)) :=
    (absence_pow_le_exp μ t _).trans (Real.exp_le_exp.mpr (neg_le_neg hcredits))
  have hchoose : (n.choose h : ℝ) ≤ (2 : ℝ) ^ n := by
    exact_mod_cast Nat.choose_le_two_pow n h
  have hbound : (n.choose h : ℝ) * (n.choose h : ℝ) * (1 - cdf μ t) ^ (h * h) ≤
      Real.exp ((n : ℝ) * Real.log 4 - c * n / 6400) := by
    calc
      _ ≤ ((2 : ℝ) ^ n * (2 : ℝ) ^ n) * Real.exp (-(c * (n : ℝ) / 6400)) :=
        mul_le_mul (mul_le_mul hchoose hchoose (by positivity) (by positivity))
          habs (pow_nonneg (sub_nonneg.mpr (cdf_le_one μ t)) _) (by positivity)
      _ = _ := by
        rw [← mul_pow, sub_eq_add_neg, Real.exp_add, Real.exp_nat_mul, Real.exp_log (by norm_num)]
        norm_num
  refine (measure_badCutAtSize_le n μ t h).trans ?_
  have he := ENNReal.ofReal_le_ofReal hbound
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_pow (sub_nonneg.mpr (cdf_le_one μ t)),
    ← measure_Ioi_eq_ofReal_one_sub_cdf] at he
  simp only [ENNReal.ofReal_natCast] at he
  exact he

private noncomputable def smallExpansionFailure (n : ℕ) (cutoff : ℕ → ℝ)
    (p : Fin n × Fin n × Bool) : Set CostArray :=
  if p.1.val ≤ p.2.1.val ∧ p.2.1.val + 1 ≤ n / 40 then
    badExpansionAtSize n p.2.2 (cutoff (p.1.val + 1)) (p.2.1.val + 1)
  else ∅

/-- Failure of the common event for the entire family of cost cutoffs.
The `j`-th cutoff applies to expansion of sets of sizes `j` through `n / 40`
on both sides, and to every cut with both sides of size `n / 40`. -/
noncomputable def commonExpansionFailure (n : ℕ) (cutoff : ℕ → ℝ) : Set CostArray :=
  (⋃ p : Fin n × Fin n × Bool, smallExpansionFailure n cutoff p) ∪
    (⋃ j : Fin n, badCutAtSize n (cutoff (j.val + 1)) (n / 40))

/-- Outside the common bad event, each admissible vertex set expands tenfold. -/
theorem expansion_of_not_mem_commonFailure {n : ℕ} {cutoff : ℕ → ℝ} {C : CostArray}
    (hC : C ∉ commonExpansionFailure n cutoff) (byRow : Bool) {j : ℕ}
    (hj : 0 < j) (S : Finset (Fin n)) (hjs : j ≤ S.card) (hs : S.card ≤ n / 40) :
    10 * S.card ≤ (cheapNeighbors byRow (cutoff j) S C).card := by
  by_contra! hsmall
  have hsₙ : S.card ≤ n := hs.trans (Nat.div_le_self _ _)
  have hs₀ : 0 < S.card := hj.trans_le hjs
  let p : Fin n × Fin n × Bool := (⟨j - 1, by omega⟩, ⟨S.card - 1, by omega⟩, byRow)
  have hp : p.1.val ≤ p.2.1.val ∧ p.2.1.val + 1 ≤ n / 40 := by dsimp [p]; omega
  have hmem : C ∈ smallExpansionFailure n cutoff p := by
    rw [smallExpansionFailure, if_pos hp]
    change ∃ T : Finset (Fin n), T.card = S.card - 1 + 1 ∧
      (cheapNeighbors byRow (cutoff (j - 1 + 1)) T C).card < 10 * (S.card - 1 + 1)
    rw [Nat.sub_add_cancel hs₀, Nat.sub_add_cancel hj]
    exact ⟨S, rfl, hsmall⟩
  exact hC (Or.inl (Set.mem_iUnion.mpr ⟨p, hmem⟩))

/-- Outside the common bad event, every admissible opposite cut has a cheap edge. -/
theorem cheapEdge_of_not_mem_commonFailure {n : ℕ} {cutoff : ℕ → ℝ} {C : CostArray}
    (hC : C ∉ commonExpansionFailure n cutoff) {j : ℕ} (hj : 0 < j) (hjn : j ≤ n)
    (S T : Finset (Fin n)) (hS : S.card = n / 40) (hT : T.card = n / 40) :
    ∃ i ∈ S, ∃ k ∈ T, C (i.val, k.val) ≤ cutoff j := by
  by_contra! h
  let q : Fin n := ⟨j - 1, by omega⟩
  have hm : C ∈ badCutAtSize n (cutoff (q.val + 1)) (n / 40) := by
    refine ⟨S, T, hS, hT, (mem_emptyRectangle _ _ _ _ _).2 ?_⟩
    intro i hi k hk
    change cutoff (j - 1 + 1) < C (i.val, k.val)
    rw [Nat.sub_add_cancel hj]
    exact h i hi k hk
  exact hC (Or.inr (Set.mem_iUnion.mpr ⟨q, hm⟩))

/-- The simultaneous expansion probability bound given uniform lower retention.
There are at most two times `n^2` expansion terms and `n` cut terms. -/
theorem measure_commonExpansionFailure_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (n : ℕ) (cutoff : ℕ → ℝ) (c B : ℝ) (hn : 80 ≤ n) (hc : 0 ≤ c) (hB : 0 ≤ B)
    (hc₁ : B + 2 ≤ 3 * c / 4 - 11) (hc₂ : Real.log 4 + 1 ≤ c / 6400)
    (hretention : ∀ j : ℕ, 0 < j → j ≤ n → c / n * expansionLog n j ≤ cdf μ (cutoff j)) :
    iidCosts μ (commonExpansionFailure n cutoff) ≤
      (2 * (n : ℝ≥0∞) ^ 2) * ENNReal.ofReal (Real.exp (-(B + 2) * Real.log (n : ℝ))) +
        (n : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(n : ℝ))) := by
  have hn₀ : 0 < n := by omega
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn₀
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn₀
  have hc₀ : 0 ≤ c / (n : ℝ) := div_nonneg hc hn'.le
  let A : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(B + 2) * Real.log (n : ℝ)))
  let D : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(n : ℝ)))
  have hsmall (p : Fin n × Fin n × Bool) : iidCosts μ (smallExpansionFailure n cutoff p) ≤ A := by
    unfold smallExpansionFailure
    split
    · rename_i hp
      let j := p.1.val + 1
      let s := p.2.1.val + 1
      have hs : 0 < s := Nat.zero_lt_succ _
      have hjs : j ≤ s := Nat.succ_le_succ hp.1
      have hj : 0 < j := Nat.zero_lt_succ _
      have hs₄₀ : 40 * s ≤ n := by
        have hfloor : s ≤ n / 40 := hp.2
        omega
      have hsn : s ≤ n := by omega
      have hlo : c / n * expansionLog n s ≤ cdf μ (cutoff j) :=
        (mul_le_mul_of_nonneg_left (expansionLog_antitone hn₀ hj hjs) hc₀).trans
          (hretention j hj (hjs.trans hsn))
      apply (measure_badExpansionAtSize_le_exp μ n s p.2.2 (cutoff j) c hs hs₄₀ hc hlo).trans
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hlog := log_n_le_size_mul_expansionLog hs hsn
      have hq := mul_le_mul hc₁ hlog (Real.log_nonneg hn₁) (by linarith : 0 ≤ 3 * c / 4 - 11)
      linarith
    · simp
  have hcut (p : Fin n) : iidCosts μ (badCutAtSize n (cutoff (p.val + 1)) (n / 40)) ≤ D := by
    have hfloor : n ≤ 80 * (n / 40) := by omega
    have hfloor' : (n : ℝ) ≤ 80 * ((n / 40 : ℕ) : ℝ) := by exact_mod_cast hfloor
    have hj : 0 < p.val + 1 := Nat.zero_lt_succ _
    have hjn : p.val + 1 ≤ n := p.isLt
    have hlo : c / n ≤ cdf μ (cutoff (p.val + 1)) := by
      have he := mul_le_mul_of_nonneg_left (expansionLog_ge_one hj hjn) hc₀
      simp only [mul_one] at he
      exact he.trans (hretention _ hj hjn)
    apply (measure_badCutAtSize_le_exp μ n (n / 40) _ c hn₀ (by linarith) hc hlo).trans
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hn'.le (sub_nonneg.mpr hc₂)]
  unfold commonExpansionFailure
  apply (measure_union_le _ _).trans
  apply add_le_add
  · apply (measure_iUnion_le _).trans
    rw [tsum_fintype]
    calc
      _ ≤ ∑ _ : Fin n × Fin n × Bool, A := Finset.sum_le_sum (fun p _ => hsmall p)
      _ = _ := by
        change (∑ _ : Fin n × Fin n × Bool, A) = (2 * (n : ℝ≥0∞) ^ 2) * A
        simp [nsmul_eq_mul, Fintype.card_prod, Nat.cast_mul, pow_two,
          mul_assoc, mul_comm]
  · apply (measure_iUnion_le _).trans
    rw [tsum_fintype]
    calc
      _ ≤ ∑ _ : Fin n, D := Finset.sum_le_sum (fun p _ => hcut p)
      _ = _ := by
        change (∑ _ : Fin n, D) = (n : ℝ≥0∞) * D
        simp [nsmul_eq_mul]

theorem measurableSet_emptyRectangle {n : ℕ} (byRow : Bool) (t : ℝ)
    (S T : Finset (Fin n)) : MeasurableSet (emptyRectangle byRow t S T) := by
  unfold emptyRectangle
  exact MeasurableSet.iInter (fun p => MeasurableSet.iInter
    (fun _ => (measurable_pi_apply (orientedEntry byRow p)) measurableSet_Ioi))

theorem measurableSet_badExpansionAtSize (n : ℕ) (byRow : Bool) (t : ℝ) (s : ℕ) :
    MeasurableSet (badExpansionAtSize n byRow t s) := by
  classical
  let A (p : Finset (Fin n) × Finset (Fin n)) : Set CostArray :=
    if p.1.card = s ∧ p.2.card < 10 * s then emptyRectangle byRow t p.1 (univ \ p.2) else ∅
  have hA (p : Finset (Fin n) × Finset (Fin n)) : MeasurableSet (A p) := by
    dsimp only [A]
    split
    · exact measurableSet_emptyRectangle _ _ _ _
    · exact MeasurableSet.empty
  suffices he : badExpansionAtSize n byRow t s = ⋃ p, A p by
    rw [he]
    exact MeasurableSet.iUnion hA
  ext C
  constructor
  · rintro ⟨S, hS, hN⟩
    let T := cheapNeighbors byRow t S C
    have hcard : T.card < 10 * s := hN
    have hE : C ∈ emptyRectangle byRow t S (univ \ T) := by
      apply (mem_emptyRectangle _ _ _ _ _).mpr
      intro i hi j hj
      exact lt_of_not_ge (fun h => (Finset.mem_sdiff.mp hj).2
        ((mem_cheapNeighbors _ _ _ _ _).mpr ⟨i, hi, h⟩))
    apply Set.mem_iUnion.mpr
    refine ⟨(S, T), ?_⟩
    change C ∈ (if S.card = s ∧ T.card < 10 * s then emptyRectangle byRow t S
      (univ \ T) else ∅)
    rw [if_pos ⟨hS, hcard⟩]
    exact hE
  · intro h
    obtain ⟨⟨S, T⟩, hE⟩ := Set.mem_iUnion.mp h
    dsimp only [A] at hE
    split at hE
    · rename_i hcard
      have hins : cheapNeighbors byRow t S C ⊆ T := by
        intro j hj
        by_contra hjT
        obtain ⟨i, hi, hcheap⟩ := (mem_cheapNeighbors _ _ _ _ _).mp hj
        exact (not_lt_of_ge hcheap)
          ((mem_emptyRectangle _ _ _ _ _).mp hE i hi j
            (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hjT⟩))
      exact ⟨S, hcard.1, (Finset.card_le_card hins).trans_lt hcard.2⟩
    · exact False.elim hE

theorem measurableSet_badCutAtSize (n : ℕ) (t : ℝ) (h : ℕ) :
    MeasurableSet (badCutAtSize n t h) := by
  classical
  let A (p : SizedSubset n h × SizedSubset n h) := emptyRectangle true t p.1.val p.2.val
  have he : badCutAtSize n t h = ⋃ p, A p := by
    ext C
    constructor
    · rintro ⟨S, T, hS, hT, hC⟩
      exact Set.mem_iUnion.mpr ⟨(⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hS⟩⟩,
        ⟨T, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hT⟩⟩), hC⟩
    · intro hC
      obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hC
      exact ⟨p.1.val, p.2.val, sizedSubset_card _, sizedSubset_card _, hp⟩
  rw [he]
  exact MeasurableSet.iUnion (fun p => measurableSet_emptyRectangle _ _ _ _)

theorem measurableSet_commonExpansionFailure (n : ℕ) (cutoff : ℕ → ℝ) :
    MeasurableSet (commonExpansionFailure n cutoff) := by
  unfold commonExpansionFailure
  apply MeasurableSet.union
  · apply MeasurableSet.iUnion
    intro p
    unfold smallExpansionFailure
    split
    · exact measurableSet_badExpansionAtSize _ _ _ _
    · exact MeasurableSet.empty
  · exact MeasurableSet.iUnion (fun _ => measurableSet_badCutAtSize _ _ _)

end Certificate.Completion

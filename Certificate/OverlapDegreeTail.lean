import Certificate.OverlapDiscardedWeights
import Certificate.RootEdgeMarks
import Certificate.SoftConcentrationMGF

/-! The loss from trimming high degree vertices at a fixed length cutoff. -/

open Finset Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

namespace Certificate.Overlap

private theorem mgf_pi_copies {A I : Type*} [MeasurableSpace A] [Fintype I]
    (P : Measure A) [IsProbabilityMeasure P] {f : A → ℝ} (hf : Measurable f) (t : ℝ) :
    mgf (fun w : I → A => ∑ i, f (w i)) (Measure.pi (fun _ : I => P)) t =
      mgf f P t ^ Fintype.card I := by
  let X (i : I) (w : I → A) := f (w i)
  have hi : iIndepFun X (Measure.pi (fun _ : I => P)) :=
    iIndepFun_pi (X := fun _ : I => f) (fun _ => hf.aemeasurable)
  have hX (i : I) : Measurable (X i) := hf.comp (measurable_pi_apply i)
  have hmgf (i : I) : mgf (X i) (Measure.pi (fun _ : I => P)) t = mgf f P t := by
    have h := mgf_map (Y := fun w : I → A => w i) (X := f)
      (μ := Measure.pi (fun _ : I => P)) (measurable_pi_apply i).aemeasurable (t := t)
      (hf.const_mul t).exp.aestronglyMeasurable
    rw [(measurePreserving_eval (fun _ : I => P) i).map_eq] at h
    exact h.symm
  rw [show (fun w : I → A => ∑ i, f (w i)) = ∑ i, X i from funext fun _ => by simp [X],
    hi.mgf_sum hX univ]
  simp only [hmgf, prod_const, card_univ]

private noncomputable def shortIndicator (d κ R : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  if lengthScale d κ n * x ≤ R then 1 else 0

private theorem measurable_shortIndicator (d κ R : ℝ) (n : ℕ) :
    Measurable (shortIndicator d κ R n) :=
  measurable_const.piecewise
    (measurableSet_le (f := fun x : ℝ => lengthScale d κ n * x) (by fun_prop) measurable_const)
    measurable_const

private theorem mgf_shortIndicator {μ : Measure ℝ} [IsProbabilityMeasure μ] {κ : ℝ}
    (hκ : 0 < κ) (d R : ℝ) {n : ℕ} (hn : 0 < n) :
    mgf (shortIndicator d κ R n) μ 2 =
      1 + (Real.exp 2 - 1) * shortEdgeProbability μ d κ R n := by
  let s : Set ℝ := {x | lengthScale d κ n * x ≤ R}
  have hs : MeasurableSet s := measurableSet_le (by fun_prop) measurable_const
  have hp : μ.real s = shortEdgeProbability μ d κ R n := by
    have h := scaledLengthLaw_Iic (μ := μ) (d := d) hκ hn R
    unfold scaledLengthLaw at h
    rw [Measure.map_apply (by fun_prop) measurableSet_Iic] at h
    simpa only [measureReal_def, s, Set.preimage, Set.mem_Iic, ENNReal.toReal_ofReal,
      shortEdgeProbability, cdf_nonneg] using congrArg ENNReal.toReal h
  have hI : (fun x => Real.exp (2 * shortIndicator d κ R n x)) =
      fun x => 1 + (Real.exp 2 - 1) * s.indicator (fun _ : ℝ => (1 : ℝ)) x := by
    funext x
    by_cases hx : x ∈ s
    · simp [shortIndicator, show lengthScale d κ n * x ≤ R from hx, hx]
    · simp [shortIndicator, show ¬ lengthScale d κ n * x ≤ R from hx, hx]
  unfold mgf
  rw [hI, integral_add (integrable_const _)
    (((integrable_const (1:ℝ)).indicator hs).const_mul _),
    integral_const, probReal_univ, one_smul, integral_const_mul, integral_indicator hs,
    setIntegral_const, smul_eq_mul, mul_one, hp]

private noncomputable def lengthDegree (d κ R : ℝ) {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ j, shortIndicator d κ R n (x j)

private theorem measurable_lengthDegree (d κ R : ℝ) (n : ℕ) :
    Measurable (lengthDegree d κ R (n := n)) :=
  Finset.measurable_sum _ fun j _ => (measurable_shortIndicator ..).comp (measurable_pi_apply j)

private theorem lengthDegree_mem (d κ R : ℝ) {n : ℕ} (x : Fin n → ℝ) :
    lengthDegree d κ R x ∈ Icc 0 (n : ℝ) := by
  constructor
  · exact sum_nonneg fun j _ => by unfold shortIndicator; split_ifs <;> norm_num
  · calc
      _ ≤ ∑ _ : Fin n, (1 : ℝ) := sum_le_sum fun j _ => by
        unfold shortIndicator
        split_ifs <;> norm_num
      _ = _ := by simp

private noncomputable def excessDegree (d κ R : ℝ) (D : ℕ) {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  if (D : ℝ) < lengthDegree d κ R x then lengthDegree d κ R x else 0

private theorem measurable_excessDegree (d κ R : ℝ) (n D : ℕ) :
    Measurable (excessDegree d κ R D (n := n)) :=
  (measurable_lengthDegree ..).piecewise (measurableSet_lt measurable_const
    (measurable_lengthDegree ..)) measurable_const

private theorem excessDegree_le (d κ R : ℝ) (D : ℕ) {n : ℕ} (x : Fin n → ℝ) :
    excessDegree d κ R D x ≤ (n : ℝ) := by
  unfold excessDegree
  split_ifs
  · exact (lengthDegree_mem d κ R x).2
  · positivity

private theorem degreeE_mgf_le {A : Type*} [MeasurableSpace A] (P : Measure A)
    [IsProbabilityMeasure P] {f : A → ℝ} (hf : Measurable f) {B : ℝ}
    (hB : ∀ x, f x ≤ B) (D : ℕ) :
    mgf (fun a => if (D : ℝ) < f a then f a else 0) P 1 ≤
      1 + Real.exp (-(D : ℝ)) * mgf f P 2 := by
  let g (a : A) := if (D : ℝ) < f a then f a else 0
  have hm : Measurable g :=
    hf.piecewise (measurableSet_lt measurable_const hf) measurable_const
  have hg : Integrable (fun a => Real.exp (g a)) P :=
    Integrable.of_bound hm.exp.aestronglyMeasurable (Real.exp (max B 0))
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
        unfold g
        split_ifs
        · exact (hB x).trans (le_max_left _ _)
        · exact le_max_right _ _)
  have h2 : Integrable (fun a => Real.exp (2 * f a)) P :=
    Integrable.of_bound ((hf.const_mul 2).exp.aestronglyMeasurable) (Real.exp (2 * B))
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
        gcongr
        exact hB x)
  change mgf g P 1 ≤ _
  unfold mgf
  simp only [one_mul]
  calc
    _ ≤ ∫ a, 1 + Real.exp (-(D : ℝ)) * Real.exp (2 * f a) ∂P :=
      integral_mono hg ((integrable_const _).add (h2.const_mul _)) (fun a => by
        unfold g
        split_ifs with ha
        · rw [← Real.exp_add]
          have hmul : Real.exp (f a) ≤ Real.exp (-(D : ℝ) + 2 * f a) :=
            Real.exp_le_exp.mpr (by linarith)
          linarith
        · rw [Real.exp_zero]
          exact le_add_of_nonneg_right (by positivity))
    _ = _ := by rw [integral_add (integrable_const _) (h2.const_mul _), integral_const,
      probReal_univ, one_smul, integral_const_mul]

private theorem degree_mgf_le {μ : Measure ℝ} [IsProbabilityMeasure μ] {κ : ℝ}
    (hκ : 0 < κ) (d R : ℝ) {n : ℕ} (hn : 0 < n)
    (hpn : (n : ℝ) * shortEdgeProbability μ d κ R n ≤ R ^ d + 1) :
    mgf (lengthDegree d κ R (n := n)) (Measure.pi (fun _ : Fin n => μ)) 2 ≤
      Real.exp ((Real.exp 2 - 1) * (R ^ d + 1)) := by
  change mgf (fun x : Fin n → ℝ => ∑ j, shortIndicator d κ R n (x j)) _ _ ≤ _
  rw [mgf_pi_copies μ (measurable_shortIndicator ..), Fintype.card_fin,
    mgf_shortIndicator hκ d R hn]
  have hcoef : 0 ≤ Real.exp 2 - 1 :=
    sub_nonneg.mpr (Real.one_le_exp_iff.mpr (by norm_num))
  have hp : 0 ≤ shortEdgeProbability μ d κ R n := cdf_nonneg _ _
  calc
    _ ≤ Real.exp ((Real.exp 2 - 1) * shortEdgeProbability μ d κ R n) ^ n :=
      pow_le_pow_left₀ (by positivity)
        ((add_comm _ _).le.trans (Real.add_one_le_exp _)) n
    _ = Real.exp ((Real.exp 2 - 1) * ((n : ℝ) * shortEdgeProbability μ d κ R n)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hpn hcoef)

private theorem ae_eventually_excessDegree_lt_linear {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {d κ R ε : ℝ} (hd : 0 < d) (hκ : 0 < κ) (hR : 0 < R)
    (hμ : SmallCostTail μ κ d) (hε : 0 < ε) :
    ∃ D : ℕ, ∀ (row : (n : ℕ) → CostArray → Fin n → Fin n → ℝ),
      (∀ n, MeasurePreserving (row n) (iidCosts μ)
        (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ)))) →
      ∀ᵐ C ∂iidCosts μ, ∀ᶠ n in atTop, (∑ i : Fin n, excessDegree d κ R D (row n C i)) <
        ε * (n : ℝ) := by
  let : IsProbabilityMeasure (iidCosts μ) := by unfold iidCosts; infer_instance
  let K := Real.exp ((Real.exp 2 - 1) * (R ^ d + 1))
  have hdecay : Tendsto (fun D : ℕ => K * Real.exp (-(D : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_apply] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul K
  obtain ⟨D, hD⟩ := (hdecay.eventually (Iio_mem_nhds (half_pos hε))).exists
  refine ⟨D, fun row hrow => ?_⟩
  let F (n : ℕ) (w : Fin n → Fin n → ℝ) := ∑ i, excessDegree d κ R D (w i)
  have hFm (n : ℕ) : Measurable (F n) :=
    Finset.measurable_sum _ fun i _ => (measurable_excessDegree d κ R n D).comp
      (measurable_pi_apply i)
  have hint n : Integrable (fun C => Real.exp (F n (row n C))) (iidCosts μ) :=
    Integrable.of_bound ((hFm n).comp (hrow n).measurable).exp.aestronglyMeasurable
      (Real.exp ((n : ℝ) * n)) (Eventually.of_forall fun C => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
        calc
          _ ≤ ∑ _ : Fin n, (n : ℝ) := sum_le_sum fun i _ => excessDegree_le ..
          _ = _ := by simp)
  have hb : ∀ᶠ n in atTop, mgf (fun C => F n (row n C)) (iidCosts μ) 1 ≤
      Real.exp ((ε / 2) * (n : ℝ)) := by
    filter_upwards [(tendsto_scaled_shortEdgeProbability hd hκ hR hμ).eventually
      (Iio_mem_nhds (show R ^ d < R ^ d + (1:ℝ) by linarith)),
      eventually_gt_atTop (0 : ℕ)] with n hpn hn
    have hmap := mgf_map (μ := iidCosts μ) (Y := row n) (X := F n) (hrow n).measurable.aemeasurable (t := 1)
      ((hFm n).const_mul 1).exp.aestronglyMeasurable
    rw [(hrow n).map_eq] at hmap
    change mgf (F n) _ _ = mgf (fun C => F n (row n C)) _ _ at hmap
    rw [← hmap]
    change mgf (fun w : Fin n → Fin n → ℝ => ∑ i, excessDegree d κ R D (w i)) _ _ ≤ _
    rw [mgf_pi_copies (Measure.pi (fun _ : Fin n => μ))
      (measurable_excessDegree ..), Fintype.card_fin]
    let P := Measure.pi (fun _ : Fin n => μ)
    have hinner : mgf (excessDegree d κ R D (n := n)) P 1 ≤ Real.exp (ε / 2) := by
      have h := degreeE_mgf_le P (measurable_lengthDegree d κ R n)
        (fun x => (lengthDegree_mem d κ R x).2) D
      refine h.trans ?_
      calc
        _ ≤ 1 + Real.exp (-(D : ℝ)) * K := add_le_add_right
          (mul_le_mul_of_nonneg_left (degree_mgf_le hκ d R hn
            (show (n : ℝ) * shortEdgeProbability μ d κ R n ≤ R ^ d + 1 from hpn.le))
            (Real.exp_nonneg _)) 1
        _ ≤ Real.exp (ε / 2) := by
          have hD' : Real.exp (-(D : ℝ)) * K < ε / 2 := by
            rw [mul_comm]
            exact hD
          linarith [Real.add_one_le_exp (ε / 2)]
    refine (pow_le_pow_left₀ mgf_nonneg hinner n).trans ?_
    rw [← Real.exp_nat_mul, mul_comm]
  have ha := ae_eventually_lt_linear_of_mgf (iidCosts μ) (c := ε / 2)
    (δ := ε / 2) (half_pos hε) hint hb
  convert ha using 5
  ring

/-- Transpose the two sides of the infinite cost array. -/
def transposeCosts (C : CostArray) : CostArray := C ∘ Prod.swap

/-- Transposition preserves the iid cost law. -/
theorem measurePreserving_transposeCosts (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    MeasurePreserving transposeCosts (iidCosts μ) (iidCosts μ) := by
  let η : Equiv.Perm (ℕ × ℕ) := Equiv.prodComm ℕ ℕ
  exact ⟨measurable_pi_iff.mpr fun i => measurable_pi_apply (η i),
    Measure.map_infinitePi_infinitePi_of_inj η.injective⟩

private theorem rowDegree_eq (d κ R : ℝ) {n : ℕ} (C : CostArray) (i : Fin n) :
    ((rowEdges (retainedEdges d κ R n C) i).card : ℝ) =
      lengthDegree d κ R (costRows n C i) := by
  let s := (univ : Finset (Fin n)).filter fun j => edgeLength d κ n C (i,j) ≤ R
  let e : Fin n ↪ Fin n × Fin n := ⟨fun j => (i,j), fun _ _ h => congrArg Prod.snd h⟩
  have h : rowEdges (retainedEdges d κ R n C) i = s.map e := by
    ext p
    rcases p with ⟨r,c⟩
    simp only [rowEdges, retainedEdges, s, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_map, e]
    constructor
    · rintro ⟨h,rfl⟩
      exact ⟨c,h,rfl⟩
    · rintro ⟨j,h,hj⟩
      rcases Prod.mk.inj hj with ⟨rfl,rfl⟩
      exact ⟨h,rfl⟩
  rw [h, card_map]
  dsimp only [s, lengthDegree, shortIndicator, edgeLength, costRows]
  exact natCast_card_filter _ _

private theorem colDegree_eq (d κ R : ℝ) {n : ℕ} (C : CostArray) (j : Fin n) :
    ((colEdges (retainedEdges d κ R n C) j).card : ℝ) =
      lengthDegree d κ R (costRows n (transposeCosts C) j) := by
  let e := (Equiv.prodComm (Fin n) (Fin n)).toEmbedding
  have h : rowEdges (retainedEdges d κ R n (transposeCosts C)) j =
      (colEdges (retainedEdges d κ R n C) j).map e := by
    ext p
    have hmem (C' : CostArray) (q : Fin n × Fin n) :
        q ∈ retainedEdges d κ R n C' ↔ edgeLength d κ n C' q ≤ R := by
      unfold retainedEdges
      exact Finset.mem_filter.trans (and_iff_right (Finset.mem_univ _))
    simp only [e, Finset.mem_map_equiv, Equiv.prodComm_symm, Equiv.prodComm_apply,
      rowEdges, colEdges, Finset.mem_filter, hmem, edgeLength, transposeCosts,
      Function.comp_apply, Prod.fst_swap, Prod.snd_swap, Prod.swap_prod_mk]
  rw [← rowDegree_eq, h, card_map]

/-- A fixed cap makes the high original degrees on both sides arbitrarily
small per row, almost surely for all sufficiently large assignment sizes. -/
theorem ae_eventually_highDegrees_div_lt {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {d κ R ε : ℝ} (hd : 0 < d) (hκ : 0 < κ) (hR : 0 < R)
    (hμ : SmallCostTail μ κ d) (hε : 0 < ε) :
    ∃ D : ℕ, ∀ᵐ C ∂iidCosts μ, ∀ᶠ n in atTop,
      let S := retainedEdges d κ R n C
      (((∑ i, if D < (rowEdges S i).card then (rowEdges S i).card else 0) +
        (∑ j, if D < (colEdges S j).card then (colEdges S j).card else 0) : ℕ) : ℝ) /
        (n : ℝ) < ε := by
  obtain ⟨D,hD⟩ := ae_eventually_excessDegree_lt_linear hd hκ hR hμ (half_pos hε)
  refine ⟨D, ?_⟩
  filter_upwards [hD costRows (measurePreserving_costRows μ),
    hD (fun n => costRows n ∘ transposeCosts)
      (fun n => (measurePreserving_costRows μ n).comp (measurePreserving_transposeCosts μ))]
    with C hr hc
  filter_upwards [hr, hc, eventually_gt_atTop (0 : ℕ)] with n hrn hcn hn
  dsimp only
  rw [div_lt_iff₀ (Nat.cast_pos.mpr hn)]
  simp only [Nat.cast_add, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, ← Nat.cast_lt (α := ℝ),
    rowDegree_eq, colDegree_eq]
  change (∑ i : Fin n, excessDegree d κ R D (costRows n C i)) +
    (∑ j : Fin n, excessDegree d κ R D (costRows n (transposeCosts C) j)) < ε * (n : ℝ)
  change (∑ j : Fin n, excessDegree d κ R D (costRows n (transposeCosts C) j)) <
    (ε / 2) * (n : ℝ) at hcn
  linarith

/-- At a fixed length cutoff, the proportion of edges lost to degree trimming
is eventually arbitrarily small for all sufficiently large deterministic caps. -/
theorem ae_eventually_trimDegree_discarded_div_lt_forall_ge
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {d κ R ε : ℝ}
    (hd : 0 < d) (hκ : 0 < κ) (hR : 0 < R) (hμ : SmallCostTail μ κ d) (hε : 0 < ε) :
    ∃ D₀ : ℕ, ∀ᵐ C ∂iidCosts μ, ∀ᶠ n in atTop, ∀ D ≥ D₀,
      let S := retainedEdges d κ R n C
      ((S \ trimDegrees D S).card : ℝ) / (n : ℝ) < ε := by
  obtain ⟨D₀,hD⟩ := ae_eventually_highDegrees_div_lt hd hκ hR hμ hε
  refine ⟨D₀, ?_⟩
  filter_upwards [hD] with C hC
  filter_upwards [hC] with n hn D hD
  let S := retainedEdges d κ R n C
  have hmono (k : ℕ) : (if D < k then k else 0) ≤ (if D₀ < k then k else 0) := by
    by_cases hk : D < k
    · simp [hk, hD.trans_lt hk]
    · simp [hk]
  have hb := (card_trimDegree_discarded_le D S).trans
    (add_le_add (Finset.sum_le_sum fun i _ => hmono ((rowEdges S i).card))
      (Finset.sum_le_sum fun i _ => hmono ((colEdges S i).card)))
  exact (div_le_div_of_nonneg_right (by exact_mod_cast hb) (Nat.cast_nonneg n)).trans_lt hn

/-- A sufficiently large fixed cap makes degree trimming lose an arbitrarily
small proportion of edges at any fixed positive length cutoff. -/
theorem ae_eventually_trimDegree_discarded_div_lt {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {d κ R ε : ℝ} (hd : 0 < d) (hκ : 0 < κ) (hR : 0 < R)
    (hμ : SmallCostTail μ κ d) (hε : 0 < ε) :
    ∃ D : ℕ, ∀ᵐ C ∂iidCosts μ, ∀ᶠ n in atTop,
      let S := retainedEdges d κ R n C
      ((S \ trimDegrees D S).card : ℝ) / (n : ℝ) < ε := by
  obtain ⟨D,hD⟩ := ae_eventually_trimDegree_discarded_div_lt_forall_ge hd hκ hR hμ hε
  exact ⟨D, hD.mono fun _ h => h.mono fun _ hn => hn D le_rfl⟩

/-- Removed edges consist of all long edges and the discarded short edges.
Each short edge contributes at most one when costs are nonnegative. -/
theorem trimmedAssignment_omittedWeight_le {β d κ R : ℝ} (hβ : 0 ≤ β) (hκ : 0 ≤ κ)
    (n D : ℕ) (C : CostArray) (hC : ∀ e, 0 ≤ C e) :
    let S := retainedEdges d κ R n C
    (∑ e ∈ Finset.univ \ trimDegrees D S, (assignmentGraph β d κ n C).weight e) ≤
      longAssignmentMass β d κ R n C + ((S \ trimDegrees D S).card : ℝ) := by
  let S := retainedEdges d κ R n C
  let w := (assignmentGraph β d κ n C).weight
  have hpart : Finset.univ \ trimDegrees D S = (Finset.univ \ S) ∪ (S \ trimDegrees D S) := by
    ext e
    have hsub := @trimDegrees_subset (Fin n) (Fin n) _ _ D S
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union]
    by_cases he : e ∈ S
    · simp [he]
    · have ht : e ∉ trimDegrees D S := fun ht => he (hsub ht)
      simp [he, ht]
  have hdis : Disjoint (Finset.univ \ S) (S \ trimDegrees D S) :=
    Finset.disjoint_left.mpr fun e he h => (Finset.mem_sdiff.mp he).2 (Finset.mem_sdiff.mp h).1
  have hlong : (∑ e ∈ Finset.univ \ S, w e) = longAssignmentMass β d κ R n C := by
    rw [← Finset.filter_notMem_eq_sdiff, Finset.sum_filter]
    unfold longAssignmentMass
    apply Finset.sum_congr rfl
    intro e _
    simp only [S, retainedEdges, Finset.mem_filter, Finset.mem_univ, true_and, not_le]
    rfl
  change (∑ e ∈ Finset.univ \ trimDegrees D S, w e) ≤ _
  rw [hpart, Finset.sum_union hdis, hlong, add_le_add_iff_left]
  have hw (e : Fin n × Fin n) : w e ≤ 1 := by
    change Real.exp (-β * (lengthScale d κ n * C (e.1.val,e.2.val))) ≤ 1
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hβ)
      (mul_nonneg (Real.rpow_nonneg (mul_nonneg hκ (Nat.cast_nonneg n)) _) (hC _))
  calc
    _ ≤ ∑ _ ∈ S \ trimDegrees D S, (1 : ℝ) := Finset.sum_le_sum fun e _ => hw e
    _ = _ := by simp [S]

/-- A sufficiently large length cutoff and then a sufficiently large degree
cap make the normalized omitted weight eventually small almost surely. -/
theorem ae_eventually_trimmedAssignment_omittedWeight_div_lt
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {β d κ ε : ℝ}
    (hβ : 0 < β) (hd : 0 < d) (hκ : 0 < κ) (hμ : SmallCostTail μ κ d) (hε : 0 < ε) :
    ∃ R₀ : ℕ, 0 < R₀ ∧ ∀ R : ℝ, (R₀ : ℝ) ≤ R → ∃ D₀ : ℕ,
      ∀ᵐ C ∂iidCosts μ, ∀ᶠ n in atTop, ∀ D ≥ D₀,
        let S := retainedEdges d κ R n C
        (∑ e ∈ Finset.univ \ trimDegrees D S, (assignmentGraph β d κ n C).weight e) /
          (n : ℝ) < ε := by
  obtain ⟨R₀,hR₀,hlong⟩ := ae_eventually_longAssignmentMass_div_lt hβ hd hκ hμ (half_pos hε)
  refine ⟨R₀,hR₀,fun R hR => ?_⟩
  have hRpos : 0 < R := (Nat.cast_pos.mpr hR₀).trans_le hR
  obtain ⟨D₀,hD⟩ :=
    ae_eventually_trimDegree_discarded_div_lt_forall_ge hd hκ hRpos hμ (half_pos hε)
  refine ⟨D₀, ?_⟩
  filter_upwards [hD, hlong, ae_cost_nonneg μ hμ.1] with C hD hL hC
  filter_upwards [hD, hL] with n hDn hLn D hD₀
  calc
    _ ≤ (longAssignmentMass β d κ R n C +
        ((retainedEdges d κ R n C \ trimDegrees D (retainedEdges d κ R n C)).card : ℝ)) /
          (n : ℝ) :=
      div_le_div_of_nonneg_right
        (trimmedAssignment_omittedWeight_le hβ.le hκ.le n D C hC) (Nat.cast_nonneg n)
    _ < ε := by
      rw [add_div]
      linarith [hLn R hR, hDn D hD₀]

end Certificate.Overlap

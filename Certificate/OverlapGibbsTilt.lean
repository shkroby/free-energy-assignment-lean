import Certificate.OverlapConcentration
import Certificate.SoftAssignment
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-! Finite Gibbs tilt, restoration of omitted edges, and Chernoff bounds. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Certificate

/-- The integral of a real observable in a fixed Gibbs assignment law is
the exact finite weighted sum divided by the permanent. -/
theorem integral_gibbsAssignment (β d κ : ℝ) (n : ℕ) (C : CostArray)
    (F : Equiv.Perm (Fin n) → ℝ) :
    (∫ σ, F σ ∂gibbsAssignment β d κ n C) =
      (∑ σ, gibbsAssignmentWeight β d κ n C σ * F σ) / assignmentPartition β d κ n C := by
  rw [gibbsAssignment, PMF.integral_eq_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro σ _
  rw [gibbsAssignmentPMF, PMF.ofFintype_apply,
    ENNReal.toReal_ofReal (div_nonneg (gibbsAssignmentWeight_nonneg β d κ n C σ)
      (assignmentPartition_pos β d κ n C).le), smul_eq_mul]
  ring

/-- The complete assignment graph with edge weights tilted by `exp (s f)`. -/
noncomputable def gibbsTiltedAssignmentGraph (β d κ s : ℝ) (n : ℕ) (C : CostArray)
    (f : Fin n × Fin n → ℝ) : WeightedGraph (Fin n ⊕ Fin n) (Fin n × Fin n) where
  __ := assignmentGraph β d κ n C
  weight e := (assignmentGraph β d κ n C).weight e * Real.exp (s * f e)
  weight_nonneg e := mul_nonneg ((assignmentGraph β d κ n C).weight_nonneg e) (Real.exp_nonneg _)

/-- The perfect-assignment partition with the same edge tilt. -/
noncomputable def tiltedAssignmentPartition (β d κ s : ℝ) (n : ℕ) (C : CostArray)
    (f : Fin n × Fin n → ℝ) : ℝ :=
  permanent (fun i j => (gibbsTiltedAssignmentGraph β d κ s n C f).weight (i,j))

theorem tiltedAssignmentPartition_pos (β d κ s : ℝ) (n : ℕ) (C : CostArray)
    (f : Fin n × Fin n → ℝ) : 0 < tiltedAssignmentPartition β d κ s n C f :=
  permanent_pos (fun _ _ => mul_pos (Real.exp_pos _) (Real.exp_pos _))

private theorem gibbsAssignmentWeight_eq_prod (β d κ : ℝ) (n : ℕ) (C : CostArray)
    (σ : Equiv.Perm (Fin n)) :
    gibbsAssignmentWeight β d κ n C σ =
      ∏ i, (assignmentGraph β d κ n C).weight (i, σ i) := by
  simp only [gibbsAssignmentWeight, assignmentGraph, edgeLength, mul_assoc, neg_mul]

/-- The centered statistic is the sum on the occupied edges minus the
deterministic center, in row notation. -/
theorem centeredAssignmentStatistic_eq_rowSum {n : ℕ}
    (f γ : Fin n × Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    centeredAssignmentStatistic f γ σ =
      (∑ i, f (i, σ i)) - ∑ e, f e * γ e := by
  unfold centeredAssignmentStatistic
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, Fintype.sum_prod_type]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp [assignmentEdgeIndicator, mul_ite, eq_comm]

/-- The centered moment generating function is the ratio of the tilted
and untilted permanents, with the deterministic center removed. -/
theorem mgf_centeredAssignmentStatistic (β d κ s : ℝ) (n : ℕ) (C : CostArray)
    (f γ : Fin n × Fin n → ℝ) :
    mgf (centeredAssignmentStatistic f γ) (gibbsAssignment β d κ n C) s =
      Real.exp (-s * (∑ e, f e * γ e)) *
        tiltedAssignmentPartition β d κ s n C f / assignmentPartition β d κ n C := by
  let center := ∑ e, f e * γ e
  unfold mgf
  rw [integral_gibbsAssignment, tiltedAssignmentPartition, permanent, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  have hw : (∏ i, (gibbsTiltedAssignmentGraph β d κ s n C f).weight (i, σ i)) =
      gibbsAssignmentWeight β d κ n C σ * Real.exp (s * (∑ i, f (i, σ i))) := by
    rw [gibbsAssignmentWeight_eq_prod, Finset.mul_sum, Real.exp_sum, ← Finset.prod_mul_distrib]
    rfl
  rw [hw, centeredAssignmentStatistic_eq_rowSum, mul_sub, Real.exp_sub, neg_mul, Real.exp_neg]
  ring

/-- Exact finite-volume log-moment-generating-function identity. -/
theorem cgf_centeredAssignmentStatistic (β d κ s : ℝ) (n : ℕ) (C : CostArray)
    (f γ : Fin n × Fin n → ℝ) :
    cgf (centeredAssignmentStatistic f γ) (gibbsAssignment β d κ n C) s =
      Real.log (tiltedAssignmentPartition β d κ s n C f) -
        Real.log (assignmentPartition β d κ n C) - s * (∑ e, f e * γ e) := by
  unfold cgf
  rw [mgf_centeredAssignmentStatistic,
    Real.log_div (mul_pos (Real.exp_pos _) (tiltedAssignmentPartition_pos β d κ s n C f)).ne'
      (assignmentPartition_pos β d κ n C).ne',
    Real.log_mul (Real.exp_pos _).ne' (tiltedAssignmentPartition_pos β d κ s n C f).ne',
    Real.log_exp]
  ring

namespace Tree.Bipartite

/-- A completed permutation matching contributes with coefficient one to the
soft partition. All remaining contributions are nonnegative. -/
theorem permanent_le_monomerPartition {n : ℕ} (w : Fin n × Fin n → ℝ)
    (hw : ∀ e, 0 ≤ w e) {z : ℝ} (hz : 0 ≤ z) :
    permanent (fun i j => w (i,j)) ≤ monomerPartition (ends (n := n)) Finset.univ Finset.univ w z := by
  classical
  let emb (σ : Equiv.Perm (Fin n)) : Fin n ↪ Fin n × Fin n :=
    ⟨fun i => (i, σ i), fun _ _ h => congrArg Prod.fst h⟩
  let E (σ : Equiv.Perm (Fin n)) := (Finset.univ : Finset (Fin n)).map (emb σ)
  have heq (σ : Equiv.Perm (Fin n)) : E σ = edgesOf (fun i => some (σ i)) := by
    ext ⟨i,j⟩
    simp only [E, Finset.mem_map, Finset.mem_univ, true_and, mem_edgesOf, Option.some.injEq]
    change (∃ a, (a, σ a) = (i, j)) ↔ σ i = j
    constructor
    · rintro ⟨a, ha⟩
      have hai : a = i := congrArg Prod.fst ha
      subst a
      exact congrArg Prod.snd ha
    · intro hij
      exact ⟨i, Prod.ext rfl hij⟩
  have hinj : Function.Injective E := by
    intro σ τ h
    apply Equiv.ext
    intro i
    have he := edgesOf_injective ((heq σ).symm.trans (h.trans (heq τ)))
    exact Option.some.inj (congrFun he i)
  have hmatching (σ : Equiv.Perm (Fin n)) : E σ ∈ matchings ends Finset.univ Finset.univ := by
    rw [heq σ, edgesOf_valid_iff]
    intro i j c hi hj
    exact σ.injective ((Option.some.inj hi).trans (Option.some.inj hj).symm)
  let a (M : Finset (Fin n × Fin n)) :=
    z ^ ((Finset.univ : Finset (Fin n ⊕ Fin n)).card - 2 * M.card) * ∏ e ∈ M, w e
  have ha (σ : Equiv.Perm (Fin n)) : a (E σ) = ∏ i, w (i, σ i) := by
    have hv : (Finset.univ : Finset (Fin n ⊕ Fin n)).card = 2 * n := by simp; omega
    have hm : (E σ).card = n := by simp [E]
    simp only [a, hv, hm, Nat.sub_self, pow_zero, one_mul, E, Finset.prod_map]
    rfl
  unfold permanent monomerPartition
  calc
    _ = ∑ σ, a (E σ) := Finset.sum_congr rfl (fun σ _ => (ha σ).symm)
    _ = ∑ M ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))).image E, a M :=
      (Finset.sum_image hinj.injOn).symm
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro M hM
        obtain ⟨σ, _, rfl⟩ := Finset.mem_image.mp hM
        exact hmatching σ
      · intro M _ _
        exact mul_nonneg (pow_nonneg hz _) (Finset.prod_nonneg fun e _ => hw e)

end Tree.Bipartite

/-- Passing from perfect assignments to the soft partition and restoring
omitted edges transfers a retained-graph tilt bound to the hard Gibbs law. -/
theorem cgf_centeredAssignmentStatistic_div_le_of_retained_tilt
    (β d κ s u : ℝ) {n : ℕ} (hn : 0 < n) (C : CostArray)
    (kept : Finset (Fin n × Fin n)) (f γ : Fin n × Fin n → ℝ)
    (hf : ∀ e, |f e| ≤ 1) (remainder : ℝ)
    (hTilt :
      Real.log (((gibbsTiltedAssignmentGraph β d κ s n C f).retain kept
        (Finset.subset_univ _)).Z u) ≤
      Real.log (((assignmentGraph β d κ n C).retain kept (Finset.subset_univ _)).Z u) +
        s * (∑ e, f e * γ e) + remainder) :
    cgf (centeredAssignmentStatistic f γ) (gibbsAssignment β d κ n C) s / (n : ℝ) ≤
      softAssignmentPressure β d κ u n C - pressure β d κ n C +
        ((∑ e ∈ Finset.univ \ kept, (assignmentGraph β d κ n C).weight e) / (n : ℝ)) *
          Real.exp (|s| - 2*u) + remainder / (n : ℝ) := by
  let G := assignmentGraph β d κ n C
  let Gt := gibbsTiltedAssignmentGraph β d κ s n C f
  let W := ∑ e ∈ Finset.univ \ kept, G.weight e
  have hP : Real.log (tiltedAssignmentPartition β d κ s n C f) ≤ Real.log (Gt.Z u) :=
    Real.log_le_log (tiltedAssignmentPartition_pos β d κ s n C f)
      (Tree.Bipartite.permanent_le_monomerPartition Gt.weight Gt.weight_nonneg
        (Real.exp_nonneg u))
  have hUntil : Real.log ((G.retain kept (Finset.subset_univ _)).Z u) ≤ Real.log (G.Z u) :=
    sub_nonneg.mp (G.logZ_sub_logZ_retain_le kept (Finset.subset_univ _) u).1
  have hsum : (∑ e ∈ Finset.univ \ kept, Gt.weight e) ≤ W * Real.exp |s| := by
    rw [show W = ∑ e ∈ Finset.univ \ kept, G.weight e from rfl, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro e _
    change G.weight e * Real.exp (s * f e) ≤ G.weight e * Real.exp |s|
    apply mul_le_mul_of_nonneg_left _ (G.weight_nonneg e)
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ |s * f e| := le_abs_self _
      _ = |s| * |f e| := abs_mul _ _
      _ ≤ |s| := mul_le_of_le_one_right (abs_nonneg s) (hf e)
  have hRestore : Real.log (Gt.Z u) -
      Real.log ((Gt.retain kept (Finset.subset_univ _)).Z u) ≤ W * Real.exp (|s| - 2*u) := by
    calc
      _ ≤ (∑ e ∈ Finset.univ \ kept, Gt.weight e) * Real.exp (-2*u) :=
        (Gt.logZ_sub_logZ_retain_le kept (Finset.subset_univ _) u).2
      _ ≤ (W * Real.exp |s|) * Real.exp (-2*u) :=
        mul_le_mul_of_nonneg_right hsum (Real.exp_nonneg _)
      _ = _ := by rw [mul_assoc, ← Real.exp_add, sub_eq_add_neg, neg_mul]
  have hcgf : cgf (centeredAssignmentStatistic f γ) (gibbsAssignment β d κ n C) s ≤
      Real.log (G.Z u) - Real.log (assignmentPartition β d κ n C) +
        W * Real.exp (|s| - 2*u) + remainder := by
    change Real.log ((Gt.retain kept (Finset.subset_univ _)).Z u) ≤
      Real.log ((G.retain kept (Finset.subset_univ _)).Z u) +
        s * (∑ e, f e * γ e) + remainder at hTilt
    rw [cgf_centeredAssignmentStatistic]
    linarith only [hP, hUntil, hRestore, hTilt]
  calc
    _ ≤ (Real.log (G.Z u) - Real.log (assignmentPartition β d κ n C) +
        W * Real.exp (|s| - 2*u) + remainder) / (n : ℝ) :=
      div_le_div_of_nonneg_right hcgf (Nat.cast_pos.mpr hn).le
    _ = _ := by
      change (Real.log (G.Z u) - Real.log (assignmentPartition β d κ n C) +
        W * Real.exp (|s| - 2*u) + remainder) / (n : ℝ) =
        Real.log (G.Z u) / (n : ℝ) - Real.log (assignmentPartition β d κ n C) / (n : ℝ) +
        W / (n : ℝ) * Real.exp (|s| - 2*u) + remainder / (n : ℝ)
      ring

/-- Chernoff at the two tilt signs yields the uniform edge-statistic tail
with the precise factor two. -/
theorem gibbsAssignment_edgeStatistic_tail_of_cgf {β d κ δ c s : ℝ}
    {n : ℕ} (hn : 0 < n) (hs : 0 < s) (C : CostArray) (f γ : Fin n × Fin n → ℝ)
    (hplus : cgf (centeredAssignmentStatistic f γ) (gibbsAssignment β d κ n C) s / (n : ℝ) ≤
      s*δ-c)
    (hminus : cgf (centeredAssignmentStatistic f γ) (gibbsAssignment β d κ n C) (-s) / (n : ℝ) ≤
      s*δ-c) :
    gibbsAssignment β d κ n C
        {σ | (n : ℝ)*δ < |centeredAssignmentStatistic f γ σ|} ≤
      ENNReal.ofReal (2 * Real.exp (-c * (n : ℝ))) := by
  let P := gibbsAssignment β d κ n C
  let X := centeredAssignmentStatistic f γ
  let a := (n : ℝ)*δ
  let E₁ : Set (Equiv.Perm (Fin n)) := {σ | a ≤ X σ}
  let E₂ : Set (Equiv.Perm (Fin n)) := {σ | X σ ≤ -a}
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have h₁ : P E₁ ≤ ENNReal.ofReal (Real.exp (-c * (n : ℝ))) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top P E₁)]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ Real.exp (-s*a + cgf X P s) := measure_ge_le_exp_cgf a hs.le Integrable.of_finite
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have h := (div_le_iff₀ hn').mp hplus
        change cgf X P s ≤ (s*δ-c)*(n : ℝ) at h
        dsimp only [a]
        nlinarith only [h]
  have h₂ : P E₂ ≤ ENNReal.ofReal (Real.exp (-c * (n : ℝ))) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top P E₂)]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ Real.exp (-(-s)*(-a) + cgf X P (-s)) :=
        measure_le_le_exp_cgf (-a) (neg_nonpos.mpr hs.le) Integrable.of_finite
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have h := (div_le_iff₀ hn').mp hminus
        change cgf X P (-s) ≤ (s*δ-c)*(n : ℝ) at h
        dsimp only [a]
        nlinarith only [h]
  have hsub : {σ | a < |X σ|} ⊆ E₁ ∪ E₂ := by
    intro σ hσ
    change a < |X σ| at hσ
    by_cases hX : 0 ≤ X σ
    · rw [abs_of_nonneg hX] at hσ
      exact Or.inl hσ.le
    · rw [abs_of_nonpos (le_of_not_ge hX)] at hσ
      exact Or.inr ((lt_neg.mp hσ).le)
  change P {σ | a < |X σ|} ≤ _
  calc
    _ ≤ P (E₁ ∪ E₂) := measure_mono hsub
    _ ≤ P E₁ + P E₂ := measure_union_le _ _
    _ ≤ _ := (add_le_add h₁ h₂).trans_eq (by
      rw [← ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _), ← two_mul])

/-- A tilt can be chosen so the quadratic penalty uses only one eighth of
the Chernoff margin. The same step applies at either sign. -/
theorem exists_overlap_chernoff_step {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 1 ∧ 16*s^2/η ≤ s*δ/8 := by
  let s := min 1 (η*δ/128)
  have hs : 0 < s := lt_min zero_lt_one (by positivity)
  refine ⟨s, hs, min_le_left _ _, ?_⟩
  have h := (le_div_iff₀ (by norm_num : (0:ℝ) < 128)).mp (min_le_right 1 (η*δ/128))
  apply (div_le_iff₀ hη).mpr
  nlinarith only [mul_le_mul_of_nonneg_left h hs.le]

/-- The paper's quadratic, exceptional-row, and remaining error budgets
sum to half the Chernoff exponent. -/
theorem overlap_cgf_margin_of_error_budgets {η δ s bad rest : ℝ}
    (hs : 0 ≤ s) (hquad : 16*s^2/η ≤ s*δ/8) (hbad : bad ≤ δ/16)
    (hrest : rest ≤ s*δ/4) :
    rest + 16*s^2/η + 2*s*bad ≤ s*δ - s*δ/2 := by
  have h := mul_le_mul_of_nonneg_left hbad (show 0 ≤ 2*s by positivity)
  linarith only [hquad,hrest,h]

/-- A retained-graph tilt estimate at both signs, together with its
normalized pressure and error budget, yields the edge-statistic bound at
the actual matrix size. -/
theorem edgeStatisticBoundAt_of_retained_tilt
    {β d κ Q δ c s u : ℝ} {n : ℕ} (hn : 0 < n) (hs : 0 < s) (hs₁ : s ≤ 1)
    (C : CostArray) (kept : Finset (Fin n × Fin n)) (γ : Fin n × Fin n → ℝ) (error : ℝ)
    (hBias : |(∑ e, (γ e)^2) / (n : ℝ) - Q| < δ)
    (hTilt : ∀ f : Fin n × Fin n → ℝ, (∀ e, |f e| ≤ 1) → ∀ t : ℝ, |t| = s →
      Real.log (((gibbsTiltedAssignmentGraph β d κ t n C f).retain kept
        (Finset.subset_univ _)).Z u) ≤
      Real.log (((assignmentGraph β d κ n C).retain kept (Finset.subset_univ _)).Z u) +
        t * (∑ e, f e * γ e) + (n : ℝ) * error)
    (hBudget :
      softAssignmentPressure β d κ u n C - pressure β d κ n C +
        ((∑ e ∈ Finset.univ \ kept, (assignmentGraph β d κ n C).weight e) / (n : ℝ)) *
          Real.exp (1 - 2*u) + error ≤ s*δ-c) :
    EdgeStatisticBoundAt β d κ Q δ c γ C := by
  refine ⟨hBias, fun f hf => ?_⟩
  let gap := softAssignmentPressure β d κ u n C - pressure β d κ n C
  let W := (∑ e ∈ Finset.univ \ kept, (assignmentGraph β d κ n C).weight e) / (n : ℝ)
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hW : 0 ≤ W := div_nonneg (Finset.sum_nonneg fun e _ =>
    (assignmentGraph β d κ n C).weight_nonneg e) hn'.le
  have hcgf (t : ℝ) (ht : |t| = s) :
      cgf (centeredAssignmentStatistic f γ) (gibbsAssignment β d κ n C) t / (n : ℝ) ≤ s*δ-c := by
    calc
      _ ≤ gap + W * Real.exp (|t| - 2*u) + (n : ℝ) * error / (n : ℝ) :=
        cgf_centeredAssignmentStatistic_div_le_of_retained_tilt β d κ t u hn C kept f γ hf
          ((n : ℝ) * error) (hTilt f hf t ht)
      _ = gap + W * Real.exp (s - 2*u) + error := by
        rw [ht, mul_div_cancel_left₀ _ hn'.ne']
      _ ≤ gap + W * Real.exp (1 - 2*u) + error :=
        add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (sub_le_sub_right hs₁ _)) hW)) le_rfl
      _ ≤ _ := hBudget
  exact gibbsAssignment_edgeStatistic_tail_of_cgf hn hs C f γ
    (hcgf s (abs_of_pos hs)) (hcgf (-s) (by rw [abs_neg, abs_of_pos hs]))

end Certificate

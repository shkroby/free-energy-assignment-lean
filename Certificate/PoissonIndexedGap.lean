import Certificate.Model
import Certificate.PoissonFull
import Certificate.PoissonGap
import Mathlib.Probability.Independence.InfinitePi

/-!
# Deleting a coordinate of an iid sequence

Dropping one coordinate leaves an iid sequence independent of that coordinate.
For exponential spacings, deleting one arrival merges its adjacent gaps. The
law of the deleted gap together with the remaining sequence follows from
the two-gap density.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators

namespace Certificate

private def skipIndex (i j : ℕ) : ℕ := if j < i then j else j+1

private theorem skipIndex_ne (i j : ℕ) : skipIndex i j ≠ i := by
  unfold skipIndex
  split_ifs <;> omega

private theorem skipIndex_injective (i : ℕ) : Function.Injective (skipIndex i) := by
  intro x y h
  unfold skipIndex at h
  split_ifs at h <;> omega

/-- Drop index `i` and shift the subsequent coordinates down by one. -/
def eraseSequence {Y : Type*} (i : ℕ) (ω : ℕ → Y) : ℕ → Y :=
  fun j => ω (skipIndex i j)

@[fun_prop] theorem measurable_eraseSequence {Y : Type*} [MeasurableSpace Y] (i : ℕ) :
    Measurable (eraseSequence i : (ℕ → Y) → (ℕ → Y)) :=
  measurable_pi_lambda _ (fun j => measurable_pi_apply (skipIndex i j))

theorem eraseSequence_apply_of_lt {Y : Type*} (ω : ℕ → Y) {i j : ℕ} (h : j < i) :
    eraseSequence i ω j = ω j := by
  simp [eraseSequence, skipIndex, h]

theorem eraseSequence_apply_of_ge {Y : Type*} (ω : ℕ → Y) {i j : ℕ} (h : i ≤ j) :
    eraseSequence i ω j = ω (j+1) := by
  simp [eraseSequence, skipIndex, not_lt.mpr h]

/-- In a nonnegative sum, restoring a skipped term recovers the full sum. -/
theorem tsum_nat_skip_add {f g : ℕ → ℝ≥0∞} (i : ℕ)
    (h : ∀ j, g j = if j < i then f j else f (j+1)) :
    (∑' j, g j) + f i = ∑' j, f j := by
  classical
  let S : Set ℕ := {j | j ≠ i}
  let e (j : ℕ) : S := ⟨skipIndex i j, skipIndex_ne i j⟩
  have hi : Function.Injective e := fun _ _ hh =>
    skipIndex_injective i (congrArg Subtype.val hh)
  have hs : Function.Surjective e := by
    intro z
    have hz : (z : ℕ) ≠ i := z.2
    rcases lt_or_gt_of_ne hz with h | h
    · exact ⟨z, Subtype.ext (by simp [e, skipIndex, h])⟩
    · refine ⟨(z : ℕ)-1, Subtype.ext ?_⟩
      have hge : i ≤ (z : ℕ)-1 := by omega
      simp only [e, skipIndex, if_neg (not_lt.mpr hge)]
      omega
  let u : ℕ ≃ S := Equiv.ofBijective e ⟨hi,hs⟩
  have hsum : (∑' j, g j) = ∑' j : S, f j.1 := by
    calc
      _ = ∑' j, f (u j).1 := tsum_congr (fun j => by
        change g j = f (skipIndex i j)
        rw [h, skipIndex]
        split_ifs <;> rfl)
      _ = _ := u.tsum_eq (fun j => f j.1)
  have hsub : (∑' j : S, f j.1) = ∑' j, if j = i then 0 else f j := by
    rw [tsum_subtype S f]
    apply tsum_congr
    intro j
    by_cases hh : j = i <;> simp [S, hh]
  rw [hsum, hsub, add_comm]
  have hc : (∑' j, if j = i then (0 : ℝ≥0∞) else f j) =
      ∑' j, @ite ℝ≥0∞ (j = i) (Classical.propDecidable _) 0 (f j) := by
    apply tsum_congr
    intro j
    by_cases hj : j = i <;> simp [hj]
  exact (congrArg (fun x => f i + x) hc).trans
    (ENNReal.tsum_eq_add_tsum_ite (f := f) i).symm

private theorem eraseSequence_update {Y : Type*} (i : ℕ) (ω : ℕ → Y) (y : Y) :
    eraseSequence i (Function.update ω i y) = eraseSequence i ω := by
  funext j
  exact Function.update_of_ne (skipIndex_ne i j) _ _

/-- The deleted coordinate is independent of the whole sequence of remaining
coordinates. -/
theorem iid_eraseSequence_lintegral {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)
    [IsProbabilityMeasure μ] (i : ℕ) (f : Y × (ℕ → Y) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, f (ω i, eraseSequence i ω) ∂Measure.infinitePi (fun _ : ℕ => μ)) =
      ∫⁻ z, f z ∂μ.prod (Measure.infinitePi (fun _ : ℕ => μ)) := by
  let P := Measure.infinitePi (fun _ : ℕ => μ)
  let F := fun ω : ℕ → Y => f (ω i, eraseSequence i ω)
  have hF : Measurable F := hf.comp ((measurable_pi_apply i).prodMk (measurable_eraseSequence i))
  have href := infinitePi_refresh (fun _ : ℕ => μ) i
  have herase : MeasurePreserving (eraseSequence i) P P :=
    ⟨measurable_eraseSequence i,
      Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ => μ) (skipIndex_injective i)⟩
  have hM : Measurable (fun p : (ℕ → Y) × Y => f (p.2, eraseSequence i p.1)) :=
    hf.comp (measurable_snd.prodMk ((measurable_eraseSequence i).comp measurable_fst))
  change (∫⁻ ω, F ω ∂P) = _
  calc
    _ = ∫⁻ p, F (Function.update p.1 i p.2) ∂P.prod μ := (href.lintegral_comp hF).symm
    _ = ∫⁻ p, f (p.2, eraseSequence i p.1) ∂P.prod μ := by
      apply lintegral_congr
      intro p
      simp only [F, eraseSequence_update, Function.update_self]
    _ = ∫⁻ x, ∫⁻ ω, f (x,eraseSequence i ω) ∂P ∂μ := lintegral_prod_symm' _ hM
    _ = ∫⁻ x, ∫⁻ ω, f (x,ω) ∂P ∂μ :=
      lintegral_congr (fun x => herase.lintegral_comp
        (hf.comp (measurable_const.prodMk measurable_id)))
    _ = ∫⁻ p, f p ∂μ.prod P := (lintegral_prod _ hf.aemeasurable).symm

/-- Merge gaps `i` and `i+1`, shifting down the gaps after them. This removes
the arrival after gap `i`. -/
def eraseArrivalGap (i : ℕ) (ω : ℕ → ℝ) : ℕ → ℝ :=
  Function.update (eraseSequence (i+1) ω) i (ω i + ω (i+1))

@[fun_prop] theorem measurable_eraseArrivalGap (i : ℕ) :
    Measurable (eraseArrivalGap i) := by
  apply measurable_pi_lambda
  intro j
  by_cases h : j = i
  · subst j
    simp only [eraseArrivalGap, Function.update_self]
    fun_prop
  · simpa only [eraseArrivalGap, Function.update_of_ne h, Function.comp_def] using
      (measurable_pi_apply j).comp (measurable_eraseSequence (Y := ℝ) (i+1))

/-- The gap-splitting identity on the entire iid spacing sequence. The test may
depend measurably on every retained gap. -/
theorem exp_indexed_gap_split_lintegral (i : ℕ)
    (g : ℝ × (ℕ → ℝ) → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ ω, g (ω i, eraseArrivalGap i ω) ∂exponentialSpacings) =
      ∫⁻ ω, (∫⁻ a in Ioo 0 (ω i), g (a,ω)) ∂exponentialSpacings := by
  let E := expMeasure 1
  let P := exponentialSpacings
  let : IsProbabilityMeasure E := isProbabilityMeasure_expMeasure zero_lt_one
  let : IsProbabilityMeasure P := isProbabilityMeasure_exponentialSpacings
  have href : MeasurePreserving
      (fun p : (ℕ → ℝ) × ℝ => Function.update p.1 i p.2) (P.prod E) P :=
    infinitePi_refresh (fun _ : ℕ => E) i
  let F := fun p : ℝ × (ℕ → ℝ) => g (p.2 i, Function.update p.2 i (p.2 i+p.1))
  let K := fun (r : ℕ → ℝ) (p : ℝ × ℝ) => g (p.1, Function.update r i (p.1+p.2))
  let K' := fun (r : ℕ → ℝ) (p : ℝ × ℝ) => g (p.1, Function.update r i p.2)
  have hev : Measurable (fun p : ℝ × (ℕ → ℝ) => p.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  have hF : Measurable F := hg.comp (hev.prodMk
    (href.measurable.comp (measurable_snd.prodMk (hev.add measurable_fst))))
  have hK (r : ℕ → ℝ) : Measurable (K r) := hg.comp
    (measurable_fst.prodMk (href.measurable.comp (measurable_const.prodMk
      (measurable_fst.add measurable_snd))))
  have hK' (r : ℕ → ℝ) : Measurable (K' r) := hg.comp
    (measurable_fst.prodMk (href.measurable.comp (measurable_const.prodMk measurable_snd)))
  have hsplit (b : ℝ) :
      (∫⁻ r, F (b,r) ∂P) = ∫⁻ r, ∫⁻ a, K r (a,b) ∂E ∂P := by
    let L := fun r : ℕ → ℝ => F (b,r)
    have hL : Measurable L := hF.comp (measurable_const.prodMk measurable_id)
    have hLc : Measurable (fun p : (ℕ → ℝ) × ℝ => L (Function.update p.1 i p.2)) :=
      hL.comp href.measurable
    calc
      _ = ∫⁻ p, L (Function.update p.1 i p.2) ∂P.prod E := (href.lintegral_comp hL).symm
      _ = ∫⁻ r, ∫⁻ a, L (Function.update r i a) ∂E ∂P := lintegral_prod _ hLc.aemeasurable
      _ = _ := by
        apply lintegral_congr
        intro r
        apply lintegral_congr
        intro a
        simp only [L, F, K, Function.update_self, Function.update_idem]
  have hJoint : Measurable (fun p : (ℝ × (ℕ → ℝ)) × ℝ => K p.1.2 (p.2,p.1.1)) :=
    hg.comp (measurable_snd.prodMk (href.measurable.comp
      ((measurable_snd.comp measurable_fst).prodMk
        (measurable_snd.add (measurable_fst.comp measurable_fst)))))
  have hInner : Measurable (fun p : ℝ × (ℕ → ℝ) => ∫⁻ a, K p.2 (a,p.1) ∂E) :=
    hJoint.lintegral_prod_right' (ν := E)
  let H := fun ω : ℕ → ℝ => ∫⁻ a in Ioo 0 (ω i), g (a,ω)
  have hH : Measurable H := by
    let S : Set ((ℕ → ℝ) × ℝ) := {p | 0 < p.2 ∧ p.2 < p.1 i}
    have hS : MeasurableSet S := (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd ((measurable_pi_apply i).comp measurable_fst))
    have hs : Measurable (S.indicator (fun p => g (p.2,p.1))) :=
      (hg.comp measurable_swap).indicator hS
    have hex : H = fun ω => ∫⁻ a, S.indicator (fun p => g (p.2,p.1)) (ω,a) := by
      funext ω
      exact (lintegral_indicator measurableSet_Ioo (fun a => g (a,ω))).symm
    rw [hex]
    exact hs.lintegral_prod_right'
  change (∫⁻ ω, g (ω i, eraseArrivalGap i ω) ∂P) = ∫⁻ ω, H ω ∂P
  calc
    _ = ∫⁻ ω, F (ω (i+1), eraseSequence (i+1) ω) ∂P := by
      apply lintegral_congr
      intro ω
      simp only [F, eraseArrivalGap, eraseSequence, skipIndex, if_pos (Nat.lt_succ_self i)]
    _ = ∫⁻ p, F p ∂E.prod P := iid_eraseSequence_lintegral E (i+1) F hF
    _ = ∫⁻ b, ∫⁻ r, F (b,r) ∂P ∂E := lintegral_prod _ hF.aemeasurable
    _ = ∫⁻ b, ∫⁻ r, ∫⁻ a, K r (a,b) ∂E ∂P ∂E := lintegral_congr hsplit
    _ = ∫⁻ r, ∫⁻ b, ∫⁻ a, K r (a,b) ∂E ∂E ∂P := lintegral_lintegral_swap hInner.aemeasurable
    _ = ∫⁻ r, ∫⁻ p, K r p ∂E.prod E ∂P :=
      lintegral_congr (fun r => (lintegral_prod_symm' _ (hK r)).symm)
    _ = ∫⁻ r, ∫⁻ s, (∫⁻ a in Ioo 0 s, K' r (a,s)) ∂E ∂P :=
      lintegral_congr (fun r => exp_gap_split_lintegral (K' r) (hK' r))
    _ = ∫⁻ r, ∫⁻ s, H (Function.update r i s) ∂E ∂P := by
      apply lintegral_congr
      intro r
      apply lintegral_congr
      intro s
      simp only [H, K', Function.update_self]
    _ = ∫⁻ p, H (Function.update p.1 i p.2) ∂P.prod E := by
      have hm : Measurable (fun p : (ℕ → ℝ) × ℝ => H (Function.update p.1 i p.2)) :=
        hH.comp href.measurable
      exact (lintegral_prod _ hm.aemeasurable).symm
    _ = ∫⁻ ω, H ω ∂P := href.lintegral_comp hH

end Certificate

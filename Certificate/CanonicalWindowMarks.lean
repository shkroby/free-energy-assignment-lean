import Certificate.PoissonArrivalCount
import Mathlib.GroupTheory.Perm.Fin

/-! The count-conditional marked law of the canonical finite Poisson window. -/

open Finset Filter MeasureTheory Set
open scoped ENNReal

namespace Certificate

variable {Y : Type*} [MeasurableSpace Y]

private abbrev Configuration (Y : Type*) := (ℕ → ℝ) × (ℕ → Y)

def arrivalWindow (R : ℝ) : Set (ℝ × Y) := Set.Ioc 0 R ×ˢ Set.univ

def arrivalWindowCountEvent (d R : ℝ) (n : ℕ) : Set (Configuration Y) :=
  {ω | markedArrivalCount d (arrivalWindow R) ω = (n : ℝ≥0∞)}

noncomputable def firstMarkedArrivals (d : ℝ) (n : ℕ) (ω : Configuration Y) : Fin n → ℝ × Y :=
  fun i => markedArrivalPoint d i ω

noncomputable def conditionalWindowMarkLaw (d R : ℝ) (μ : Measure Y) : Measure (ℝ × Y) :=
  let T := (intensity d).prod μ
  (T (arrivalWindow R))⁻¹ • T.restrict (arrivalWindow R)

private theorem measurableSet_arrivalWindow (R : ℝ) :
    MeasurableSet (arrivalWindow (Y := Y) R) := measurableSet_Ioc.prod MeasurableSet.univ

private theorem measurableSet_arrivalWindowCountEvent (d R : ℝ) (n : ℕ) :
    MeasurableSet (arrivalWindowCountEvent (Y := Y) d R n) :=
  measurable_markedArrivalCount d (measurableSet_arrivalWindow R) (measurableSet_singleton _)

private theorem measurable_markedPoint (d : ℝ) (i : ℕ) :
    Measurable (markedArrivalPoint (Y := Y) d i) := by
  unfold markedArrivalPoint arrivalLength
  fun_prop

private theorem measurable_firstMarkedArrivals (d : ℝ) (n : ℕ) :
    Measurable (firstMarkedArrivals (Y := Y) d n) :=
  measurable_pi_iff.mpr (fun i => measurable_markedPoint d i)

private theorem measurable_cons {n : ℕ} :
    Measurable (fun p : (ℝ × Y) × (Fin n → ℝ × Y) => (Fin.cons p.1 p.2 : Fin (n+1) → ℝ × Y)) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ × Y) 0
  convert e.symm.measurable using 1
  funext p
  simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero']

omit [MeasurableSpace Y] in
private theorem markedPoint_erase (d : ℝ) (ω : Configuration Y) (i j : ℕ) :
    markedArrivalPoint d j (eraseArrivalGap i ω.1, eraseSequence i ω.2) =
      if j < i then markedArrivalPoint d j ω else markedArrivalPoint d (j+1) ω := by
  unfold markedArrivalPoint
  dsimp
  rw [arrivalLength_eraseGap]
  by_cases h : j < i
  · rw [if_pos h, if_pos h, eraseSequence_apply_of_lt ω.2 h]
  · rw [if_neg h, if_neg h, eraseSequence_apply_of_ge ω.2 (le_of_not_gt h)]

omit [MeasurableSpace Y] in
private theorem firstMarkedArrivals_erase (d : ℝ) (ω : Configuration Y) {n : ℕ} (i : Fin (n+1)) :
    firstMarkedArrivals d n (eraseArrivalGap i ω.1, eraseSequence i ω.2) =
      i.removeNth (firstMarkedArrivals d (n+1) ω) := by
  funext j
  unfold firstMarkedArrivals
  rw [Fin.removeNth_apply, markedPoint_erase]
  by_cases h : (j : ℕ) < (i : ℕ)
  · rw [if_pos h, Fin.succAbove_of_castSucc_lt _ _ h]
    rfl
  · rw [if_neg h, Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt h)]
    rfl

omit [MeasurableSpace Y] in
private theorem arrivalWindowCount_erase_add (d R : ℝ) (ω : Configuration Y) (i : ℕ) :
    markedArrivalCount d (arrivalWindow R) (eraseArrivalGap i ω.1, eraseSequence i ω.2) +
      (arrivalWindow R).indicator (fun _ => (1 : ℝ≥0∞)) (markedArrivalPoint d i ω) =
        markedArrivalCount d (arrivalWindow R) ω := by
  unfold markedArrivalCount
  apply tsum_nat_skip_add i
  intro j
  rw [markedPoint_erase]
  split_ifs <;> rfl

omit [MeasurableSpace Y] in
private theorem window_index_lt_of_count {d R : ℝ} (hd : 0 < d) {n i : ℕ}
    {ω : Configuration Y} (hpos : ∀ j, 0 < ω.1 j)
    (hcount : ω ∈ arrivalWindowCountEvent d R n) (hi : markedArrivalPoint d i ω ∈ arrivalWindow R) :
    i < n := by
  have hn : markedArrivalCount d (arrivalWindow R) ω = (n : ℝ≥0∞) := hcount
  have hmono : Monotone (arrivalLength d ω.1) := by
    have hp : Monotone (arrivalPrefix ω.1) := monotone_nat_of_le_succ fun j => by
      rw [arrivalPrefix_succ]
      exact le_add_of_nonneg_right (hpos j).le
    apply monotone_nat_of_le_succ
    intro j
    change arrivalPrefix ω.1 (j+1) ^ (1/d : ℝ) ≤ arrivalPrefix ω.1 (j+2) ^ (1/d : ℝ)
    exact Real.rpow_le_rpow (by have h := hp (Nat.zero_le (j+1)); simpa using h)
      (hp (Nat.le_succ (j+1))) (by positivity)
  have hl (j : ℕ) : 0 < arrivalLength d ω.1 j := by
    unfold arrivalLength
    exact Real.rpow_pos_of_pos
      (Finset.sum_pos (fun u _ => hpos u) (Finset.nonempty_range_add_one)) _
  have hbound (j : ℕ) (hj : j ∈ Finset.range (i+1)) :
      markedArrivalPoint d j ω ∈ arrivalWindow R :=
    ⟨⟨hl j, (hmono (Nat.le_of_lt_succ (Finset.mem_range.mp hj))).trans hi.1.2⟩, Set.mem_univ _⟩
  let f (j : ℕ) := (arrivalWindow R).indicator (fun _ => (1 : ℝ≥0∞)) (markedArrivalPoint d j ω)
  have hsum : (∑ j ∈ Finset.range (i+1), f j) = ((i+1 : ℕ) : ℝ≥0∞) := by
    calc
      _ = ∑ _j ∈ Finset.range (i+1), (1 : ℝ≥0∞) :=
        Finset.sum_congr rfl fun j hj => indicator_of_mem (hbound j hj) _
      _ = _ := by simp
  have hle := ENNReal.sum_le_tsum (s := Finset.range (i+1)) (f := f)
  rw [hsum] at hle
  change ((i+1 : ℕ) : ℝ≥0∞) ≤ markedArrivalCount d (arrivalWindow R) ω at hle
  rw [hn, Nat.cast_le] at hle
  omega

omit [MeasurableSpace Y] in
/-- On a fixed-count event the finite window is exactly the corresponding
initial segment of the ordered arrivals. -/
theorem markedArrivalPoint_mem_window_iff_of_count {d R : ℝ} (hd : 0 < d) {n i : ℕ}
    {ω : Configuration Y} (hpos : ∀ j, 0 < ω.1 j)
    (hcount : ω ∈ arrivalWindowCountEvent d R n) :
    markedArrivalPoint d i ω ∈ arrivalWindow R ↔ i < n := by
  refine ⟨window_index_lt_of_count hd hpos hcount, fun hi => ?_⟩
  by_contra hnot
  let f (j : ℕ) := (arrivalWindow R).indicator (fun _ => (1 : ℝ≥0∞)) (markedArrivalPoint d j ω)
  have hsupport (j : ℕ) (hj : j ∉ Finset.range n) : f j = 0 :=
    indicator_of_notMem (fun h => hj (Finset.mem_range.mpr
      (window_index_lt_of_count hd hpos hcount h))) _
  have heq : (∑' j, f j) = ∑ j ∈ Finset.range n, f j := tsum_eq_sum hsupport
  have hs : (∑ j ∈ Finset.range n, f j) = (n : ℝ≥0∞) := by
    rw [← heq]
    exact hcount
  have him : i ∈ Finset.range n := Finset.mem_range.mpr hi
  have hf0 : f i = 0 := indicator_of_notMem hnot _
  rw [← Finset.sum_erase_add _ f him, hf0, add_zero] at hs
  have hle : (∑ j ∈ (Finset.range n).erase i, f j) ≤
      (((Finset.range n).erase i).card : ℝ≥0∞) := by
    calc
      _ ≤ ∑ _j ∈ (Finset.range n).erase i, (1 : ℝ≥0∞) :=
        Finset.sum_le_sum fun j _ => by
          by_cases hj : markedArrivalPoint d j ω ∈ arrivalWindow R
          · rw [show f j = 1 from indicator_of_mem hj _]
          · rw [show f j = 0 from indicator_of_notMem hj _]
            exact zero_le_one
      _ = _ := by simp
  rw [hs, Nat.cast_le, Finset.card_erase_of_mem him, Finset.card_range] at hle
  omega

private theorem window_mark_recurrence {d R : ℝ} (hd : 0 < d)
    (μ : Measure Y) [IsProbabilityMeasure μ] (n : ℕ) (F : (Fin (n+1) → ℝ × Y) → ℝ≥0∞)
    (hF : Measurable F) (hsym : ∀ (x : Fin (n+1) → ℝ × Y) (p : Equiv.Perm (Fin (n+1))), F (x ∘ p) = F x) :
    ((n+1 : ℕ) : ℝ≥0∞) *
      (∫⁻ ω in arrivalWindowCountEvent d R (n+1), F (firstMarkedArrivals d (n+1) ω)
        ∂markedArrivalSequenceLaw μ) =
      ∫⁻ x in arrivalWindow R, ∫⁻ ω in arrivalWindowCountEvent d R n,
        F (Fin.cons x (firstMarkedArrivals d n ω)) ∂markedArrivalSequenceLaw μ
        ∂(intensity d).prod μ := by
  let P := markedArrivalSequenceLaw μ
  let T := (intensity d).prod μ
  let A := arrivalWindow (Y := Y) R
  let e := arrivalWindowCountEvent (Y := Y) d R
  let H (p : (ℝ × Y) × Configuration Y) := F (Fin.cons p.1 (firstMarkedArrivals d n p.2))
  let g := (A ×ˢ e n).indicator H
  have hH : Measurable H := hF.comp (measurable_cons.comp
    (measurable_fst.prodMk ((measurable_firstMarkedArrivals d n).comp measurable_snd)))
  have hg : Measurable g := hH.indicator ((measurableSet_arrivalWindow R).prod (measurableSet_arrivalWindowCountEvent d R n))
  have hM := canonical_iid_marked_arrival_insertion hd μ g hg
  have hR : (∫⁻ p, g p ∂T.prod P) =
      ∫⁻ x in A, ∫⁻ ω in e n, H (x, ω) ∂P ∂T := by
    let : IsProbabilityMeasure P := isProbabilityMeasure_markedArrivalSequenceLaw μ
    rw [lintegral_prod _ hg.aemeasurable, ← lintegral_indicator (measurableSet_arrivalWindow R)]
    apply lintegral_congr
    intro x
    by_cases hx : x ∈ A
    · rw [indicator_of_mem hx, ← lintegral_indicator (measurableSet_arrivalWindowCountEvent d R n)]
      apply lintegral_congr
      intro ω
      change g (x, ω) = (e n).indicator (fun ω => H (x, ω)) ω
      by_cases he : ω ∈ e n
      · dsimp only [g]
        rw [indicator_of_mem (show (x, ω) ∈ A ×ˢ e n from ⟨hx, he⟩), indicator_of_mem he]
      · dsimp only [g]
        rw [indicator_of_notMem (show (x, ω) ∉ A ×ˢ e n from fun h => he h.2), indicator_of_notMem he]
    · rw [indicator_of_notMem hx]
      have heq : ∀ ω, g (x, ω) = 0 := fun ω => indicator_of_notMem (fun h => hx h.1) _
      simp_rw [heq, lintegral_zero]
  have hpos : ∀ᵐ ω ∂P, ∀ i, 0 < ω.1 i := by
    let : IsProbabilityMeasure (Measure.infinitePi (fun _ : ℕ => μ)) := inferInstance
    have hp := Measure.quasiMeasurePreserving_fst (μ := exponentialSpacings)
      (ν := Measure.infinitePi (fun _ : ℕ => μ))
    exact hp.tendsto_ae.eventually ae_expSpacing_pos
  have hL : (∫⁻ ω, ∑' i, g (markedArrivalPoint d i ω,
      (eraseArrivalGap i ω.1, eraseSequence i ω.2)) ∂P) =
      ((n+1 : ℕ) : ℝ≥0∞) * (∫⁻ ω in e (n+1), F (firstMarkedArrivals d (n+1) ω) ∂P) := by
    have hm : Measurable (fun ω : Configuration Y => F (firstMarkedArrivals d (n+1) ω)) :=
      hF.comp (measurable_firstMarkedArrivals d (n+1))
    rw [← lintegral_indicator (measurableSet_arrivalWindowCountEvent d R (n+1)),
      ← lintegral_const_mul _ (hm.indicator (measurableSet_arrivalWindowCountEvent d R (n+1)))]
    apply lintegral_congr_ae
    filter_upwards [hpos] with ω hω
    let f (i : ℕ) := A.indicator (fun _ => (1 : ℝ≥0∞)) (markedArrivalPoint d i ω)
    have hs (i : ℕ) :
        g (markedArrivalPoint d i ω, (eraseArrivalGap i ω.1, eraseSequence i ω.2)) =
          f i * (e (n+1)).indicator (fun x => F (firstMarkedArrivals d (n+1) x)) ω := by
      by_cases hi : markedArrivalPoint d i ω ∈ A
      · have hfi : f i = 1 := indicator_of_mem hi _
        have hE : (eraseArrivalGap i ω.1, eraseSequence i ω.2) ∈ e n ↔ ω ∈ e (n+1) := by
          have h := arrivalWindowCount_erase_add d R ω i
          change _ + f i = _ at h
          rw [hfi] at h
          change markedArrivalCount d A _ = _ ↔ markedArrivalCount d A ω = _
          rw [← h, Nat.cast_add, Nat.cast_one, ENNReal.add_left_inj ENNReal.one_ne_top]
        by_cases he : ω ∈ e (n+1)
        · have hj := window_index_lt_of_count hd hω he hi
          let j : Fin (n+1) := ⟨i,hj⟩
          have hm : (markedArrivalPoint d i ω, (eraseArrivalGap i ω.1, eraseSequence i ω.2)) ∈
              A ×ˢ e n := ⟨hi, hE.mpr he⟩
          dsimp only [g]
          rw [indicator_of_mem hm, hfi, indicator_of_mem he, one_mul]
          change F (Fin.cons (firstMarkedArrivals d (n+1) ω j)
            (firstMarkedArrivals d n (eraseArrivalGap j ω.1, eraseSequence j ω.2))) = _
          rw [firstMarkedArrivals_erase, Fin.cons_removeNth_eq_comp_cycleRange_symm]
          exact hsym _ _
        · have hm : (markedArrivalPoint d i ω, (eraseArrivalGap i ω.1, eraseSequence i ω.2)) ∉
              A ×ˢ e n := fun h => he (hE.mp h.2)
          dsimp only [g]
          rw [indicator_of_notMem hm, indicator_of_notMem he, mul_zero]
      · have hm : (markedArrivalPoint d i ω, (eraseArrivalGap i ω.1, eraseSequence i ω.2)) ∉
            A ×ˢ e n := fun h => hi h.1
        dsimp only [g]
        rw [indicator_of_notMem hm, show f i = 0 from indicator_of_notMem hi _, zero_mul]
    simp_rw [hs, ENNReal.tsum_mul_right]
    by_cases he : ω ∈ e (n+1)
    · rw [indicator_of_mem he]
      have hc : (∑' i, f i) = ((n+1 : ℕ) : ℝ≥0∞) := he
      rw [hc]
    · rw [indicator_of_notMem he, mul_zero, mul_zero]
  exact hL.symm.trans (hM.trans hR)

private theorem windowMeasure_mass {d R : ℝ} (hd : 0 < d) (hR : 0 < R)
    (μ : Measure Y) [IsProbabilityMeasure μ] :
    ((intensity d).prod μ) (arrivalWindow R) = ENNReal.ofReal (R ^ d) := by
  unfold arrivalWindow
  rw [Measure.prod_prod, intensity_Ioc_zero hd hR.le, measure_univ, mul_one]

theorem isProbabilityMeasure_conditionalWindowMarkLaw {d R : ℝ} (hd : 0 < d) (hR : 0 < R)
    (μ : Measure Y) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (conditionalWindowMarkLaw d R μ) := by
  constructor
  unfold conditionalWindowMarkLaw
  rw [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul, windowMeasure_mass hd hR μ,
    ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr (Real.rpow_pos_of_pos hR d)) ENNReal.ofReal_ne_top]

private theorem windowCount_mass_recurrence {d R : ℝ} (hd : 0 < d)
    (μ : Measure Y) [IsProbabilityMeasure μ] (n : ℕ) :
    ((n+1 : ℕ) : ℝ≥0∞) * markedArrivalSequenceLaw μ (arrivalWindowCountEvent d R (n+1)) =
      ((intensity d).prod μ) (arrivalWindow R) * markedArrivalSequenceLaw μ (arrivalWindowCountEvent d R n) := by
  have h := window_mark_recurrence (R := R) hd μ n (fun _ => 1) measurable_const (fun _ _ => rfl)
  simpa only [lintegral_const, Measure.restrict_apply_univ, one_mul, mul_comm] using h

omit [MeasurableSpace Y] in
private theorem window_cons_tail_symmetry {n : ℕ} {F : (Fin (n+1) → ℝ × Y) → ℝ≥0∞}
    (hsym : ∀ (x : Fin (n+1) → ℝ × Y) (p : Equiv.Perm (Fin (n+1))), F (x ∘ p) = F x)
    (x : ℝ × Y) (y : Fin n → ℝ × Y) (p : Equiv.Perm (Fin n)) :
    F (Fin.cons x (y ∘ p)) = F (Fin.cons x y) := by
  let q : Equiv.Perm (Fin (n+1)) := Equiv.Perm.decomposeFin.symm (0, p)
  have heq : Fin.cons x (y ∘ p) = (Fin.cons x y) ∘ q := by
    funext i
    cases i using Fin.cases <;> simp [q, Function.comp_def]
  rw [heq, hsym]

/-- For every symmetric nonnegative measurable test, the marked points in
the finite window, conditional on their count, have the iid restricted
and normalized intensity law. The factors on both sides are unnormalized
count-restricted integrals, so the equality applies to extended tests. -/
theorem lintegral_canonical_window_marks {d R : ℝ} (hd : 0 < d) (hR : 0 < R)
    (μ : Measure Y) [IsProbabilityMeasure μ] (n : ℕ) (F : (Fin n → ℝ × Y) → ℝ≥0∞)
    (hF : Measurable F) (hsym : ∀ (x : Fin n → ℝ × Y) (p : Equiv.Perm (Fin n)), F (x ∘ p) = F x) :
    (∫⁻ ω in arrivalWindowCountEvent d R n, F (firstMarkedArrivals d n ω) ∂markedArrivalSequenceLaw μ) =
      markedArrivalSequenceLaw μ (arrivalWindowCountEvent d R n) *
        ∫⁻ x, F x ∂Measure.pi (fun _ : Fin n => conditionalWindowMarkLaw d R μ) := by
  let P := markedArrivalSequenceLaw μ
  let T := (intensity d).prod μ
  let A := arrivalWindow (Y := Y) R
  let e := arrivalWindowCountEvent (Y := Y) d R
  let ν := conditionalWindowMarkLaw d R μ
  let : IsProbabilityMeasure ν := isProbabilityMeasure_conditionalWindowMarkLaw hd hR μ
  let p (n : ℕ) := P (e n)
  change (∫⁻ ω in e n, F (firstMarkedArrivals d n ω) ∂P) =
    p n * ∫⁻ x, F x ∂Measure.pi (fun _ : Fin n => ν)
  induction n with
  | zero =>
    have heq : F = fun _ => F Fin.elim0 :=
      funext fun v => congrArg F (funext fun i => i.elim0)
    rw [heq, lintegral_const, lintegral_const, Measure.restrict_apply_univ, measure_univ, mul_one, mul_comm]
  | succ n ih =>
    let G (p : (ℝ × Y) × (Fin n → ℝ × Y)) := F (Fin.cons p.1 p.2)
    have hG : Measurable G := hF.comp measurable_cons
    have hGx (x : ℝ × Y) : Measurable (fun y => F (Fin.cons x y)) :=
      hG.comp measurable_prodMk_left
    let Q := Measure.pi (fun _ : Fin n => ν)
    have hsplit : (∫⁻ xy, G xy ∂ν.prod Q) = ∫⁻ v, F v ∂Measure.pi (fun _ : Fin (n+1) => ν) := by
      let f := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ × Y) 0
      have hf : MeasurePreserving f (Measure.pi (fun _ : Fin (n+1) => ν)) (ν.prod Q) :=
        measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => ν) 0
      have h := hf.symm.lintegral_comp hF
      change (∫⁻ xy, F (f.symm xy) ∂ν.prod Q) = _ at h
      have heq (xy : (ℝ × Y) × (Fin n → ℝ × Y)) : f.symm xy = Fin.cons xy.1 xy.2 := by
        simp [f, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero']
      simpa only [G, heq] using h
    have hr : T.restrict A = (T A) • ν := by
      have hr₀ : T A ≠ 0 := by
        rw [windowMeasure_mass hd hR μ]
        exact ENNReal.ofReal_ne_zero_iff.mpr (Real.rpow_pos_of_pos hR d)
      have hr₁ : T A ≠ ∞ := by rw [windowMeasure_mass hd hR μ]; exact ENNReal.ofReal_ne_top
      unfold ν conditionalWindowMarkLaw
      rw [smul_smul, ENNReal.mul_inv_cancel hr₀ hr₁, one_smul]
    have hrec := window_mark_recurrence (R := R) hd μ n F hF hsym
    change ((n+1 : ℕ) : ℝ≥0∞) *
        (∫⁻ ω in e (n+1), F (firstMarkedArrivals d (n+1) ω) ∂P) =
      ∫⁻ x in A, ∫⁻ ω in e n, F (Fin.cons x (firstMarkedArrivals d n ω)) ∂P ∂T at hrec
    simp_rw [fun x => ih (fun y => F (Fin.cons x y)) (hGx x) (window_cons_tail_symmetry hsym x)] at hrec
    have hGmeas : Measurable (fun x => ∫⁻ y, G (x, y) ∂Q) := hG.lintegral_prod_right'
    rw [hr, lintegral_smul_measure, smul_eq_mul, lintegral_const_mul _ hGmeas, ← mul_assoc,
      ← lintegral_prod G hG.aemeasurable, hsplit, ← windowCount_mass_recurrence (R := R) hd μ n] at hrec
    rw [mul_assoc] at hrec
    exact (ENNReal.mul_right_inj (by positivity : ((n+1 : ℕ) : ℝ≥0∞) ≠ 0)
      (ENNReal.natCast_ne_top _)).mp hrec

/-- Each retained point has an independent mark with the original mark law. -/
theorem conditionalWindowMarkLaw_eq_prod {d R : ℝ} (hd : 0 < d) (hR : 0 < R)
    (μ : Measure Y) [IsProbabilityMeasure μ] :
    conditionalWindowMarkLaw d R μ =
      (((ENNReal.ofReal (R ^ d))⁻¹ • (intensity d).restrict (Set.Ioc 0 R)).prod μ) := by
  let : SigmaFinite (intensity d) := sigmaFinite_intensity d
  unfold conditionalWindowMarkLaw arrivalWindow
  dsimp only
  rw [Measure.prod_prod, intensity_Ioc_zero hd hR.le, measure_univ, mul_one,
    ← Measure.prod_restrict, Measure.restrict_univ, Measure.prod_smul_left]

/-- The finite-window count-conditioned expectation of a symmetric test
equals its iid expectation. -/
theorem lintegral_canonical_window_marks_conditioned {d R : ℝ} (hd : 0 < d) (hR : 0 < R)
    (μ : Measure Y) [IsProbabilityMeasure μ] (n : ℕ) (F : (Fin n → ℝ × Y) → ℝ≥0∞)
    (hF : Measurable F) (hsym : ∀ (x : Fin n → ℝ × Y) (p : Equiv.Perm (Fin n)), F (x ∘ p) = F x) :
    let P := markedArrivalSequenceLaw μ
    let e := arrivalWindowCountEvent (Y := Y) d R n
    (∫⁻ ω, F (firstMarkedArrivals d n ω) ∂((P e)⁻¹ • P.restrict e)) =
      ∫⁻ x, F x ∂Measure.pi (fun _ : Fin n => conditionalWindowMarkLaw d R μ) := by
  dsimp only
  let P := markedArrivalSequenceLaw μ
  let e := arrivalWindowCountEvent (Y := Y) d R n
  let : IsProbabilityMeasure P := isProbabilityMeasure_markedArrivalSequenceLaw μ
  have hmass : 0 < P e := by
    have hfin : ((intensity d).prod μ) (arrivalWindow (Y := Y) R) ≠ ∞ := by
      rw [windowMeasure_mass hd hR μ]
      exact ENNReal.ofReal_ne_top
    have h := canonical_iid_marked_count_probability hd μ (measurableSet_arrivalWindow R) hfin n
    change P e = _ at h
    rw [h, ProbabilityTheory.poissonMeasure_singleton, windowMeasure_mass hd hR μ,
      ENNReal.coe_toNNReal_eq_toReal, ENNReal.toReal_ofReal (Real.rpow_nonneg hR.le d)]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  rw [lintegral_smul_measure, lintegral_canonical_window_marks hd hR μ n F hF hsym, smul_eq_mul]
  change (P e)⁻¹ * (P e * _) = _
  rw [← mul_assoc, ENNReal.inv_mul_cancel hmass.ne' (measure_ne_top P e), one_mul]

end Certificate

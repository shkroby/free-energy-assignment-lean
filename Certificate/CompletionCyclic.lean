import Certificate.Model
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Probability.Independence.InfinitePi

/-!
# Independent cyclic assignments

The exceptional-event integrability argument uses disjoint cyclic assignments.
Here their disjointness is expressed as injectivity of the entry-index map,
and independence follows from the concrete infinite product law.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal MeasureTheory

namespace Certificate.Completion

/-- Shift the columns of a square assignment by a fixed cyclic offset. -/
def cyclicAssignment (n : ℕ) (s : Fin (n + 1)) : Equiv.Perm (Fin (n + 1)) :=
  Equiv.addRight s

/-- All entries used by the cyclic assignments, indexed by shift and row. -/
def cyclicEntry (n : ℕ) (p : Fin (n + 1) × Fin (n + 1)) : ℕ × ℕ :=
  (p.2.val, (cyclicAssignment n p.1 p.2).val)

/-- The square family of cyclic assignments uses every matrix position at most once. -/
theorem cyclicEntry_injective (n : ℕ) : Function.Injective (cyclicEntry n) := by
  rintro ⟨s, i⟩ ⟨t, j⟩ h
  have hij : i = j := Fin.ext (congrArg Prod.fst h)
  subst j
  have hs : i + s = i + t := Fin.ext (congrArg Prod.snd h)
  exact Prod.ext (add_left_cancel hs) rfl

/-- The collection of row costs in the cyclic assignment with offset `s`. -/
def cyclicRows (n : ℕ) (s : Fin (n + 1)) (C : CostArray) (i : Fin (n + 1)) : ℝ :=
  C (cyclicEntry n (s, i))

/-- The unscaled cost of the cyclic assignment with offset `s`. -/
def cyclicCost (n : ℕ) (s : Fin (n + 1)) (C : CostArray) : ℝ :=
  ∑ i, cyclicRows n s C i

/-- The entire collection of row costs has product law across shifts and rows. -/
theorem cyclicRows_jointLaw (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ) :
    (iidCosts μ).map (fun C s => cyclicRows n s C) =
      Measure.infinitePi (fun _ : Fin (n + 1) => Measure.infinitePi (fun _ : Fin (n + 1) => μ)) := by
  let D := Fin (n + 1)
  let extract : CostArray → (D × D → ℝ) := fun C p => C (cyclicEntry n p)
  have hm : Measurable extract := by unfold extract; fun_prop
  have hmap : (iidCosts μ).map extract = Measure.infinitePi (fun _ : D × D => μ) :=
    Measure.map_infinitePi_infinitePi_of_inj (cyclicEntry_injective n)
  have hcurry : (fun C s => cyclicRows n s C) =
      (MeasurableEquiv.curry D D ℝ) ∘ extract := rfl
  rw [hcurry, ← Measure.map_map (MeasurableEquiv.curry D D ℝ).measurable hm,
    hmap, Measure.infinitePi_map_curry (fun (_ : D) (_ : D) => μ)]

/-- The total costs of the disjoint cyclic assignments are jointly independent. -/
theorem cyclicCost_independent (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ) :
    iIndepFun (cyclicCost n) (iidCosts μ) := by
  let : IsProbabilityMeasure (iidCosts μ) := by unfold iidCosts; infer_instance
  have hrow (s : Fin (n + 1)) : Measurable (cyclicRows n s) := by unfold cyclicRows; fun_prop
  have hmarginal (s : Fin (n + 1)) :
      (iidCosts μ).map (cyclicRows n s) = Measure.infinitePi (fun _ : Fin (n + 1) => μ) :=
    Measure.map_infinitePi_infinitePi_of_inj
      (fun i j h => Fin.ext (congrArg Prod.fst h))
  have hrows : iIndepFun (cyclicRows n) (iidCosts μ) := by
    rw [iIndepFun_iff_map_fun_eq_infinitePi_map hrow, cyclicRows_jointLaw]
    simp only [hmarginal]
  exact hrows.comp (fun _ r => ∑ i, r i) (by intro s; fun_prop)

/-- A cyclic assignment exceeding `u` must use an entry exceeding `u / (n + 1)`. -/
theorem cyclicCost_tail_le (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ)
    (s : Fin (n + 1)) (u : ℝ) :
    iidCosts μ ((cyclicCost n s) ⁻¹' Ioi u) ≤
      ((n : ℝ≥0∞) + 1) * μ (Ioi (u / ((n : ℝ) + 1))) := by
  let t : ℝ := u / ((n : ℝ) + 1)
  let A (i : Fin (n + 1)) : Set CostArray := (fun C => cyclicRows n s C i) ⁻¹' Ioi t
  have hsub : (cyclicCost n s) ⁻¹' Ioi u ⊆ ⋃ i, A i := by
    intro C hC
    by_contra h
    have hentry (i : Fin (n + 1)) : cyclicRows n s C i ≤ t :=
      le_of_not_gt (fun hi => h (mem_iUnion.mpr ⟨i, hi⟩))
    have hsum : cyclicCost n s C ≤ u := calc
      _ ≤ ∑ _i : Fin (n + 1), t := Finset.sum_le_sum (fun i _ => hentry i)
      _ = _ := by
        simp [nsmul_eq_mul, Nat.cast_add, t]
        field_simp
    exact (not_lt_of_ge hsum) hC
  have hA (i : Fin (n + 1)) : iidCosts μ (A i) = μ (Ioi t) := by
    let j := cyclicEntry n (s, i)
    change iidCosts μ ((fun C : CostArray => C j) ⁻¹' Ioi t) = μ (Ioi t)
    rw [← Measure.map_apply (measurable_pi_apply j) measurableSet_Ioi]
    exact congrArg (fun ν : Measure ℝ => ν (Ioi t))
      (Measure.infinitePi_map_eval (fun _ : ℕ × ℕ => μ) j)
  calc
    _ ≤ iidCosts μ (⋃ i, A i) := measure_mono hsub
    _ ≤ ∑' i, iidCosts μ (A i) := measure_iUnion_le A
    _ = _ := by rw [tsum_fintype]; simp [hA, nsmul_eq_mul, Nat.cast_add, t]

/-- For any number of selected cyclic shifts, the upper tail for their minimum
has a power equal to the number of selected shifts. -/
theorem cyclicCost_min_tail_le (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ)
    (S : Finset (Fin (n + 1))) (u : ℝ) :
    iidCosts μ (⋂ s ∈ S, (cyclicCost n s) ⁻¹' Ioi u) ≤
      (((n : ℝ≥0∞) + 1) * μ (Ioi (u / ((n : ℝ) + 1)))) ^ S.card := by
  let A (s : Fin (n + 1)) : Set CostArray := (cyclicCost n s) ⁻¹' Ioi u
  have hA (s : Fin (n + 1)) :
      MeasurableSet[MeasurableSpace.comap (cyclicCost n s) inferInstance] (A s) :=
    ⟨Ioi u, measurableSet_Ioi, rfl⟩
  change iidCosts μ (⋂ s ∈ S, A s) ≤ _
  rw [(cyclicCost_independent μ n).meas_biInter (fun s _ => hA s)]
  calc
    _ ≤ ∏ _s ∈ S, ((n : ℝ≥0∞) + 1) * μ (Ioi (u / ((n : ℝ) + 1))) :=
      Finset.prod_le_prod (fun _ _ => zero_le) (fun s _ => cyclicCost_tail_le μ n s u)
    _ = _ := Finset.prod_const _

/-- Markov's inequality for a positive real power of the individual cost. -/
theorem cost_rpow_tail_le (μ : Measure ℝ) {q t : ℝ} (hq : 0 < q) (ht : 0 < t) :
    μ (Ioi t) ≤ (∫⁻ c, ENNReal.ofReal (c ^ q) ∂μ) / ENNReal.ofReal (t ^ q) := by
  let f : ℝ → ℝ≥0∞ := fun c => ENNReal.ofReal (c ^ q)
  have hm : Measurable f := by unfold f; fun_prop
  apply (measure_mono (t := {c | ENNReal.ofReal (t ^ q) ≤ f c}) ?_).trans
    (meas_ge_le_lintegral_div hm.aemeasurable
      (ENNReal.ofReal_ne_zero_iff.mpr (Real.rpow_pos_of_pos ht q)) ENNReal.ofReal_ne_top)
  intro c hc
  exact ENNReal.ofReal_le_ofReal (Real.rpow_lt_rpow ht.le (mem_Ioi.mp hc) hq).le

/-- Explicit positive-moment bound on the probability that every selected cyclic
assignment has a total cost above the same threshold. -/
theorem cyclicCost_min_tail_le_rpow (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ)
    (S : Finset (Fin (n + 1))) {u q : ℝ} (hu : 0 < u) (hq : 0 < q) :
    iidCosts μ (⋂ s ∈ S, (cyclicCost n s) ⁻¹' Ioi u) ≤
      (((n : ℝ≥0∞) + 1) *
        ((∫⁻ c, ENNReal.ofReal (c ^ q) ∂μ) /
          ENNReal.ofReal ((u / ((n : ℝ) + 1)) ^ q))) ^ S.card := by
  apply (cyclicCost_min_tail_le μ n S u).trans
  gcongr
  exact cost_rpow_tail_le μ hq (div_pos hu (by positivity))

/-- Any one cyclic assignment gives a deterministic lower bound on the pressure. -/
theorem neg_pressure_le_cyclicCost (β d κ : ℝ) (n : ℕ) (s : Fin (n + 1)) (C : CostArray) :
    -pressure β d κ (n + 1) C ≤
      (β * lengthScale d κ (n + 1) * cyclicCost n s C) / ((n + 1 : ℕ) : ℝ) := by
  let a := β * lengthScale d κ (n + 1)
  have hweight : Real.exp (-(a * cyclicCost n s C)) ≤ assignmentPartition β d κ (n + 1) C := by
    calc
      _ = ∏ i : Fin (n + 1), Real.exp (-(a * cyclicRows n s C i)) := by
        rw [cyclicCost, ← neg_mul, Finset.mul_sum, Real.exp_sum]
        simp only [neg_mul]
      _ ≤ _ := by
        unfold assignmentPartition permanent
        exact Finset.single_le_sum (a := cyclicAssignment n s)
          (f := fun p : Equiv.Perm (Fin (n + 1)) =>
            ∏ i : Fin (n + 1), Real.exp (-(a * C (i.val, (p i).val))))
          (fun _ _ => Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le)
          (Finset.mem_univ _)
  have hlog := Real.log_le_log (Real.exp_pos _) hweight
  rw [Real.log_exp] at hlog
  unfold pressure
  rw [← neg_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  change -Real.log (assignmentPartition β d κ (n + 1) C) ≤ a * cyclicCost n s C
  linarith

/-- The negative part is bounded by the same selected cyclic cost when the
scaled cost is nonnegative. -/
theorem pressure_negPart_le_cyclicCost (β d κ : ℝ) (n : ℕ)
    (s : Fin (n + 1)) (C : CostArray)
    (hnonneg : 0 ≤ β * lengthScale d κ (n + 1) * cyclicCost n s C) :
    max (-pressure β d κ (n + 1) C) 0 ≤
      (β * lengthScale d κ (n + 1) * cyclicCost n s C) / ((n + 1 : ℕ) : ℝ) :=
  max_le (neg_pressure_le_cyclicCost β d κ n s C) (div_nonneg hnonneg (by positivity))

end Certificate.Completion

import Certificate.CouplingOrthantOrder
import Certificate.PoissonArrivalMecke
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.Probability.Independence.InfinitePi

/-! Lower-orthant comparison under independent addition and nonnegative weighted sums. -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Certificate

/-- Law of the coordinatewise sum of two independent real pairs. -/
noncomputable def pairConvolution (ρ τ : ProbabilityMeasure (ℝ × ℝ)) :
    ProbabilityMeasure (ℝ × ℝ) :=
  (ρ.prod τ).map ((measurable_fst.add measurable_snd).aemeasurable)

theorem pairConvolution_apply_orthant (ρ τ : ProbabilityMeasure (ℝ × ℝ)) (x y : ℝ) :
    (pairConvolution ρ τ : Measure (ℝ × ℝ)) (Iic x ×ˢ Iic y) =
      ∫⁻ q, (ρ : Measure (ℝ × ℝ)) (Iic (x - q.1) ×ˢ Iic (y - q.2)) ∂(τ : Measure (ℝ × ℝ)) := by
  let addPair : (ℝ × ℝ) × (ℝ × ℝ) → ℝ × ℝ := fun p => p.1 + p.2
  have hm : Measurable addPair := measurable_fst.add measurable_snd
  have hs : MeasurableSet (Iic x ×ˢ Iic y) := measurableSet_Iic.prod measurableSet_Iic
  change (((ρ : Measure (ℝ × ℝ)).prod (τ : Measure (ℝ × ℝ))).map addPair) _ = _
  rw [Measure.map_apply hm hs, Measure.prod_apply_symm (hs.preimage hm)]
  apply lintegral_congr
  intro q
  congr 1
  ext p
  change (p.1 + q.1 ≤ x ∧ p.2 + q.2 ≤ y) ↔ (p.1 ≤ x - q.1 ∧ p.2 ≤ y - q.2)
  simp only [le_sub_iff_add_le]

theorem pairConvolution_comm (ρ τ : ProbabilityMeasure (ℝ × ℝ)) :
    pairConvolution ρ τ = pairConvolution τ ρ := by
  apply Subtype.ext
  let addPair : (ℝ × ℝ) × (ℝ × ℝ) → ℝ × ℝ := fun p => p.1 + p.2
  have hm : Measurable addPair := measurable_fst.add measurable_snd
  have hswap : addPair ∘ Prod.swap = addPair := funext fun p => add_comm p.2 p.1
  change ((ρ : Measure (ℝ × ℝ)).prod (τ : Measure (ℝ × ℝ))).map addPair =
    ((τ : Measure (ℝ × ℝ)).prod (ρ : Measure (ℝ × ℝ))).map addPair
  rw [← Measure.prod_swap (μ := (ρ : Measure (ℝ × ℝ))) (ν := (τ : Measure (ℝ × ℝ))),
    Measure.map_map hm measurable_swap, hswap]

/-- Adding an independent pair preserves lower-orthant order. -/
theorem orthantLE_pairConvolution_left {ρ σ : ProbabilityMeasure (ℝ × ℝ)}
    (h : orthantLE ρ σ) (τ : ProbabilityMeasure (ℝ × ℝ)) :
    orthantLE (pairConvolution ρ τ) (pairConvolution σ τ) := by
  intro x y
  rw [pairConvolution_apply_orthant, pairConvolution_apply_orthant]
  apply lintegral_mono
  intro q
  exact h (x - q.1) (y - q.2)

/-- Independent addition is monotone in both pair laws. -/
theorem orthantLE_pairConvolution {ρ σ τ υ : ProbabilityMeasure (ℝ × ℝ)}
    (h₁ : orthantLE ρ σ) (h₂ : orthantLE τ υ) :
    orthantLE (pairConvolution ρ τ) (pairConvolution σ υ) := by
  have ha := orthantLE_pairConvolution_left h₁ τ
  have hb := orthantLE_pairConvolution_left h₂ σ
  rw [pairConvolution_comm τ σ, pairConvolution_comm υ σ] at hb
  exact fun x y => (ha x y).trans (hb x y)

private theorem measurable_pairScale (a : ℝ) : Measurable (fun p : ℝ × ℝ => a • p) := by
  fun_prop

/-- Law of a real pair scaled by a deterministic scalar. -/
noncomputable def pairScaleLaw (a : ℝ) (ρ : ProbabilityMeasure (ℝ × ℝ)) :
    ProbabilityMeasure (ℝ × ℝ) :=
  ρ.map (measurable_pairScale a).aemeasurable

/-- A deterministic nonnegative weight preserves lower-orthant order. -/
theorem orthantLE_pairScaleLaw {ρ σ : ProbabilityMeasure (ℝ × ℝ)}
    (h : orthantLE ρ σ) {a : ℝ} (ha : 0 ≤ a) :
    orthantLE (pairScaleLaw a ρ) (pairScaleLaw a σ) := by
  intro x y
  have hm := measurable_pairScale a
  simp only [pairScaleLaw, ProbabilityMeasure.toMeasure_map,
    Measure.map_apply hm (measurableSet_Iic.prod measurableSet_Iic)]
  rcases eq_or_lt_of_le ha with rfl | ha₀
  · rw [show (fun p : ℝ × ℝ => (0 : ℝ) • p) = fun _ => 0 by simp]
    simp only [preimage_const]
    split <;> simp
  · have hpre : (fun p : ℝ × ℝ => a • p) ⁻¹' (Iic x ×ˢ Iic y) =
        Iic (x / a) ×ˢ Iic (y / a) := by
      ext p
      change (a * p.1 ≤ x ∧ a * p.2 ≤ y) ↔ (p.1 ≤ x/a ∧ p.2 ≤ y/a)
      simp only [le_div_iff₀ ha₀, mul_comm a]
    rw [hpre]
    exact h (x/a) (y/a)

/-- The finite prefix of a coordinatewise weighted sum on a sequence of pairs. -/
noncomputable def weightedPairPrefix (a : ℕ → ℝ) (n : ℕ) (ω : ℕ → ℝ × ℝ) : ℝ × ℝ :=
  ∑ i ∈ Finset.range n, a i • ω i

theorem measurable_weightedPairPrefix (a : ℕ → ℝ) (n : ℕ) :
    Measurable (weightedPairPrefix a n) := by
  unfold weightedPairPrefix
  fun_prop

/-- The actual law of the finite weighted sum of independent pairs. -/
noncomputable def iidWeightedPairSumLaw (a : ℕ → ℝ) (n : ℕ)
    (ρ : ProbabilityMeasure (ℝ × ℝ)) : ProbabilityMeasure (ℝ × ℝ) :=
  ProbabilityMeasure.map
    (⟨Measure.infinitePi (fun _ : ℕ => (ρ : Measure (ℝ × ℝ))), inferInstance⟩ :
      ProbabilityMeasure (ℕ → ℝ × ℝ)) (measurable_weightedPairPrefix a n).aemeasurable

theorem iidWeightedPairSumLaw_succ (a : ℕ → ℝ) (n : ℕ) (ρ : ProbabilityMeasure (ℝ × ℝ)) :
    iidWeightedPairSumLaw a (n + 1) ρ =
      pairConvolution (iidWeightedPairSumLaw a n ρ) (pairScaleLaw (a n) ρ) := by
  let P := Measure.infinitePi (fun _ : ℕ => (ρ : Measure (ℝ × ℝ)))
  let X := weightedPairPrefix a n
  let Y (ω : ℕ → ℝ × ℝ) := a n • ω n
  have hX : Measurable X := measurable_weightedPairPrefix a n
  have hY : Measurable Y := (measurable_pairScale (a n)).comp (measurable_pi_apply n)
  have hind : iIndepFun (fun i (ω : ℕ → ℝ × ℝ) => a i • ω i) P :=
    iIndepFun_infinitePi (X := fun i (v : ℝ × ℝ) => a i • v)
      (fun i => measurable_pairScale (a i))
  have hindXY : IndepFun X Y P := by
    have he : (∑ j ∈ Finset.range n, fun ω : ℕ → ℝ × ℝ => a j • ω j) = X := by
      funext ω
      rw [Finset.sum_apply]
      rfl
    rw [← he]
    exact hind.indepFun_finsetSum_of_notMem
      (fun i => (measurable_pairScale (a i)).comp (measurable_pi_apply i))
      (show n ∉ Finset.range n by simp)
  have hprod : P.map (fun ω => (X ω, Y ω)) = (P.map X).prod (P.map Y) :=
    hindXY.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable
  have hYlaw : P.map Y = (ρ : Measure (ℝ × ℝ)).map (fun v : ℝ × ℝ => a n • v) := calc
    P.map Y = (P.map (fun ω => ω n)).map (fun v : ℝ × ℝ => a n • v) :=
      (Measure.map_map (measurable_pairScale (a n)) (measurable_pi_apply n)).symm
    _ = _ := by rw [Measure.infinitePi_map_eval]
  let addPair : (ℝ × ℝ) × (ℝ × ℝ) → ℝ × ℝ := fun p => p.1 + p.2
  have hadd : Measurable addPair := measurable_fst.add measurable_snd
  have hstep : weightedPairPrefix a (n + 1) = addPair ∘ (fun ω => (X ω, Y ω)) := by
    funext ω
    exact Finset.sum_range_succ _ n
  apply Subtype.ext
  change P.map (weightedPairPrefix a (n+1)) =
    ((P.map X).prod ((ρ : Measure (ℝ × ℝ)).map (fun v : ℝ × ℝ => a n • v))).map addPair
  rw [hstep, ← Measure.map_map hadd (hX.prodMk hY), hprod, hYlaw]

/-- Lower-orthant comparison passes to any fixed finite sum of iid pairs
with deterministic nonnegative weights. -/
theorem orthantLE_iidWeightedPairSumLaw {ρ σ : ProbabilityMeasure (ℝ × ℝ)}
    (h : orthantLE ρ σ) (a : ℕ → ℝ) (n : ℕ) (ha : ∀ i < n, 0 ≤ a i) :
    orthantLE (iidWeightedPairSumLaw a n ρ) (iidWeightedPairSumLaw a n σ) := by
  induction n with
  | zero =>
    intro x y
    have hzero : weightedPairPrefix a 0 = fun _ => 0 := by
      funext ω
      simp [weightedPairPrefix]
    change ((Measure.infinitePi (fun _ : ℕ => (ρ : Measure (ℝ × ℝ)))).map
      (weightedPairPrefix a 0)) _ ≤
      ((Measure.infinitePi (fun _ : ℕ => (σ : Measure (ℝ × ℝ)))).map (weightedPairPrefix a 0)) _
    rw [hzero, Measure.map_const, Measure.map_const]
    simp
  | succ n ih =>
    rw [iidWeightedPairSumLaw_succ, iidWeightedPairSumLaw_succ]
    exact orthantLE_pairConvolution (ih (fun i hi => ha i (hi.trans n.lt_succ_self)))
      (orthantLE_pairScaleLaw h (ha n n.lt_succ_self))

private theorem measurable_randomWeightedPairPrefix {W : Type*} [MeasurableSpace W]
    {a : W → ℕ → ℝ} (ha : Measurable a) (n : ℕ) :
    Measurable (fun p : W × (ℕ → ℝ × ℝ) => weightedPairPrefix (a p.1) n p.2) := by
  unfold weightedPairPrefix
  apply Finset.measurable_sum
  intro i _
  exact (((measurable_pi_apply i).comp ha).comp measurable_fst).smul
    ((measurable_pi_apply i).comp measurable_snd)

/-- Law of the weighted prefix when the entire weight sequence is sampled
independently of the iid pair marks. -/
noncomputable def randomWeightedPairSumLaw {W : Type*} [MeasurableSpace W]
    (ν : ProbabilityMeasure W) {a : W → ℕ → ℝ} (ha : Measurable a) (n : ℕ)
    (ρ : ProbabilityMeasure (ℝ × ℝ)) : ProbabilityMeasure (ℝ × ℝ) :=
  (ν.prod ⟨Measure.infinitePi (fun _ : ℕ => (ρ : Measure (ℝ × ℝ))), inferInstance⟩).map
    (measurable_randomWeightedPairPrefix ha n).aemeasurable

theorem randomWeightedPairSumLaw_apply_orthant {W : Type*} [MeasurableSpace W]
    (ν : ProbabilityMeasure W) {a : W → ℕ → ℝ} (ha : Measurable a) (n : ℕ)
    (ρ : ProbabilityMeasure (ℝ × ℝ)) (x y : ℝ) :
    (randomWeightedPairSumLaw ν ha n ρ : Measure (ℝ × ℝ)) (Iic x ×ˢ Iic y) =
      ∫⁻ q, (iidWeightedPairSumLaw (a q) n ρ : Measure (ℝ × ℝ)) (Iic x ×ˢ Iic y)
        ∂(ν : Measure W) := by
  have hm := measurable_randomWeightedPairPrefix ha n
  have hs : MeasurableSet (Iic x ×ˢ Iic y) := measurableSet_Iic.prod measurableSet_Iic
  change (((ν : Measure W).prod (Measure.infinitePi (fun _ : ℕ => (ρ : Measure (ℝ × ℝ))))).map
    (fun p => weightedPairPrefix (a p.1) n p.2)) _ = _
  rw [Measure.map_apply hm hs, Measure.prod_apply (hs.preimage hm)]
  apply lintegral_congr
  intro q
  let P := Measure.infinitePi (fun _ : ℕ => (ρ : Measure (ℝ × ℝ)))
  change P (weightedPairPrefix (a q) n ⁻¹' (Iic x ×ˢ Iic y)) =
    (P.map (weightedPairPrefix (a q) n)) (Iic x ×ˢ Iic y)
  exact (Measure.map_apply (measurable_weightedPairPrefix (a q) n) hs).symm

/-- The finite weighted-sum comparison survives averaging over common
independent, almost surely nonnegative weights. -/
theorem orthantLE_randomWeightedPairSumLaw {W : Type*} [MeasurableSpace W]
    (ν : ProbabilityMeasure W) {a : W → ℕ → ℝ} (ha : Measurable a) (n : ℕ)
    (hpos : ∀ᵐ q ∂(ν : Measure W), ∀ i < n, 0 ≤ a q i)
    {ρ σ : ProbabilityMeasure (ℝ × ℝ)} (h : orthantLE ρ σ) :
    orthantLE (randomWeightedPairSumLaw ν ha n ρ) (randomWeightedPairSumLaw ν ha n σ) := by
  intro x y
  rw [randomWeightedPairSumLaw_apply_orthant, randomWeightedPairSumLaw_apply_orthant]
  apply lintegral_mono_ae
  filter_upwards [hpos] with q hq
  exact orthantLE_iidWeightedPairSumLaw h (a q) n hq x y

private noncomputable def canonicalArrivalPairWeights (β d : ℝ) (E : ℕ → ℝ) (i : ℕ) : ℝ :=
  Real.exp (-β * arrivalLength d E i)

private theorem measurable_canonicalArrivalPairWeights (β d : ℝ) :
    Measurable (canonicalArrivalPairWeights β d) := by
  unfold canonicalArrivalPairWeights arrivalLength
  fun_prop

/-- The finite weighted denominator pair on the actual canonical marked arrivals. -/
noncomputable def canonicalArrivalPairPrefix (β d : ℝ) (n : ℕ)
    (ω : (ℕ → ℝ) × (ℕ → ℝ × ℝ)) : ℝ × ℝ :=
  weightedPairPrefix (fun i => Real.exp (-β * arrivalLength d ω.1 i)) n ω.2

theorem measurable_canonicalArrivalPairPrefix (β d : ℝ) (n : ℕ) :
    Measurable (canonicalArrivalPairPrefix β d n) :=
  measurable_randomWeightedPairPrefix (measurable_canonicalArrivalPairWeights β d) n

/-- The law of the canonical weighted denominator pair truncated to its first
`n` arrivals. -/
noncomputable def canonicalArrivalPairPrefixLaw (β d : ℝ) (n : ℕ)
    (ρ : ProbabilityMeasure (ℝ × ℝ)) : ProbabilityMeasure (ℝ × ℝ) :=
  randomWeightedPairSumLaw ⟨exponentialSpacings, isProbabilityMeasure_exponentialSpacings⟩
    (measurable_canonicalArrivalPairWeights β d) n ρ

theorem canonicalArrivalPairPrefixLaw_toMeasure (β d : ℝ) (n : ℕ)
    (ρ : ProbabilityMeasure (ℝ × ℝ)) :
    (canonicalArrivalPairPrefixLaw β d n ρ : Measure (ℝ × ℝ)) =
      (markedArrivalSequenceLaw (ρ : Measure (ℝ × ℝ))).map (canonicalArrivalPairPrefix β d n) :=
  rfl

/-- Lower-orthant order passes to the actual canonical finite weighted
denominators with common independent arrivals. -/
theorem orthantLE_canonicalArrivalPairPrefixLaw {ρ σ : ProbabilityMeasure (ℝ × ℝ)}
    (h : orthantLE ρ σ) (β d : ℝ) (n : ℕ) :
    orthantLE (canonicalArrivalPairPrefixLaw β d n ρ) (canonicalArrivalPairPrefixLaw β d n σ) :=
  orthantLE_randomWeightedPairSumLaw
    ⟨exponentialSpacings, isProbabilityMeasure_exponentialSpacings⟩
    (measurable_canonicalArrivalPairWeights β d) n
    (Filter.Eventually.of_forall fun _ _ _ => Real.exp_nonneg _) h

end Certificate

import Certificate.LocalExplorationHistory
import Certificate.ShortEdges
import Mathlib.Data.Finset.Prod

/-!
# Probability of a prescribed labelled neighborhood

Testing all edges incident to the interior of a proposed neighborhood
constrains its present edges and its absent edges on disjoint array
entries. Boundary vertices may connect to untested entries.
-/

open Filter Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal Topology

namespace Certificate.LocalExploration

/-- Array positions tested by a neighborhood with the given left and
right interior labels. -/
def neighborhoodTestedEdges {n : ℕ} (L R : Finset (Fin n)) : Finset (Fin n × Fin n) :=
  (L ×ˢ (Finset.univ : Finset (Fin n))) ∪ ((Finset.univ : Finset (Fin n)) ×ˢ R)

theorem card_neighborhoodTestedEdges {n : ℕ} (L R : Finset (Fin n)) :
    (neighborhoodTestedEdges L R).card = (L.card + R.card) * n - L.card * R.card := by
  have hi : (L ×ˢ (Finset.univ : Finset (Fin n))) ∩
      ((Finset.univ : Finset (Fin n)) ×ˢ R) = L ×ˢ R := by
    ext p
    simp
  have h := Finset.card_union_add_card_inter
    (L ×ˢ (Finset.univ : Finset (Fin n))) ((Finset.univ : Finset (Fin n)) ×ˢ R)
  rw [hi, ← neighborhoodTestedEdges, Finset.card_product, Finset.card_product,
    Finset.card_product, Finset.card_univ, Fintype.card_fin, mul_comm n R.card, ← add_mul] at h
  omega

private def testedCostEntries {n : ℕ} (D : Finset (Fin n × Fin n)) : D ↪ ℕ × ℕ where
  toFun e := (e.1.1.val, e.1.2.val)
  inj' _ _ h := Subtype.ext (Prod.ext (Fin.ext (congrArg Prod.fst h)) (Fin.ext (congrArg Prod.snd h)))

/-- The retained edges on the tested part of the array are exactly the
specified set, with additional mark tests on those retained edges. -/
def labelledNeighborhoodEvent {n : ℕ} (L R : Finset (Fin n)) (E : Finset (Fin n × Fin n))
    (A : Set ℝ) (B : Fin n × Fin n → Set ℝ) : Set CostArray :=
  {C | (∀ e ∈ E, C (e.1.val, e.2.val) ∈ A ∩ B e) ∧
    (∀ e ∈ neighborhoodTestedEdges L R \ E, C (e.1.val, e.2.val) ∈ Aᶜ)}

private theorem labelledNeighborhoodEvent_eq_inter {n : ℕ} (L R : Finset (Fin n))
    (E : Finset (Fin n × Fin n)) (A : Set ℝ) (B : Fin n × Fin n → Set ℝ) :
    labelledNeighborhoodEvent L R E A B =
      (observedCosts (testedCostEntries E) ⁻¹' univ.pi (fun e => A ∩ B e)) ∩
      (observedCosts (testedCostEntries (neighborhoodTestedEdges L R \ E)) ⁻¹'
        univ.pi (fun _ => Aᶜ)) := by
  ext C
  simp only [labelledNeighborhoodEvent, mem_ofPred_eq, mem_inter_iff, Set.mem_preimage, Set.mem_pi,
    Set.mem_univ, true_implies, observedCosts, testedCostEntries, Subtype.forall]
  rfl

theorem measurableSet_labelledNeighborhoodEvent {n : ℕ} (L R : Finset (Fin n))
    (E : Finset (Fin n × Fin n)) {A : Set ℝ} (hA : MeasurableSet A)
    {B : Fin n × Fin n → Set ℝ} (hB : ∀ e ∈ E, MeasurableSet (B e)) :
    MeasurableSet (labelledNeighborhoodEvent L R E A B) := by
  rw [labelledNeighborhoodEvent_eq_inter]
  exact ((MeasurableSet.univ_pi (fun (e : E) => hA.inter (hB e e.property))).preimage
    (measurable_observedCosts _)).inter
    ((MeasurableSet.univ_pi (fun _ => hA.compl)).preimage (measurable_observedCosts _))

/-- Exact iid marked probability for a prescribed labelled neighborhood.
The exponent counts every rejected test once, including between two
interior vertices of opposite classes. -/
theorem measure_labelledNeighborhoodEvent {n : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (L R : Finset (Fin n)) (E : Finset (Fin n × Fin n))
    (hE : E ⊆ neighborhoodTestedEdges L R) {A : Set ℝ} (hA : MeasurableSet A)
    {B : Fin n × Fin n → Set ℝ} (hB : ∀ e ∈ E, MeasurableSet (B e)) :
    (iidCosts μ) (labelledNeighborhoodEvent L R E A B) =
      (∏ e ∈ E, μ (A ∩ B e)) * μ (Aᶜ) ^ ((L.card + R.card) * n - L.card*R.card - E.card) := by
  let D := neighborhoodTestedEdges L R \ E
  have hdis : ∀ (e : E) (f : D), testedCostEntries E e ≠ testedCostEntries D f := by
    intro e f heq
    have he : (e : Fin n × Fin n) = f :=
      Prod.ext (Fin.ext (congrArg Prod.fst heq)) (Fin.ext (congrArg Prod.snd heq))
    exact (Finset.mem_sdiff.mp f.property).2 (he ▸ e.property)
  rw [labelledNeighborhoodEvent_eq_inter, measure_history_inter_fresh_cylinders μ
    (testedCostEntries E) (testedCostEntries D) hdis (fun e => A ∩ B e) (fun _ => Aᶜ)
    (fun e => hA.inter (hB e e.property)) (fun _ => hA.compl)]
  have hProd : (∏ e : E, μ (A ∩ B e)) = ∏ e ∈ E, μ (A ∩ B e) :=
    Finset.prod_coe_sort (s := E) (f := fun e => μ (A ∩ B e))
  rw [hProd, Finset.prod_const, Finset.card_univ, Fintype.card_coe]
  rw [show D.card = _ from (Finset.card_sdiff_of_subset hE).trans
    (congrArg (fun x => x - E.card) (card_neighborhoodTestedEdges L R))]


private theorem tendsto_none_of_linear_tests {p : ℕ → ℝ} {m : ℝ}
    (hp : Tendsto (fun n : ℕ => (n : ℝ) * p n) atTop (𝓝 m)) (a b : ℕ) :
    Tendsto (fun n => (1 - p n)^(a*n-b)) atTop (𝓝 (Real.exp (-(a : ℝ)*m))) := by
  have hp₀ := tendsto_zero_of_tendsto_mul_atTop hp
  have hq : Tendsto (fun n => 1 - p n) atTop (𝓝 1) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hp₀
  have hpow : Tendsto (fun n => (1-p n)^n) atTop (𝓝 (Real.exp (-m))) := by
    simpa using (tendsto_choose_mul_pow_of_tendsto_mul_atTop (k := 0) hp)
  by_cases ha : a = 0
  · simp [ha]
  · have hnum : Tendsto (fun n => ((1-p n)^n)^a) atTop
        (𝓝 (Real.exp (-(a : ℝ)*m))) := by
      convert hpow.pow a using 2
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hden : Tendsto (fun n => (1-p n)^b) atTop (𝓝 1) := by simpa using hq.pow b
    have hFrac := hnum.div hden zero_ne_one.symm
    simp only [div_one] at hFrac
    refine hFrac.congr' ?_
    filter_upwards [eventually_ge_atTop b, hp₀.eventually (Iio_mem_nhds (zero_lt_one : (0 : ℝ) < 1))]
      with n hn hp₁
    have hsub : b ≤ a * n := hn.trans (by
      have ha' := Nat.pos_of_ne_zero ha
      simpa using Nat.mul_le_mul_right n ha')
    change ((1 - p n) ^ n) ^ a / (1 - p n) ^ b = (1 - p n) ^ (a * n - b)

    rw [← pow_mul, mul_comm n a, pow_sub₀ _ (sub_pos.mpr hp₁).ne' hsub, div_eq_mul_inv]

/-- The normalized scalar probability factor for a fixed number of
retained edges and a linearly growing number of rejected tests. -/
theorem tendsto_normalized_shortEdge_shape_mass {μ : Measure ℝ}
    {d κ R : ℝ} (hd : 0 < d) (hκ : 0 < κ) (hR : 0 < R) (hμ : SmallCostTail μ κ d)
    (l r e : ℕ) :
    Tendsto (fun n : ℕ => (n : ℝ)^e * (shortEdgeProbability μ d κ R n)^e *
      (1 - shortEdgeProbability μ d κ R n)^((l+r)*n-l*r-e)) atTop
      (𝓝 ((R^d)^e * Real.exp (-((l+r : ℕ) : ℝ) * R^d))) := by
  have h := tendsto_scaled_shortEdgeProbability hd hκ hR hμ
  simpa only [mul_pow, Nat.sub_sub] using
    (h.pow e).mul (tendsto_none_of_linear_tests h (l+r) (l*r+e))

/-- A single labelled finite tree event has the expected rare-edge
scaling. The parameters are its fixed edge count and the two fixed
interior vertex counts. -/
theorem tendsto_scaled_labelledNeighborhood_mass {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {d κ R₀ : ℝ} (hd : 0 < d) (hκ : 0 < κ) (hR : 0 < R₀) (hμ : SmallCostTail μ κ d)
    (l r e : ℕ) (L R : ∀ n, Finset (Fin n)) (E : ∀ n, Finset (Fin n × Fin n))
    (hfit : ∀ᶠ n in atTop, E n ⊆ neighborhoodTestedEdges (L n) (R n))
    (hcard : ∀ᶠ n in atTop, (L n).card = l ∧ (R n).card = r ∧ (E n).card = e) :
    Tendsto (fun n : ℕ => (n : ℝ)^e *
      (iidCosts μ).real (labelledNeighborhoodEvent (L n) (R n) (E n)
        (Iic (R₀ / lengthScale d κ n)) (fun _ => univ))) atTop
      (𝓝 ((R₀^d)^e * Real.exp (-((l+r : ℕ) : ℝ) * R₀^d))) := by
  let p := shortEdgeProbability μ d κ R₀
  have hp := tendsto_scaled_shortEdgeProbability hd hκ hR hμ
  have hlim := (hp.pow e).mul (tendsto_none_of_linear_tests hp (l+r) (l*r+e))
  refine hlim.congr' ?_
  filter_upwards [hfit, hcard] with n hn hc
  obtain ⟨hl, hr, he⟩ := hc
  change ((n : ℝ) * p n)^e * (1 - p n)^((l+r)*n-(l*r+e)) = _
  have hA : μ (Iic (R₀ / lengthScale d κ n)) = ENNReal.ofReal (p n) := by
    simp only [p, shortEdgeProbability, ofReal_cdf]
  have hp₀ : 0 ≤ p n := cdf_nonneg μ _
  have hp₁ : p n ≤ 1 := cdf_le_one μ _
  have hAc : μ (Iic (R₀ / lengthScale d κ n))ᶜ = ENNReal.ofReal (1 - p n) := by
    rw [prob_compl_eq_one_sub measurableSet_Iic, hA, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_sub _ hp₀]
  rw [measureReal_def, measure_labelledNeighborhoodEvent μ (L n) (R n) (E n) hn
    measurableSet_Iic (fun _ _ => MeasurableSet.univ), ENNReal.toReal_mul]
  simp only [Set.inter_univ, Finset.prod_const, hl, hr, he, Nat.sub_sub, hA, hAc,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hp₀, ENNReal.toReal_ofReal (sub_nonneg.mpr hp₁), mul_pow,
    mul_assoc]

end Certificate.LocalExploration

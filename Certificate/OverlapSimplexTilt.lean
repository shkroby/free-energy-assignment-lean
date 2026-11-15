import Certificate.OverlapSimplexBethe
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Uniform finite Bethe tilt bound

Each retained edge belongs to exactly one designated row. On rows with
three large stationary occupations, the quadratic entropy loss controls
every bounded edge test at once.
-/

open Finset
open scoped BigOperators

namespace Certificate.Overlap

variable {V E : Type*} [DecidableEq V] [DecidableEq E]

/-- The rows with three large edge occupancies. -/
noncomputable def goodRows (G : WeightedGraph V E) (rows : Finset V) (γ : E → ℝ)
    (η : ℝ) : Finset V := by
  classical
  exact rows.filter fun v => ThreeLargeOn (incidentEdges G v) γ η

omit [DecidableEq E] in
private theorem vertexL1_le_two {G : WeightedGraph V E} {γ p : E → ℝ}
    (hγ : Feasible G γ) (hp : Feasible G p) {v : V} (hv : v ∈ G.vertices) :
    vertexL1 G γ p v ≤ 2 := by
  have hLinear :
      ∑ e ∈ incidentEdges G v, |p e - γ e| ≤ ∑ e ∈ incidentEdges G v, (p e + γ e) := by
    apply Finset.sum_le_sum
    intro e he
    have he' := (mem_incidentEdges_iff (G := G)).mp he
    exact abs_le.mpr ⟨by linarith [hp.1 e he'.1], by linarith [hγ.1 e he'.1]⟩
  unfold vertexL1
  rw [Finset.sum_add_distrib] at hLinear
  have ha := hp.2 v hv
  have hb := hγ.2 v hv
  unfold vertexSlack at ha hb
  linarith only [hLinear, ha, hb]

omit [DecidableEq E] in
private theorem sum_vertexL1_rows (G : WeightedGraph V E) (rows : Finset V) (γ p : E → ℝ)
    (hRows : ∀ e ∈ G.edges, (rows ∩ G.ends e).card = 1) :
    (∑ v ∈ rows, vertexL1 G γ p v) = ∑ e ∈ G.edges, |p e - γ e| := by
  unfold vertexL1
  rw [sum_incident_comm]
  exact Finset.sum_congr rfl (fun e he => by simp [hRows e he])

omit [DecidableEq V] [DecidableEq E] in
private theorem linear_perturbation_le_l1 {G : WeightedGraph V E} {p γ f : E → ℝ}
    (hf : ∀ e ∈ G.edges, |f e| ≤ 1) (t : ℝ) :
    t * (∑ e ∈ G.edges, f e * p e) - t * (∑ e ∈ G.edges, f e * γ e) ≤
      |t| * ∑ e ∈ G.edges, |p e - γ e| := by
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro e he
  have hEq : t * (f e * p e) - t * (f e * γ e) = (t * f e) * (p e - γ e) := by ring
  rw [hEq]
  refine (le_abs_self _).trans ?_
  rw [abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (abs_nonneg t) (hf e he))
    (abs_nonneg _)

private theorem quadratic_tilt_bound (t L : ℝ) {η : ℝ} (hη : 0 < η) :
    |t| * L - (η/64) * L^2 ≤ 16*t^2/η := by
  apply (le_div_iff₀ hη).mpr
  have h : 16*t^2 - (|t| * L-(η/64)*L^2)*η = (η*L-32 * |t|)^2/64 := by
    calc
      _ = 16*|t|^2 - (|t| * L-(η/64)*L^2)*η := by rw [sq_abs]
      _ = _ := by ring
  have hn := div_nonneg (sq_nonneg (η*L-32 * |t|)) (by norm_num : (0 : ℝ) ≤ 64)
  rw [← h] at hn
  exact sub_nonneg.mp hn

/-- The tilted Bethe objective, compared to the unperturbed optimum,
satisfies the quantitative bound of the overlap lemma for every feasible
test occupation. The last factor counts rows with fewer than three
occupations of size at least eta. -/
theorem finiteBethe_perturbed_bound (G : WeightedGraph V E)
    {z η t : ℝ} {γ p f : E → ℝ} (rows : Finset V) (hRowsV : rows ⊆ G.vertices)
    (hRows : ∀ e ∈ G.edges, (rows ∩ G.ends e).card = 1)
    (hγ : Feasible G γ) (hp : Feasible G p) (hInt : ∀ e ∈ G.edges, γ e ∈ Set.Ioo (0 : ℝ) 1)
    (hSlack : ∀ v ∈ G.vertices, 0 < vertexSlack G γ v) (hstat : BetheStationary G z γ)
    (hη : 0 < η) (hf : ∀ e ∈ G.edges, |f e| ≤ 1) :
    finiteBethe G z p + t * (∑ e ∈ G.edges, f e * p e) - finiteBethe G z γ ≤
      t * (∑ e ∈ G.edges, f e * γ e) + (rows.card : ℝ) * (16*t^2/η) +
        ((rows \ goodRows G rows γ η).card : ℝ) * (2*|t|) := by
  classical
  let good := goodRows G rows γ η
  let bad := rows \ good
  let L := vertexL1 G γ p
  have hGood : good ⊆ rows := Finset.filter_subset _ _
  have hThree (v : V) (hv : v ∈ good) : ThreeLargeOn (incidentEdges G v) γ η :=
    (Finset.mem_filter.mp hv).2
  have hLoss := finiteBethe_stationary_loss G hγ hp hInt hSlack hstat hη.le
    good (hGood.trans hRowsV) hThree
  have hTilt := linear_perturbation_le_l1 (G := G) (p := p) (γ := γ) hf t
  rw [← sum_vertexL1_rows G rows γ p hRows] at hTilt
  have hRowSum : (∑ v ∈ good, L v) + ∑ v ∈ bad, L v = ∑ v ∈ rows, L v := by
    rw [add_comm]
    exact Finset.sum_sdiff hGood
  have hSplit : |t| * (∑ v ∈ rows, L v) - (η/64) * (∑ v ∈ good, L v^2) =
      (∑ v ∈ good, (|t| * L v-(η/64)*L v^2)) + ∑ v ∈ bad, |t| * L v := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← hRowSum]
    ring
  have hGoodBound :
      (∑ v ∈ good, (|t| * L v-(η/64)*L v^2)) ≤ (rows.card : ℝ)*(16*t^2/η) := by
    calc
      _ ≤ ∑ _ ∈ good, 16*t^2/η :=
        Finset.sum_le_sum fun v _ => quadratic_tilt_bound t (L v) hη
      _ = (good.card : ℝ)*(16*t^2/η) := by simp [nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Nat.cast_le.mpr (Finset.card_le_card hGood))
        (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hη.le)
  have hBadBound : (∑ v ∈ bad, |t| * L v) ≤ (bad.card : ℝ)*(2*|t|) := by
    calc
      _ ≤ ∑ _ ∈ bad, 2*|t| := by
        apply Finset.sum_le_sum
        intro v hv
        rw [mul_comm (2 : ℝ)]
        exact mul_le_mul_of_nonneg_left
          (vertexL1_le_two hγ hp (hRowsV (Finset.mem_sdiff.mp hv).1)) (abs_nonneg t)
      _ = _ := by simp [nsmul_eq_mul]
  change finiteBethe G z p ≤ finiteBethe G z γ - (η/64) * ∑ v ∈ good, L v^2 at hLoss
  change t * (∑ e ∈ G.edges, f e*p e) - t * (∑ e ∈ G.edges, f e*γ e) ≤
    |t| * ∑ v ∈ rows, L v at hTilt
  change _ ≤ _ + (bad.card : ℝ)*(2*|t|)
  linarith only [hLoss, hTilt, hSplit, hGoodBound, hBadBound]

/-- Taking the supremum over feasible occupations preserves the tilted
Bethe bound. This also gives the bound for any maximizer that attains it. -/
theorem finiteBethe_perturbed_sSup_bound (G : WeightedGraph V E)
    {z η t : ℝ} {γ f : E → ℝ} (rows : Finset V) (hRowsV : rows ⊆ G.vertices)
    (hRows : ∀ e ∈ G.edges, (rows ∩ G.ends e).card = 1)
    (hγ : Feasible G γ) (hInt : ∀ e ∈ G.edges, γ e ∈ Set.Ioo (0 : ℝ) 1)
    (hSlack : ∀ v ∈ G.vertices, 0 < vertexSlack G γ v) (hstat : BetheStationary G z γ)
    (hη : 0 < η) (hf : ∀ e ∈ G.edges, |f e| ≤ 1) :
    sSup ((fun p => finiteBethe G z p + t * (∑ e ∈ G.edges, f e * p e)) ''
        {p | Feasible G p}) - finiteBethe G z γ ≤
      t * (∑ e ∈ G.edges, f e * γ e) + (rows.card : ℝ) * (16*t^2/η) +
        ((rows \ goodRows G rows γ η).card : ℝ) * (2*|t|) := by
  apply sub_le_iff_le_add.mpr
  apply csSup_le (Set.Nonempty.image _ ⟨γ, hγ⟩)
  rintro _ ⟨p, hp, rfl⟩
  exact sub_le_iff_le_add.mp
    (finiteBethe_perturbed_bound G rows hRowsV hRows hγ hp hInt hSlack hstat hη hf)

omit [DecidableEq E] in
/-- A change of weights by an exponential tilt adds the linear tilt
to the finite graph Bethe objective. -/
theorem finiteBethe_eq_of_tilt (G G' : WeightedGraph V E) (z t : ℝ) (p f : E → ℝ)
    (hv : G'.vertices = G.vertices) (he : G'.edges = G.edges) (hends : G'.ends = G.ends)
    (hw : ∀ e ∈ G.edges, 0 < G.weight e)
    (hTilt : ∀ e ∈ G.edges, G'.weight e = G.weight e * Real.exp (t*f e)) :
    finiteBethe G' z p = finiteBethe G z p + t * ∑ e ∈ G.edges, f e * p e := by
  have hLogs (e : E) (he' : e ∈ G.edges) :
      Real.log (G'.weight e) = Real.log (G.weight e) + t*f e := by
    rw [hTilt e he', Real.log_mul (hw e he').ne' (Real.exp_pos _).ne', Real.log_exp]
  have hSlack (v : V) : vertexSlack G' p v = vertexSlack G p v := by
    unfold vertexSlack
    change 1 - (∑ e ∈ Tree.incident G'.ends G'.vertices G'.edges v, p e) =
      1 - ∑ e ∈ Tree.incident G.ends G.vertices G.edges v, p e
    rw [hv, he, hends]
  unfold finiteBethe
  rw [hv, he]
  simp_rw [hSlack]
  have hE : (∑ e ∈ G.edges, (p e * Real.log (G'.weight e) + betheAtom (p e))) =
      (∑ e ∈ G.edges, (p e * Real.log (G.weight e) + betheAtom (p e))) +
      ∑ e ∈ G.edges, t*(f e*p e) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun e h => by rw [hLogs e h]; ring)
  rw [hE, ← Finset.mul_sum]
  ring

end Certificate.Overlap

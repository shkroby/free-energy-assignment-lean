import Certificate.Tree
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Monomer pressure from local monomer probabilities

We integrate in log fugacity. The empty matching fixes the integration constant
at infinity, and the total edge weight supplies the integrable bound used to
pass from finite graphs to a limit of their average local monomer probabilities.
-/

open Finset Filter MeasureTheory Set
open scoped BigOperators Topology

namespace Certificate

/-- The graph data needed for finite pressure interpolation. -/
structure WeightedGraph (V E : Type*) where
  vertices : Finset V
  edges : Finset E
  ends : E → Finset V
  weight : E → ℝ
  weight_nonneg : ∀ e, 0 ≤ weight e
  ends_card : ∀ e ∈ edges, (ends e).card = 2
  ends_subset : ∀ e ∈ edges, ends e ⊆ vertices

namespace WeightedGraph

variable {V E : Type*} (G : WeightedGraph V E)

noncomputable section

/-- Edge activities when the monomer factor is `exp t`. -/
def activity (t : ℝ) (e : E) : ℝ := G.weight e * Real.exp (-2 * t)

theorem activity_nonneg (t : ℝ) (e : E) : 0 ≤ G.activity t e :=
  mul_nonneg (G.weight_nonneg e) (Real.exp_nonneg _)

theorem activity_eq_div (t : ℝ) :
    G.activity t = fun e => G.weight e / (Real.exp t) ^ 2 := by
  funext e
  rw [activity, div_eq_mul_inv, sq, ← Real.exp_add, ← Real.exp_neg]
  congr 2
  ring

/-- The empty matching has weight one in this normalization. -/
def Znormalized (t : ℝ) : ℝ := Tree.partition G.ends G.vertices G.edges (G.activity t)

theorem Znormalized_pos (t : ℝ) : 0 < G.Znormalized t :=
  zero_lt_one.trans_le (Tree.one_le_partition G.ends G.vertices G.edges _ (G.activity_nonneg t))

/-- The fugacity dependent partition function of the finite graph. -/
def Z (t : ℝ) : ℝ := Tree.monomerPartition G.ends G.vertices G.edges G.weight (Real.exp t)

theorem Z_pos (t : ℝ) : 0 < G.Z t :=
  Tree.monomerPartition_pos G.ends G.vertices G.edges G.weight (Real.exp_pos t) G.weight_nonneg

theorem Z_eq_normalized (t : ℝ) :
    G.Z t = (Real.exp t) ^ G.vertices.card * G.Znormalized t := by
  classical
  rw [Z, Znormalized, activity_eq_div, Tree.monomerPartition_eq_normalized
    G.ends G.vertices G.edges G.weight (Real.exp_pos t).ne' G.ends_card]

/-- Log partition with the empty-matching term subtracted. -/
def logCorrected (t : ℝ) : ℝ := Real.log (G.Z t) - (G.vertices.card : ℝ) * t

theorem logCorrected_eq (t : ℝ) : G.logCorrected t = Real.log (G.Znormalized t) := by
  rw [logCorrected, Z_eq_normalized, Real.log_mul (pow_ne_zero _ (Real.exp_pos t).ne')
    (G.Znormalized_pos t).ne', Real.log_pow, Real.log_exp, add_sub_cancel_left]

theorem logCorrected_bound (t : ℝ) :
    0 ≤ G.logCorrected t ∧ G.logCorrected t ≤ (∑ e ∈ G.edges, G.weight e) * Real.exp (-2 * t) := by
  classical
  have hempty : Tree.matchings G.ends G.vertices (∅ : Finset E) = {∅} := by
    ext M
    simp only [Tree.mem_matchings, subset_empty, Finset.mem_singleton]
    refine ⟨And.left, ?_⟩
    rintro rfl
    simp [Tree.IsMatching]
  have he : Tree.partition G.ends G.vertices ∅ (G.activity t) = 1 := by
    simp [Tree.partition, hempty]
  have h := Tree.log_partition_restore_edges_le G.ends G.vertices ∅ G.edges
    (by simp) (G.activity t) (G.activity_nonneg t) G.ends_subset
    (fun e he => card_pos.mp (by rw [G.ends_card e he]; decide))
  simpa [logCorrected_eq, Znormalized, he, activity, Finset.sum_mul] using h

theorem tendsto_logCorrected : Tendsto G.logCorrected atTop (𝓝 0) := by
  have ht : Tendsto (fun t : ℝ => -2 * t) atTop atBot := by
    simpa using tendsto_id.const_mul_atTop_of_neg (show (-2 : ℝ) < 0 by norm_num)
  have he := (Real.tendsto_exp_atBot.comp ht).const_mul (∑ e ∈ G.edges, G.weight e)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
    (fun t => (G.logCorrected_bound t).1) (fun t => (G.logCorrected_bound t).2)
  simpa using he

variable [DecidableEq V]

/-- Number of unmatched vertices in Gibbs expectation. -/
def monomerCount (t : ℝ) : ℝ := ∑ v ∈ G.vertices,
  Real.exp t * Tree.deletionRatio G.ends G.vertices G.edges G.weight (Real.exp t) v

/-- Number of matched vertices in Gibbs expectation. -/
def deficit (t : ℝ) : ℝ := (G.vertices.card : ℝ) - G.monomerCount t

theorem hasDerivAt_logCorrected (t : ℝ) :
    HasDerivAt G.logCorrected (-G.deficit t) t := by
  have hz := Tree.hasDerivAt_log_monomerPartition_eq_sum_ratios G.ends G.vertices G.edges
    G.weight G.weight_nonneg G.ends_card t
  have hl := (hasDerivAt_id t).const_mul (G.vertices.card : ℝ)
  change HasDerivAt (fun s => Real.log (G.Z s) - (G.vertices.card : ℝ) * s) (-G.deficit t) t
  simpa only [Z, deficit, monomerCount, id_eq, mul_one, neg_sub] using hz.fun_sub hl

omit [DecidableEq V] in
private theorem continuous_Z (vertices : Finset V) :
    Continuous (fun t : ℝ =>
      Tree.monomerPartition G.ends vertices G.edges G.weight (Real.exp t)) := by
  unfold Tree.monomerPartition
  fun_prop

theorem continuous_deficit : Continuous G.deficit := by
  have hc (v : V) : Continuous (fun t : ℝ => Real.exp t *
      Tree.deletionRatio G.ends G.vertices G.edges G.weight (Real.exp t) v) := by
    unfold Tree.deletionRatio
    exact Real.continuous_exp.mul ((G.continuous_Z (G.vertices.erase v)).div
      (G.continuous_Z G.vertices) (fun t => (G.Z_pos t).ne'))
  unfold deficit monomerCount
  exact continuous_const.sub (continuous_finsetSum _ (fun v _ => hc v))

theorem deficit_nonneg (t : ℝ) : 0 ≤ G.deficit t := by
  classical
  unfold deficit monomerCount
  apply sub_nonneg.mpr
  have h (v : V) (hv : v ∈ G.vertices) : Real.exp t *
      Tree.deletionRatio G.ends G.vertices G.edges G.weight (Real.exp t) v ≤ 1 := by
    have hle := (Tree.deletionRatio_pos_le G.ends G.edges G.weight G.weight_nonneg
      (Real.exp_pos t) G.ends_card hv).2
    calc
      _ ≤ Real.exp t * (Real.exp t)⁻¹ := mul_le_mul_of_nonneg_left hle (Real.exp_nonneg t)
      _ = 1 := mul_inv_cancel₀ (Real.exp_pos t).ne'
  simpa using (Finset.sum_le_sum h)

/-- Exact finite pressure identity with integration in log fugacity. -/
theorem logCorrected_eq_integral (t : ℝ) :
    G.logCorrected t = ∫ s in Ioi t, G.deficit s := by
  have hnonneg (s : ℝ) : 0 ≤ G.deficit s := G.deficit_nonneg s
  have hderiv (s : ℝ) : HasDerivAt (fun u => -G.logCorrected u) (G.deficit s) s := by
    simpa using (G.hasDerivAt_logCorrected s).fun_neg
  have htop : Tendsto (fun s => -G.logCorrected s) atTop (𝓝 0) := by
    simpa using G.tendsto_logCorrected.neg
  simpa using (integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun s _ => hderiv s) (fun s _ => hnonneg s) htop).symm

private theorem weighted_monomerCount (t : ℝ) :
    G.monomerCount t =
      (∑ M ∈ Tree.matchings G.ends G.vertices G.edges,
        ((G.vertices.card - 2 * M.card : ℕ) : ℝ) *
          ((Real.exp t) ^ (G.vertices.card - 2 * M.card) * ∏ e ∈ M, G.weight e)) / G.Z t := by
  rw [Tree.sum_weighted_unmatched G.ends G.vertices G.edges G.weight (Real.exp t) G.ends_card,
    div_eq_mul_inv, Finset.sum_mul, monomerCount]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Tree.deletionRatio, Z, div_eq_mul_inv, mul_assoc]

private theorem term_eq_normalized (t : ℝ) {M : Finset E}
    (hM : M ∈ Tree.matchings G.ends G.vertices G.edges) :
    (Real.exp t) ^ (G.vertices.card - 2 * M.card) * (∏ e ∈ M, G.weight e) =
      (Real.exp t) ^ G.vertices.card * (∏ e ∈ M, G.activity t e) := by
  obtain ⟨hsub, hMvalid⟩ := Tree.mem_matchings.mp hM
  have hcard := Tree.twice_card_le G.ends hMvalid fun e he => G.ends_card e (hsub he)
  rw [G.activity_eq_div, Finset.prod_div_distrib, Finset.prod_const, ← pow_mul,
    pow_sub₀ _ (Real.exp_pos t).ne' hcard]
  ring

private theorem weighted_deficit_normalized (t : ℝ) :
    G.deficit t =
      (∑ M ∈ Tree.matchings G.ends G.vertices G.edges,
        (2 * (M.card : ℝ)) * (∏ e ∈ M, G.activity t e)) / G.Znormalized t := by
  have hw :
      G.deficit t = (∑ M ∈ Tree.matchings G.ends G.vertices G.edges,
        (2 * (M.card : ℝ)) *
          ((Real.exp t) ^ (G.vertices.card - 2 * M.card) * ∏ e ∈ M, G.weight e)) / G.Z t := by
    rw [deficit, G.weighted_monomerCount]
    apply (eq_div_iff (G.Z_pos t).ne').mpr
    rw [sub_mul, div_mul_cancel₀ _ (G.Z_pos t).ne', Z, Tree.monomerPartition, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun M hM => ?_
    obtain ⟨hsub, hvalid⟩ := Tree.mem_matchings.mp hM
    rw [Nat.cast_sub (Tree.twice_card_le G.ends hvalid (fun e he => G.ends_card e (hsub he)))]
    push_cast
    ring
  have hnormal :
      (∑ M ∈ Tree.matchings G.ends G.vertices G.edges,
        (2 * (M.card : ℝ)) *
          ((Real.exp t) ^ (G.vertices.card - 2 * M.card) * ∏ e ∈ M, G.weight e)) =
      (Real.exp t) ^ G.vertices.card *
        (∑ M ∈ Tree.matchings G.ends G.vertices G.edges,
          (2 * (M.card : ℝ)) * (∏ e ∈ M, G.activity t e)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun M hM => ?_
    rw [G.term_eq_normalized t hM]
    ring
  rw [hw, hnormal, G.Z_eq_normalized, mul_div_mul_left _ _ (pow_ne_zero _ (Real.exp_pos t).ne')]

variable [DecidableEq E]

private theorem weighted_size_eq_sum_using_edge (t : ℝ) :
    (∑ M ∈ Tree.matchings G.ends G.vertices G.edges, (M.card : ℝ) * ∏ e ∈ M, G.activity t e) =
      ∑ e ∈ G.edges, G.activity t e *
        Tree.partition G.ends (G.vertices \ G.ends e) G.edges (G.activity t) := by
  let wt (M : Finset E) := ∏ e ∈ M, G.activity t e
  calc
    _ = ∑ M ∈ Tree.matchings G.ends G.vertices G.edges,
        ∑ e ∈ G.edges, if e ∈ M then wt M else 0 := by
      refine Finset.sum_congr rfl fun M hM => ?_
      have hs : G.edges.filter (fun e => e ∈ M) = M := by
        ext e
        simp only [mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨(Tree.mem_matchings.mp hM).1 h, h⟩⟩
      rw [← Finset.sum_filter, hs, sum_const, nsmul_eq_mul]
    _ = ∑ e ∈ G.edges, ∑ M ∈ Tree.matchings G.ends G.vertices G.edges,
        if e ∈ M then wt M else 0 := Finset.sum_comm
    _ = _ := by
      refine Finset.sum_congr rfl fun e he => ?_
      rw [← Finset.sum_filter]
      exact Tree.sum_using_edge he (G.ends_subset e he)
        (card_pos.mp (by rw [G.ends_card e he]; decide)) (G.activity t)

/-- The expected number of matched vertices is twice the sum of edge
occupation probabilities. Each probability comes from vertex deletion. -/
theorem deficit_eq_sum_edges (t : ℝ) :
    G.deficit t =
      2 * ∑ e ∈ G.edges,
        G.activity t e * (Tree.partition G.ends (G.vertices \ G.ends e) G.edges (G.activity t) /
          G.Znormalized t) := by
  rw [G.weighted_deficit_normalized]
  simp_rw [mul_assoc (2 : ℝ)]
  rw [← Finset.mul_sum, G.weighted_size_eq_sum_using_edge, mul_div_assoc,
    div_eq_mul_inv, Finset.sum_mul]
  apply congrArg ((2 : ℝ) * ·)
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [div_eq_mul_inv, mul_assoc]

/-- The deterministic exponential envelope with constant equal to the total
edge weight. -/
theorem deficit_le (t : ℝ) :
    G.deficit t ≤ 2 * (∑ e ∈ G.edges, G.weight e) * Real.exp (-2 * t) := by
  rw [G.deficit_eq_sum_edges, mul_assoc, Finset.sum_mul]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  refine Finset.sum_le_sum fun e _ => ?_
  apply mul_le_of_le_one_right (G.activity_nonneg t e)
  exact (div_le_one (G.Znormalized_pos t)).mpr
    (Tree.partition_mono_vertices G.ends sdiff_subset G.edges _ (G.activity_nonneg t))

omit [DecidableEq E] in
/-- The interpolated pressure normalized by the number of vertices in one
part of a balanced bipartite graph. -/
theorem pressure_eq_reference_add_integral (t mass : ℝ) (hmass : 0 < mass)
    (hcard : (G.vertices.card : ℝ) = 2 * mass) :
    Real.log (G.Z t) / mass = 2 * t + ∫ s in Ioi t, G.deficit s / mass := by
  rw [integral_div, ← G.logCorrected_eq_integral, logCorrected, hcard]
  field_simp
  ring

end

end WeightedGraph

section ExpectedPressure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {V E : ℕ → Type*} [∀ n, DecidableEq (V n)]
variable (G : ∀ n : ℕ, Ω → WeightedGraph (V n) (E n)) (mass : ℕ → ℝ)

/-- The expected pressure converges to the integral of the limiting local monomer
probabilities, provided their expected matched-vertex counts converge and the
average total edge weight is uniformly bounded. The variable `s` is log fugacity,
so the limiting integrand is `2 * (1 - m s)` when `m s` denotes the limiting
mean monomer probability. -/
theorem tendsto_expected_pressure_from_local_monomers
    (hmass : ∀ n, 0 < mass n)
    (hcard : ∀ n ω, ((G n ω).vertices.card : ℝ) = 2 * mass n)
    (hintWeight : ∀ n, Integrable (fun ω => ∑ e ∈ (G n ω).edges, (G n ω).weight e) μ)
    {C : ℝ}
    (hweight : ∀ n, (∫ ω, ∑ e ∈ (G n ω).edges, (G n ω).weight e ∂μ) ≤ C * mass n)
    (hmeas : ∀ n, Measurable (fun p : Ω × ℝ => (G n p.1).deficit p.2))
    (t : ℝ) (m : ℝ → ℝ)
    (hlocal : ∀ᵐ s ∂volume.restrict (Ioi t),
      Tendsto (fun n => ∫ ω, (G n ω).deficit s / mass n ∂μ) atTop (𝓝 (2 * (1 - m s)))) :
    Tendsto (fun n => ∫ ω, Real.log ((G n ω).Z t) / mass n ∂μ) atTop
      (𝓝 (2 * t + 2 * ∫ s in Ioi t, (1 - m s))) := by
  classical
  let ν : Measure ℝ := volume.restrict (Ioi t)
  let wt (n : ℕ) (ω : Ω) := ∑ e ∈ (G n ω).edges, (G n ω).weight e
  let f (n : ℕ) (ω : Ω) (s : ℝ) := (G n ω).deficit s / mass n
  have hexp : Integrable (fun s : ℝ => Real.exp (-2 * s)) ν :=
    integrableOn_exp_mul_Ioi (show (-2 : ℝ) < 0 by norm_num) t
  have hmeas_f (n : ℕ) : Measurable (Function.uncurry (f n)) :=
    (hmeas n).div_const _
  have hnorm (n : ℕ) (ω : Ω) (s : ℝ) :
      ‖f n ω s‖ ≤ (2 / mass n * wt n ω) * Real.exp (-2 * s) := by
    rw [Real.norm_of_nonneg (div_nonneg ((G n ω).deficit_nonneg s) (hmass n).le)]
    apply (div_le_iff₀ (hmass n)).mpr
    have h := (G n ω).deficit_le s
    calc
      _ ≤ 2 * wt n ω * Real.exp (-2 * s) := h
      _ = (2 / mass n * wt n ω * Real.exp (-2 * s)) * mass n := by
        field_simp [(hmass n).ne']
  have hjoint (n : ℕ) : Integrable (Function.uncurry (f n)) (μ.prod ν) :=
    (((hintWeight n).const_mul (2 / mass n)).mul_prod hexp).mono'
      (hmeas_f n).aestronglyMeasurable (.of_forall fun p => hnorm n p.1 p.2)
  have hpoint (n : ℕ) (s : ℝ) :
      ‖∫ ω, f n ω s ∂μ‖ ≤ 2 * C * Real.exp (-2 * s) := by
    calc
      _ ≤ ∫ ω, (2 / mass n * wt n ω) * Real.exp (-2 * s) ∂μ :=
        norm_integral_le_of_norm_le (((hintWeight n).const_mul _).mul_const _)
          (.of_forall fun ω => hnorm n ω s)
      _ = (2 / mass n * ∫ ω, wt n ω ∂μ) * Real.exp (-2 * s) := by
        rw [integral_mul_const, integral_const_mul]
      _ ≤ 2 * C * Real.exp (-2 * s) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        calc
          _ ≤ 2 / mass n * (C * mass n) :=
            mul_le_mul_of_nonneg_left (hweight n) (div_nonneg (by norm_num) (hmass n).le)
          _ = 2 * C := by field_simp [(hmass n).ne']
  have hfinite (n : ℕ) :
      (∫ ω, Real.log ((G n ω).Z t) / mass n ∂μ) =
        2 * t + ∫ s, ∫ ω, f n ω s ∂μ ∂ν := by
    simp_rw [(G n _).pressure_eq_reference_add_integral t (mass n) (hmass n) (hcard n _)]
    change (∫ ω, 2 * t + ∫ s, f n ω s ∂ν ∂μ) = _
    have hfint : Integrable (fun ω => ∫ s, f n ω s ∂ν) μ := (hjoint n).integral_prod_left
    rw [integral_add (integrable_const _) hfint, integral_integral_swap (hjoint n), integral_const]
    simp
  have hdc := tendsto_integral_of_dominated_convergence (μ := ν)
    (fun s : ℝ => 2 * C * Real.exp (-2 * s))
    (fun n => (hjoint n).integral_prod_right.aestronglyMeasurable)
    (hexp.const_mul _) (fun n => .of_forall (hpoint n)) hlocal
  simp_rw [hfinite]
  rw [← integral_const_mul]
  exact hdc.const_add (2 * t)

/-- The same pressure formula in the monomer fugacity variable, with the
`du / u` integration measure from the manuscript. -/
theorem tendsto_expected_pressure_from_local_monomers_fugacity
    (hmass : ∀ n, 0 < mass n)
    (hcard : ∀ n ω, ((G n ω).vertices.card : ℝ) = 2 * mass n)
    (hintWeight : ∀ n, Integrable (fun ω => ∑ e ∈ (G n ω).edges, (G n ω).weight e) μ)
    {C : ℝ}
    (hweight : ∀ n, (∫ ω, ∑ e ∈ (G n ω).edges, (G n ω).weight e ∂μ) ≤ C * mass n)
    (hmeas : ∀ n, Measurable (fun p : Ω × ℝ => (G n p.1).deficit p.2))
    {z : ℝ} (hz : 0 < z) (m : ℝ → ℝ)
    (hlocal : ∀ᵐ s ∂volume.restrict (Ioi (Real.log z)),
      Tendsto (fun n => ∫ ω, (G n ω).deficit s / mass n ∂μ) atTop
        (𝓝 (2 * (1 - m (Real.exp s))))) :
    Tendsto (fun n => ∫ ω,
      Real.log (Tree.monomerPartition (G n ω).ends (G n ω).vertices (G n ω).edges
        (G n ω).weight z) / mass n ∂μ) atTop
      (𝓝 (2 * Real.log z + 2 * ∫ u in Ioi z, (1 - m u) / u)) := by
  have h := tendsto_expected_pressure_from_local_monomers
    G mass hmass hcard hintWeight hweight hmeas (Real.log z) (m ∘ Real.exp) hlocal
  have heq :
      (∫ u in Ioi z, (1 - m u) / u) = ∫ s in Ioi (Real.log z), 1 - m (Real.exp s) := by
    have hs := integral_comp_log_Ioi (fun s : ℝ => 1 - m (Real.exp s)) hz
    refine Eq.trans ?_ hs
    refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
    have hu₀ := hz.trans (show z < u from hu)
    rw [Real.exp_log hu₀, smul_eq_mul, div_eq_inv_mul]
  rw [heq]
  simpa only [WeightedGraph.Z, Real.exp_log hz, Function.comp_apply] using h

end ExpectedPressure
end Certificate

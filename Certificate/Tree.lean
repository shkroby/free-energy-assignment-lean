import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Finite matching partition functions

Edges are indexed by a finite set, with a two-element endpoint set for each edge.
This model includes finite bipartite graphs by assigning each pair of opposite-type
vertices its own edge index. Distinct edge indices are allowed to have the same
endpoints; such edges cannot appear together in a matching.
-/

open scoped BigOperators
open Finset

namespace Certificate.Tree

variable {V E : Type*} [DecidableEq V] [DecidableEq E]

/-- A matching supported on a vertex set, with no common endpoints among its edges. -/
def IsMatching (ends : E → Finset V) (vertices : Finset V) (M : Finset E) : Prop :=
  (∀ e ∈ M, ends e ⊆ vertices) ∧
    ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint (ends e) (ends f)

noncomputable section

/-- The finite family of matchings whose edges belong to the given edge set. -/
def matchings (ends : E → Finset V) (vertices : Finset V) (edges : Finset E) :
    Finset (Finset E) := by
  classical
  exact edges.powerset.filter (IsMatching ends vertices)

omit [DecidableEq V] [DecidableEq E] in
@[simp] theorem mem_matchings {ends : E → Finset V} {vertices : Finset V}
    {edges M : Finset E} :
    M ∈ matchings ends vertices edges ↔ M ⊆ edges ∧ IsMatching ends vertices M := by
  simp [matchings]

omit [DecidableEq V] [DecidableEq E] in
theorem matching_empty (ends : E → Finset V) (vertices : Finset V) (edges : Finset E) :
    ∅ ∈ matchings ends vertices edges := by
  simp [IsMatching]

/-- The matching polynomial in the edge activities. For monomer factor `z > 0`,
use activity `w e / z ^ 2` and multiply by `z ^ vertices.card`. -/
def partition (ends : E → Finset V) (vertices : Finset V) (edges : Finset E)
    (activity : E → ℝ) : ℝ :=
  ∑ M ∈ matchings ends vertices edges, ∏ e ∈ M, activity e

omit [DecidableEq V] [DecidableEq E] in
theorem one_le_partition (ends : E → Finset V) (vertices : Finset V) (edges : Finset E)
    (activity : E → ℝ) (ha : ∀ e, 0 ≤ activity e) :
    1 ≤ partition ends vertices edges activity := by
  simpa [partition] using
    (Finset.single_le_sum
      (f := fun M : Finset E => ∏ e ∈ M, activity e)
      (fun M _ => Finset.prod_nonneg fun e _ => ha e)
      (matching_empty ends vertices edges))

/-- Incident edges with both endpoints in the current graph. -/
def incident (ends : E → Finset V) (vertices : Finset V) (edges : Finset E)
    (v : V) : Finset E :=
  edges.filter fun e => v ∈ ends e ∧ ends e ⊆ vertices

private theorem insert_mem_matchings_iff {ends : E → Finset V} {vertices : Finset V}
    {edges M : Finset E} {e : E} (he : e ∈ edges) (hv : ends e ⊆ vertices)
    (heM : e ∉ M) :
    insert e M ∈ matchings ends vertices edges ↔
      M ∈ matchings ends (vertices \ ends e) edges := by
  simp only [mem_matchings]
  constructor
  · rintro ⟨hsub, hcontained, hd⟩
    refine ⟨fun f hf => hsub (mem_insert_of_mem hf), ?_, ?_⟩
    · intro f hf x hx
      have hdisj := hd f (mem_insert_of_mem hf) e (mem_insert_self e M)
        (fun h => heM (h ▸ hf))
      exact mem_sdiff.mpr ⟨hcontained f (mem_insert_of_mem hf) hx, disjoint_left.mp hdisj hx⟩
    · exact fun f hf g hg hfg => hd f (mem_insert_of_mem hf) g (mem_insert_of_mem hg) hfg
  · rintro ⟨hsub, hcontained, hd⟩
    refine ⟨insert_subset he hsub, ?_, ?_⟩
    · intro f hf
      rcases mem_insert.mp hf with rfl | hf
      · exact hv
      · exact fun _ hx => (mem_sdiff.mp (hcontained f hf hx)).1
    · intro f hf g hg hfg
      rcases mem_insert.mp hf with hfe | hf
      · rw [hfe]
        rcases mem_insert.mp hg with hge | hg
        · exact (hfg (hfe.trans hge.symm)).elim
        · exact (disjoint_left.mpr fun _ hx => (mem_sdiff.mp (hcontained g hg hx)).2).symm
      · rcases mem_insert.mp hg with hge | hg
        · rw [hge]
          exact disjoint_left.mpr fun _ hx => (mem_sdiff.mp (hcontained f hf hx)).2
        · exact hd f hf g hg hfg

omit [DecidableEq E] in
private theorem not_mem_matching_after_delete_ends {ends : E → Finset V}
    {vertices : Finset V} {edges M : Finset E} {e : E}
    (he : (ends e).Nonempty) (hM : M ∈ matchings ends (vertices \ ends e) edges) :
    e ∉ M := by
  intro h
  obtain ⟨v, hv⟩ := he
  exact (mem_sdiff.mp ((mem_matchings.mp hM).2.1 e h hv)).2 hv

/-- Matchings using a designated edge are obtained by adjoining it to a matching
after deleting its two endpoints. -/
theorem using_edge_eq_image {ends : E → Finset V} {vertices : Finset V}
    {edges : Finset E} {e : E} (he : e ∈ edges) (hv : ends e ⊆ vertices)
    (he_ne : (ends e).Nonempty) :
    (matchings ends vertices edges).filter (fun M => e ∈ M) =
      (matchings ends (vertices \ ends e) edges).image (insert e) := by
  ext M
  constructor
  · intro hM
    obtain ⟨hM, heM⟩ := mem_filter.mp hM
    refine mem_image.mpr ⟨M.erase e, ?_, insert_erase heM⟩
    exact (insert_mem_matchings_iff he hv (notMem_erase e M)).mp (by
      simpa only [insert_erase heM] using hM)
  · intro hM
    obtain ⟨N, hN, rfl⟩ := mem_image.mp hM
    exact mem_filter.mpr
      ⟨(insert_mem_matchings_iff he hv
        (not_mem_matching_after_delete_ends he_ne hN)).mpr hN, mem_insert_self e N⟩

theorem sum_using_edge {ends : E → Finset V} {vertices : Finset V} {edges : Finset E}
    {e : E} (he : e ∈ edges) (hv : ends e ⊆ vertices) (he_ne : (ends e).Nonempty)
    (activity : E → ℝ) :
    (∑ M ∈ (matchings ends vertices edges).filter (fun M => e ∈ M),
        ∏ f ∈ M, activity f) =
      activity e * partition ends (vertices \ ends e) edges activity := by
  rw [using_edge_eq_image he hv he_ne, Finset.sum_image, partition, Finset.mul_sum]
  · exact Finset.sum_congr rfl (fun M hM =>
      Finset.prod_insert (not_mem_matching_after_delete_ends he_ne hM))
  · intro M hM N hN h
    have hh := congrArg (fun P : Finset E => P.erase e) h
    simpa only [erase_insert (not_mem_matching_after_delete_ends he_ne hM),
      erase_insert (not_mem_matching_after_delete_ends he_ne hN)] using hh

omit [DecidableEq E] in
theorem no_edge_at_iff_after_delete {ends : E → Finset V} {vertices : Finset V}
    {edges M : Finset E} {v : V} :
    M ∈ matchings ends (vertices.erase v) edges ↔
      M ∈ matchings ends vertices edges ∧ (∀ e ∈ M, v ∉ ends e) := by
  simp only [mem_matchings, IsMatching]
  constructor
  · rintro ⟨hsub, hcontained, hdisj⟩
    exact ⟨⟨hsub, fun e he _ hx => (mem_erase.mp (hcontained e he hx)).2, hdisj⟩,
      fun e he hx => (mem_erase.mp (hcontained e he hx)).1 rfl⟩
  · rintro ⟨⟨hsub, hcontained, hdisj⟩, hnom⟩
    exact ⟨hsub, fun e he _ hx => mem_erase.mpr ⟨fun h => hnom e he (h ▸ hx),
      hcontained e he hx⟩, hdisj⟩

/-- Exact vertex-deletion recurrence in the matching polynomial normalization. -/
theorem partition_vertex_deletion (ends : E → Finset V) (vertices : Finset V)
    (edges : Finset E) (activity : E → ℝ) (v : V) :
    partition ends vertices edges activity =
      partition ends (vertices.erase v) edges activity +
        ∑ e ∈ incident ends vertices edges v,
          activity e * partition ends (vertices \ ends e) edges activity := by
  classical
  let used : Finset E → Prop := fun M => ∃ e ∈ M, v ∈ ends e
  let family : E → Finset (Finset E) := fun e =>
    (matchings ends vertices edges).filter (fun M => e ∈ M)
  have hu :
      (matchings ends vertices edges).filter used =
        (incident ends vertices edges v).biUnion family := by
    ext M
    constructor
    · intro hM
      obtain ⟨hM, e, heM, hv⟩ := mem_filter.mp hM
      exact mem_biUnion.mpr ⟨e, mem_filter.mpr
        ⟨(mem_matchings.mp hM).1 heM, hv, (mem_matchings.mp hM).2.1 e heM⟩,
        mem_filter.mpr ⟨hM, heM⟩⟩
    · intro hM
      obtain ⟨e, hinc, hM⟩ := mem_biUnion.mp hM
      exact mem_filter.mpr ⟨(mem_filter.mp hM).1, e, (mem_filter.mp hM).2,
        (mem_filter.mp hinc).2.1⟩
  have hun :
      (matchings ends vertices edges).filter (fun M => ¬ used M) =
        matchings ends (vertices.erase v) edges := by
    ext M
    simp only [mem_filter, no_edge_at_iff_after_delete, used, not_exists, not_and]
  have hd : (↑(incident ends vertices edges v) : Set E).PairwiseDisjoint family := by
    intro e he f hf hne
    refine disjoint_left.mpr fun M heM hfM => ?_
    have hM := (mem_matchings.mp (mem_filter.mp heM).1).2
    exact disjoint_left.mp (hM.2 e (mem_filter.mp heM).2 f (mem_filter.mp hfM).2 hne)
      (mem_filter.mp he).2.1 (mem_filter.mp hf).2.1
  unfold partition
  rw [← Finset.sum_filter_add_sum_filter_not _ used, hu, hun, Finset.sum_biUnion hd, add_comm]
  refine congrArg (fun p : ℝ =>
    (∑ M ∈ matchings ends (vertices.erase v) edges, ∏ e ∈ M, activity e) + p) ?_
  apply Finset.sum_congr rfl
  intro e he
  exact sum_using_edge (mem_filter.mp he).1 (mem_filter.mp he).2.2
    ⟨v, (mem_filter.mp he).2.1⟩ activity

omit [DecidableEq E] in
/-- The number of occupied vertices is exactly twice the matching size. -/
theorem card_occupied (ends : E → Finset V) {vertices : Finset V} {M : Finset E}
    (hM : IsMatching ends vertices M) (hends : ∀ e ∈ M, (ends e).card = 2) :
    (M.biUnion ends).card = 2 * M.card := by
  rw [Finset.card_biUnion (s := M) (t := ends)]
  · calc
      (∑ e ∈ M, (ends e).card) = ∑ _e ∈ M, 2 :=
        Finset.sum_congr rfl hends
      _ = 2 * M.card := by simp [Nat.mul_comm]
  · intro e he f hf hne
    exact hM.2 e he f hf hne

omit [DecidableEq E] in
theorem twice_card_le (ends : E → Finset V) {vertices : Finset V} {M : Finset E}
    (hM : IsMatching ends vertices M) (hends : ∀ e ∈ M, (ends e).card = 2) :
    2 * M.card ≤ vertices.card := by
  rw [← card_occupied ends hM hends]
  apply Finset.card_le_card
  intro v hv
  obtain ⟨e, he, hv⟩ := mem_biUnion.mp hv
  exact hM.1 e he hv

/-- The manuscript's partition function, with one factor of `z` per unmatched vertex. -/
def monomerPartition (ends : E → Finset V) (vertices : Finset V) (edges : Finset E)
    (w : E → ℝ) (z : ℝ) : ℝ :=
  ∑ M ∈ matchings ends vertices edges, z ^ (vertices.card - 2 * M.card) * ∏ e ∈ M, w e

omit [DecidableEq E] in
theorem monomerPartition_eq_normalized (ends : E → Finset V) (vertices : Finset V)
    (edges : Finset E) (w : E → ℝ) {z : ℝ} (hz : z ≠ 0)
    (hends : ∀ e ∈ edges, (ends e).card = 2) :
    monomerPartition ends vertices edges w z =
      z ^ vertices.card * partition ends vertices edges (fun e => w e / z ^ 2) := by
  rw [monomerPartition, partition, Finset.mul_sum]
  refine Finset.sum_congr rfl fun M hM => ?_
  obtain ⟨hsub, hMvalid⟩ := mem_matchings.mp hM
  have hcard := twice_card_le ends hMvalid fun e he => hends e (hsub he)
  rw [Finset.prod_div_distrib, Finset.prod_const, ← pow_mul, pow_sub₀ z hz hcard]
  ring

omit [DecidableEq V] [DecidableEq E] in
theorem monomerPartition_pos (ends : E → Finset V) (vertices : Finset V)
    (edges : Finset E) (w : E → ℝ) {z : ℝ} (hz : 0 < z)
    (hw : ∀ e, 0 ≤ w e) :
    0 < monomerPartition ends vertices edges w z := by
  have h :=
    Finset.single_le_sum
      (f := fun M : Finset E =>
        z ^ (vertices.card - 2 * M.card) * ∏ e ∈ M, w e)
      (fun M _ => mul_nonneg (pow_nonneg hz.le _) (Finset.prod_nonneg fun e _ => hw e))
      (matching_empty ends vertices edges)
  exact (pow_pos hz _).trans_le (by simpa [monomerPartition] using h)

/-- Exact vertex-deletion recurrence for the manuscript's partition function. -/
theorem monomerPartition_vertex_deletion (ends : E → Finset V) {vertices : Finset V}
    (edges : Finset E) (w : E → ℝ) {z : ℝ} (hz : 0 < z)
    (hends : ∀ e ∈ edges, (ends e).card = 2) {v : V} (hv : v ∈ vertices) :
    monomerPartition ends vertices edges w z =
      z * monomerPartition ends (vertices.erase v) edges w z +
        ∑ e ∈ incident ends vertices edges v,
          w e * monomerPartition ends (vertices \ ends e) edges w z := by
  simp_rw [monomerPartition_eq_normalized ends _ edges w hz.ne' hends]
  rw [partition_vertex_deletion ends vertices edges _ v, mul_add, Finset.mul_sum]
  congr 1
  · have hpow : z ^ vertices.card = z * z ^ (vertices.erase v).card := by
      rw [← pow_succ', card_erase_add_one hv]
    rw [hpow, mul_assoc]
  · refine Finset.sum_congr rfl fun e hinc => ?_
    obtain ⟨he, _, hevs⟩ := mem_filter.mp hinc
    have hcard : (vertices \ ends e).card + 2 = vertices.card := by
      simpa [hends e he] using card_sdiff_add_card_eq_card hevs
    have hpow : z ^ vertices.card = z ^ (vertices \ ends e).card * z ^ 2 := by
      rw [← pow_add, hcard]
    rw [hpow]
    field_simp

omit [DecidableEq V] [DecidableEq E] in
theorem partition_mono_vertices (ends : E → Finset V) {vertices larger : Finset V}
    (h : vertices ⊆ larger) (edges : Finset E) (activity : E → ℝ)
    (ha : ∀ e, 0 ≤ activity e) :
    partition ends vertices edges activity ≤ partition ends larger edges activity := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro M hM
    obtain ⟨hsub, hcontained, hdisj⟩ := mem_matchings.mp hM
    exact mem_matchings.mpr ⟨hsub, fun e he => (hcontained e he).trans h, hdisj⟩
  · exact fun M _ _ => Finset.prod_nonneg fun e _ => ha e

/-- Inserting an edge modifies the partition by the weight of matchings using it. -/
theorem partition_insert_edge (ends : E → Finset V) (vertices : Finset V)
    {edges : Finset E} (activity : E → ℝ) {e : E} (he : e ∉ edges)
    (hevs : ends e ⊆ vertices) (hene : (ends e).Nonempty) :
    partition ends vertices (insert e edges) activity =
      partition ends vertices edges activity +
        activity e * partition ends (vertices \ ends e) edges activity := by
  classical
  have hno :
      (matchings ends vertices (insert e edges)).filter (fun M => e ∉ M) =
        matchings ends vertices edges := by
    ext M
    simp only [mem_filter, mem_matchings]
    constructor
    · rintro ⟨⟨hsub, hM⟩, heM⟩
      exact ⟨fun f hf => (mem_insert.mp (hsub hf)).resolve_left
        (fun h => heM (h ▸ hf)), hM⟩
    · rintro ⟨hsub, hM⟩
      exact ⟨⟨fun f hf => mem_insert_of_mem (hsub hf), hM⟩, fun h => he (hsub h)⟩
  have hdel :
      matchings ends (vertices \ ends e) (insert e edges) =
        matchings ends (vertices \ ends e) edges := by
    ext M
    constructor
    · intro hM
      have heM := not_mem_matching_after_delete_ends hene hM
      obtain ⟨hsub, hM⟩ := mem_matchings.mp hM
      exact mem_matchings.mpr ⟨fun f hf => (mem_insert.mp (hsub hf)).resolve_left
        (fun h => heM (h ▸ hf)), hM⟩
    · intro hM
      exact mem_matchings.mpr ⟨fun f hf => mem_insert_of_mem ((mem_matchings.mp hM).1 hf),
        (mem_matchings.mp hM).2⟩
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (matchings ends vertices (insert e edges)) (fun M => e ∈ M)
    (fun M => ∏ f ∈ M, activity f)
  rw [show partition ends vertices (insert e edges) activity = _ from hsplit.symm,
    hno, sum_using_edge (mem_insert_self e edges) hevs hene, add_comm]
  congr 2
  simp only [partition, hdel]

/-- A single edge with nonnegative weight changes the log partition by at most
its activity. In the monomer normalization the activity is `w / z ^ 2`. -/
theorem log_partition_insert_edge_le (ends : E → Finset V) (vertices : Finset V)
    {edges : Finset E} (activity : E → ℝ) (ha : ∀ e, 0 ≤ activity e)
    {e : E} (he : e ∉ edges) (hevs : ends e ⊆ vertices) (hene : (ends e).Nonempty) :
    0 ≤ Real.log (partition ends vertices (insert e edges) activity) -
        Real.log (partition ends vertices edges activity) ∧
      Real.log (partition ends vertices (insert e edges) activity) -
        Real.log (partition ends vertices edges activity) ≤ activity e := by
  let A := partition ends vertices edges activity
  let B := partition ends (vertices \ ends e) edges activity
  have hA : 0 < A :=
    zero_lt_one.trans_le (one_le_partition ends vertices edges activity ha)
  have hB : 0 ≤ B :=
    zero_le_one.trans (one_le_partition ends (vertices \ ends e) edges activity ha)
  have hBA : B ≤ A := partition_mono_vertices ends sdiff_subset edges activity ha
  rw [partition_insert_edge ends vertices activity he hevs hene]
  change 0 ≤ Real.log (A + activity e * B) - Real.log A ∧
    Real.log (A + activity e * B) - Real.log A ≤ activity e
  have hpos : 0 < A + activity e * B :=
    add_pos_of_pos_of_nonneg hA (mul_nonneg (ha e) hB)
  rw [← Real.log_div hpos.ne' hA.ne']
  have hquot : (A + activity e * B) / A = 1 + activity e * (B / A) := by
    rw [add_div, div_self hA.ne', mul_div_assoc]
  rw [hquot]
  have hnonneg : 0 ≤ activity e * (B / A) :=
    mul_nonneg (ha e) (div_nonneg hB hA.le)
  constructor
  · exact Real.log_nonneg (le_add_of_nonneg_right hnonneg)
  · have le_log := Real.log_le_sub_one_of_pos (add_pos_of_pos_of_nonneg zero_lt_one hnonneg)
    have hprod : activity e * (B / A) ≤ activity e :=
      mul_le_of_le_one_right (ha e) ((div_le_one hA).mpr hBA)
    linarith only [le_log, hprod]

omit [DecidableEq V] [DecidableEq E] in
/-- The matching polynomial's logarithmic derivative with respect to the monomer
factor counts unmatched vertices. The weighted count in the numerator is over
the same matching family as the partition. -/
theorem hasDerivAt_log_monomerPartition (ends : E → Finset V)
    (vertices : Finset V) (edges : Finset E) (w : E → ℝ)
    (hw : ∀ e, 0 ≤ w e) (t : ℝ) :
    HasDerivAt (fun s => Real.log (monomerPartition ends vertices edges w (Real.exp s)))
      ((∑ M ∈ matchings ends vertices edges,
          ((vertices.card - 2 * M.card : ℕ) : ℝ) *
            ((Real.exp t) ^ (vertices.card - 2 * M.card) * ∏ e ∈ M, w e)) /
        monomerPartition ends vertices edges w (Real.exp t)) t := by
  have hsum : HasDerivAt (fun s => monomerPartition ends vertices edges w (Real.exp s))
      (∑ M ∈ matchings ends vertices edges,
        ((vertices.card - 2 * M.card : ℕ) : ℝ) *
          ((Real.exp t) ^ (vertices.card - 2 * M.card) * ∏ e ∈ M, w e)) t := by
    unfold monomerPartition
    apply HasDerivAt.fun_sum
    intro M _
    let k := vertices.card - 2 * M.card
    have h := ((Real.hasDerivAt_exp t).pow k).mul_const (∏ e ∈ M, w e)
    refine h.congr_deriv ?_
    change _ = (k : ℝ) * ((Real.exp t) ^ k * ∏ e ∈ M, w e)
    cases k with
    | zero => simp
    | succ k =>
        simp only [Nat.succ_sub_one, pow_succ]
        ring
  exact hsum.log (monomerPartition_pos ends vertices edges w (Real.exp_pos t) hw).ne'

omit [DecidableEq E] in
/-- At zero monomer factor only matchings that cover every vertex survive. -/
theorem monomerPartition_zero (ends : E → Finset V) (vertices : Finset V)
    (edges : Finset E) (w : E → ℝ) (hends : ∀ e ∈ edges, (ends e).card = 2) :
    monomerPartition ends vertices edges w 0 =
      ∑ M ∈ (matchings ends vertices edges).filter (fun M => M.biUnion ends = vertices),
        ∏ e ∈ M, w e := by
  rw [monomerPartition, Finset.sum_filter]
  refine Finset.sum_congr rfl fun M hM => ?_
  obtain ⟨hsub, hMvalid⟩ := mem_matchings.mp hM
  have hocc := card_occupied ends hMvalid (fun e he => hends e (hsub he))
  have hcontained : M.biUnion ends ⊆ vertices := by
    intro v hv
    obtain ⟨e, he, hv⟩ := mem_biUnion.mp hv
    exact hMvalid.1 e he hv
  by_cases hfull : M.biUnion ends = vertices
  · have hcard : vertices.card = 2 * M.card := hfull ▸ hocc
    simp [hfull, hcard]
  · have hlt : 2 * M.card < vertices.card := by
      rw [← hocc]
      exact Finset.card_lt_card (ssubset_of_subset_of_ne hcontained hfull)
    rw [if_neg hfull, zero_pow (Nat.sub_ne_zero_iff_lt.mpr hlt), zero_mul]

/-- The cavity message is the partition function after removing a root,
divided by the full partition function. -/
def deletionRatio (ends : E → Finset V) (vertices : Finset V) (edges : Finset E)
    (w : E → ℝ) (z : ℝ) (v : V) : ℝ :=
  monomerPartition ends (vertices.erase v) edges w z /
    monomerPartition ends vertices edges w z

/-- The finite cavity recursion, indexed by the edges incident to the root.
Each child numerator deletes both ends of its edge. -/
theorem deletionRatio_recursion (ends : E → Finset V) {vertices : Finset V}
    (edges : Finset E) (w : E → ℝ) (hw : ∀ e, 0 ≤ w e) {z : ℝ} (hz : 0 < z)
    (hends : ∀ e ∈ edges, (ends e).card = 2) {v : V} (hv : v ∈ vertices) :
    deletionRatio ends vertices edges w z v =
      (z + ∑ e ∈ incident ends vertices edges v,
        w e * (monomerPartition ends (vertices \ ends e) edges w z /
          monomerPartition ends (vertices.erase v) edges w z))⁻¹ := by
  unfold deletionRatio
  rw [← inv_div]
  congr 1
  apply (div_eq_iff (monomerPartition_pos ends (vertices.erase v) edges w hz hw).ne').mpr
  rw [monomerPartition_vertex_deletion ends edges w hz hends hv, add_mul, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [mul_assoc, div_mul_cancel₀ _ (monomerPartition_pos ends (vertices.erase v) edges w hz hw).ne']

/-- Nonnegative edge weights give a positive cavity message bounded by `1/z`. -/
theorem deletionRatio_pos_le (ends : E → Finset V) {vertices : Finset V}
    (edges : Finset E) (w : E → ℝ) (hw : ∀ e, 0 ≤ w e) {z : ℝ} (hz : 0 < z)
    (hends : ∀ e ∈ edges, (ends e).card = 2) {v : V} (hv : v ∈ vertices) :
    0 < deletionRatio ends vertices edges w z v ∧
      deletionRatio ends vertices edges w z v ≤ z⁻¹ := by
  refine ⟨div_pos (monomerPartition_pos ends (vertices.erase v) edges w hz hw)
    (monomerPartition_pos ends vertices edges w hz hw), ?_⟩
  rw [deletionRatio_recursion ends edges w hw hz hends hv]
  apply inv_anti₀ hz
  refine le_add_of_nonneg_right (sum_nonneg fun e _ => mul_nonneg (hw e) ?_)
  exact div_nonneg (monomerPartition_pos ends (vertices \ ends e) edges w hz hw).le
    (monomerPartition_pos ends (vertices.erase v) edges w hz hw).le

/-- Restoring any set of omitted edges changes the logarithm of the normalized
partition by at most the total restored activity. -/
theorem log_partition_restore_edges_le (ends : E → Finset V) (vertices : Finset V)
    (kept removed : Finset E) (hdisj : Disjoint kept removed)
    (activity : E → ℝ) (ha : ∀ e, 0 ≤ activity e)
    (hv : ∀ e ∈ removed, ends e ⊆ vertices)
    (hene : ∀ e ∈ removed, (ends e).Nonempty) :
    0 ≤ Real.log (partition ends vertices (kept ∪ removed) activity) -
        Real.log (partition ends vertices kept activity) ∧
      Real.log (partition ends vertices (kept ∪ removed) activity) -
        Real.log (partition ends vertices kept activity) ≤ ∑ e ∈ removed, activity e := by
  revert hdisj hv hene
  induction removed using Finset.induction_on with
  | empty => simp
  | @insert e removed he ih =>
    intro hdisj hv hene
    obtain ⟨hekept, hdisj⟩ := disjoint_insert_right.mp hdisj
    have hnew : e ∉ kept ∪ removed := fun h => (mem_union.mp h).elim hekept he
    have hprev := ih hdisj (fun f hf => hv f (mem_insert_of_mem hf))
      (fun f hf => hene f (mem_insert_of_mem hf))
    have hstep := log_partition_insert_edge_le ends vertices activity ha hnew
      (hv e (mem_insert_self e removed)) (hene e (mem_insert_self e removed))
    rw [Finset.union_insert, Finset.sum_insert he]
    exact ⟨by linarith only [hprev.1, hstep.1], by linarith only [hprev.2, hstep.2]⟩

omit [DecidableEq E] in
/-- Summing deletion partition functions over roots counts each matching once
per uncovered vertex, after restoring the missing monomer factor. -/
theorem sum_weighted_unmatched (ends : E → Finset V) (vertices : Finset V)
    (edges : Finset E) (w : E → ℝ) (z : ℝ)
    (hends : ∀ e ∈ edges, (ends e).card = 2) :
    (∑ M ∈ matchings ends vertices edges,
      ((vertices.card - 2 * M.card : ℕ) : ℝ) *
        (z ^ (vertices.card - 2 * M.card) * ∏ e ∈ M, w e)) =
    ∑ v ∈ vertices, z * monomerPartition ends (vertices.erase v) edges w z := by
  classical
  let wt (M : Finset E) := z ^ (vertices.card - 2 * M.card) * ∏ e ∈ M, w e
  calc
    _ = ∑ M ∈ matchings ends vertices edges,
        ∑ v ∈ vertices, if v ∉ M.biUnion ends then wt M else 0 := by
      refine sum_congr rfl fun M hM => ?_
      obtain ⟨hsub, hmatching⟩ := mem_matchings.mp hM
      have hocc := card_occupied ends hmatching (fun e he => hends e (hsub he))
      have hcard : (vertices \ M.biUnion ends).card = vertices.card - 2 * M.card := by
        rw [← hocc]
        exact card_sdiff_of_subset (by
          intro v hv
          obtain ⟨e, he, hv⟩ := mem_biUnion.mp hv
          exact hmatching.1 e he hv)
      have hs : vertices.filter (fun v => v ∉ M.biUnion ends) =
          vertices \ M.biUnion ends := by ext v; simp
      rw [← sum_filter, hs, sum_const, hcard, nsmul_eq_mul]
    _ = ∑ v ∈ vertices, ∑ M ∈ matchings ends vertices edges,
        if v ∉ M.biUnion ends then wt M else 0 := sum_comm
    _ = _ := by
      refine sum_congr rfl fun v hv => ?_
      have hfilter : (matchings ends vertices edges).filter (fun M => v ∉ M.biUnion ends) =
          matchings ends (vertices.erase v) edges := by
        ext M
        rw [mem_filter, no_edge_at_iff_after_delete]
        simp only [mem_biUnion, not_exists, not_and]
      rw [← sum_filter, hfilter, monomerPartition, Finset.mul_sum]
      refine sum_congr rfl fun M hM => ?_
      obtain ⟨hsub, hmatching⟩ := mem_matchings.mp hM
      have hcard := twice_card_le ends hmatching (fun e he => hends e (hsub he))
      have hsucc : vertices.card - 2 * M.card = (vertices.erase v).card - 2 * M.card + 1 := by
        have herase := card_erase_add_one hv
        omega
      dsimp only [wt]
      rw [hsucc, pow_succ', mul_assoc]

omit [DecidableEq E] in
/-- The finite logarithmic derivative is the sum of the monomer probabilities
`z * H(v)` over all vertices. -/
theorem hasDerivAt_log_monomerPartition_eq_sum_ratios (ends : E → Finset V)
    (vertices : Finset V) (edges : Finset E) (w : E → ℝ)
    (hw : ∀ e, 0 ≤ w e) (hends : ∀ e ∈ edges, (ends e).card = 2) (t : ℝ) :
    HasDerivAt (fun s => Real.log (monomerPartition ends vertices edges w (Real.exp s)))
      (∑ v ∈ vertices, Real.exp t * deletionRatio ends vertices edges w (Real.exp t) v) t := by
  have h := hasDerivAt_log_monomerPartition ends vertices edges w hw t
  refine h.congr_deriv ?_
  rw [sum_weighted_unmatched ends vertices edges w (Real.exp t) hends, div_eq_mul_inv, sum_mul]
  refine sum_congr rfl fun v _ => ?_
  rw [deletionRatio, div_eq_mul_inv, mul_assoc]

end

end Certificate.Tree

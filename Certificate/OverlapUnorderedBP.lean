import Certificate.OverlapUnorderedObservables
import Certificate.Endpoints

/-! The finite-depth occupation test expressed on unordered marked child bags. -/

open MeasureTheory Set
open scoped BigOperators

namespace Certificate.UnorderedTree

/-- Raw degree of a nonroot row, including its parent edge. -/
def rowDegree : (k : ℕ) → Depth k → ℕ
  | 0, _ => 1
  | _+1, t => 1 + childCount t

theorem measurable_rowDegree (k : ℕ) : Measurable (rowDegree k) := by
  cases k with
  | zero => exact measurable_const
  | succ k => exact measurable_const.add (measurable_childCount k)

/-- The column is reached from a row retained by the first trim. Its
post-row degree counts that parent and the retained child rows. -/
noncomputable def reachedColumnDegree (D : ℕ) : (k : ℕ) → Depth k → ℕ
  | 0, _ => 1
  | k+1, t => 1 + countChildrenWhere (fun a => rowDegree k a.2 ≤ D) t

theorem measurable_reachedColumnDegree (D k : ℕ) :
    Measurable (reachedColumnDegree D k) := by
  cases k with
  | zero => exact measurable_const
  | succ k =>
    exact measurable_const.add (measurable_countChildrenWhere
      (measurableSet_le ((measurable_rowDegree k).comp measurable_snd) measurable_const))

/-- A reached row keeps only eligible columns. A reached column keeps
only eligible rows. -/
def childAdmitted (D : ℕ) (fromRow : Bool) (k : ℕ) (t : Depth k) : Prop :=
  if fromRow then reachedColumnDegree D k t ≤ D else rowDegree k t ≤ D

noncomputable instance (D : ℕ) (fromRow : Bool) (k : ℕ) (t : Depth k) :
    Decidable (childAdmitted D fromRow k t) := by
  unfold childAdmitted
  cases fromRow <;> infer_instance

theorem measurableSet_childAdmitted (D : ℕ) (fromRow : Bool) (k : ℕ) :
    MeasurableSet {t | childAdmitted D fromRow k t} := by
  cases fromRow with
  | false =>
    exact measurableSet_le (measurable_rowDegree k) measurable_const
  | true =>
    exact measurableSet_le (measurable_reachedColumnDegree D k) measurable_const

/-- Directed messages toward the parent, in the component reached by
edges surviving both trim passes. The row argument indicates parity. -/
noncomputable def upwardIterate (D : ℕ) (β u : ℝ) :
    (k : ℕ) → ℕ → Bool → Depth k → ℝ
  | 0, _, _, _ => u⁻¹
  | _+1, 0, _, _ => u⁻¹
  | k+1, s+1, row, t =>
    (u + sumChildren (fun a =>
      if childAdmitted D row k a.2 then
        Real.exp (-β * a.1) * upwardIterate D β u k s (!row) a.2
      else 0) t)⁻¹

theorem measurable_upwardIterate (D : ℕ) (β u : ℝ) (k s : ℕ) (row : Bool) :
    Measurable (upwardIterate D β u k s row) := by
  induction k generalizing s row with
  | zero => exact measurable_const
  | succ k ih =>
    cases s with
    | zero => exact measurable_const
    | succ s =>
      apply Measurable.inv
      apply measurable_const.add
      refine measurable_sumChildren (Measurable.ite
        ((measurableSet_childAdmitted D row k).preimage measurable_snd) ?_ measurable_const)
      exact (measurable_const.mul measurable_fst).exp.mul ((ih s (!row)).comp measurable_snd)

/-- The activity times the upward message of a column adjacent to a retained root row. -/
noncomputable def rootChildTerm (D : ℕ) (β u : ℝ) (k s : ℕ)
    (a : ℝ × Depth k) : ℝ := by
  classical
  exact if childAdmitted D true k a.2 then
    Real.exp (-β * a.1) * upwardIterate D β u k s false a.2 else 0

theorem measurable_rootChildTerm (D : ℕ) (β u : ℝ) (k s : ℕ) :
    Measurable (rootChildTerm D β u k s) := by
  classical
  exact Measurable.ite ((measurableSet_childAdmitted D true k).preimage measurable_snd)
    ((measurable_const.mul measurable_fst).exp.mul
      ((measurable_upwardIterate D β u k s false).comp measurable_snd)) measurable_const

/-- The root cavity message excluding the named child occurrence. -/
noncomputable def rootExcluding (D : ℕ) (β u : ℝ) (k : ℕ) :
    ℕ → Depth (k+1) → (ℝ × Depth k) → ℝ
  | 0, _, _ => u⁻¹
  | s+1, t, a =>
    (u + sumChildren (rootChildTerm D β u k s) t - rootChildTerm D β u k s a)⁻¹

theorem measurable_rootExcluding (D : ℕ) (β u : ℝ) (k s : ℕ) :
    Measurable (fun x : Depth (k+1) × (ℝ × Depth k) =>
      rootExcluding D β u k s x.1 x.2) := by
  cases s with
  | zero => exact measurable_const
  | succ s =>
    exact ((measurable_const.add
      ((measurable_sumChildren (measurable_rootChildTerm D β u k s)).comp measurable_fst)).sub
        ((measurable_rootChildTerm D β u k s).comp measurable_snd)).inv

/-- A root-edge occupation, given zero for the child edges the trim removes. -/
noncomputable def rootChildOccupation (D : ℕ) (β u : ℝ) (k s : ℕ)
    (t : Depth (k+1)) (a : ℝ × Depth k) : ℝ := by
  classical
  exact if childCount t ≤ D ∧ childAdmitted D true k a.2 then
    edgeOccupation (Real.exp (-β * a.1)) (rootExcluding D β u k s t a)
      (upwardIterate D β u k s false a.2) else 0

theorem measurable_rootChildOccupation (D : ℕ) (β u : ℝ) (k s : ℕ) :
    Measurable (fun x : Depth (k+1) × (ℝ × Depth k) =>
      rootChildOccupation D β u k s x.1 x.2) := by
  classical
  refine Measurable.ite
    ((measurableSet_le ((measurable_childCount k).comp measurable_fst) measurable_const).inter
      ((measurableSet_childAdmitted D true k).preimage (measurable_snd.comp measurable_snd))) ?_
      measurable_const
  have h := (((measurable_const (a := -β)).mul (measurable_fst.comp measurable_snd)).exp.mul
    (measurable_rootExcluding D β u k s)).mul
    ((measurable_upwardIterate D β u k s false).comp (measurable_snd.comp measurable_snd))
  exact h.div (measurable_const.add h)

/-- The truncated square sum is a symmetric function of the child bag. -/
noncomputable def rootSquare (D : ℕ) (β u : ℝ) (k s : ℕ) (t : Depth (k+1)) : ℝ :=
  min 1 (sumChildren (fun a => (rootChildOccupation D β u k s t a)^2) t)

theorem measurable_rootSquare (D : ℕ) (β u : ℝ) (k s : ℕ) :
    Measurable (rootSquare D β u k s) := by
  apply measurable_ofBatch_iff.mpr
  apply measurable_on_poissonBatch
  intro n
  change Measurable (fun x => rootSquare D β u k s (node n x))
  simp only [rootSquare, sumChildren_node]
  apply measurable_const.min
  exact Finset.measurable_fun_sum _ fun i _ =>
    ((measurable_rootChildOccupation D β u k s).comp
      ((measurable_node k n).prodMk (measurable_pi_apply i))).pow_const 2

/-- Count all root-child occupations at or above the level, with multiplicity. -/
noncomputable def countRootOccupationsGE (D : ℕ) (β u : ℝ) (k s : ℕ)
    (q : ℝ) (t : Depth (k+1)) : ℕ :=
  countChildrenWhere (fun a => q ≤ rootChildOccupation D β u k s t a) t

theorem measurable_countRootOccupationsGE (D : ℕ) (β u : ℝ) (k s : ℕ) (q : ℝ) :
    Measurable (countRootOccupationsGE D β u k s q) := by
  classical
  apply measurable_ofBatch_iff.mpr
  apply measurable_on_poissonBatch
  intro n
  change Measurable (fun x => countRootOccupationsGE D β u k s q (node n x))
  simp only [countRootOccupationsGE, countChildrenWhere, sumChildren_node]
  exact Finset.measurable_fun_sum _ fun i _ => Measurable.ite
    (measurableSet_le measurable_const
      ((measurable_rootChildOccupation D β u k s).comp
        ((measurable_node k n).prodMk (measurable_pi_apply i)))) measurable_const measurable_const

/-- The third root occupation is recovered from the levels at which at
least three child occupations survive. Here the levels range over a
countable dense set, with default value zero. -/
noncomputable def rootThird (D : ℕ) (β u : ℝ) (k s : ℕ) (t : Depth (k+1)) : ℝ :=
  ⨆ q : ℚ, if 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ 1 ∧ 3 ≤ countRootOccupationsGE D β u k s q t
    then (q : ℝ) else 0

theorem measurable_rootThird (D : ℕ) (β u : ℝ) (k s : ℕ) :
    Measurable (rootThird D β u k s) := by
  classical
  apply Measurable.iSup
  intro q
  by_cases h : 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ 1
  · simpa only [h.1, h.2, true_and] using
      (Measurable.ite (measurableSet_le measurable_const
        (measurable_countRootOccupationsGE D β u k s q))
        (measurable_const (a := (q : ℝ))) (measurable_const (a := (0 : ℝ))))
  · have hq (t : Depth (k+1)) :
        ¬(0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ 1 ∧ 3 ≤ countRootOccupationsGE D β u k s q t) :=
      fun h' => h ⟨h'.1,h'.2.1⟩
    simpa only [if_neg (hq _)] using
      (measurable_const : Measurable (fun _ : Depth (k+1) => (0:ℝ)))

end Certificate.UnorderedTree

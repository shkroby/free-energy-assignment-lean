import Certificate.OverlapUnorderedTree

/-! Measurable symmetric sums on the children of an unordered tree. -/

open MeasureTheory Set
open scoped BigOperators

namespace Certificate.UnorderedTree

def sumChildren {k : ℕ} {Y : Type*} [AddCommMonoid Y]
    (f : ℝ × Depth k → Y) (t : Depth (k+1)) : Y :=
  (Multiset.map f t).sum

theorem sumChildren_node {k n : ℕ} {Y : Type*} [AddCommMonoid Y]
    (f : ℝ × Depth k → Y) (x : Fin n → ℝ × Depth k) :
    sumChildren f (node n x) = ∑ i : Fin n, f (x i) := by
  simp [sumChildren, node, ofBatch, unorderedBatch, Multiset.map_coe, List.map_ofFn, List.sum_ofFn]

theorem measurable_sumChildren {k : ℕ} {Y : Type*} [AddCommMonoid Y] [MeasurableSpace Y]
    [MeasurableAdd₂ Y] {f : ℝ × Depth k → Y} (hf : Measurable f) :
    Measurable (sumChildren f) := by
  apply measurable_ofBatch_iff.mpr
  apply measurable_on_poissonBatch
  intro n
  change Measurable (fun x => sumChildren f (node n x))
  simp only [sumChildren_node]
  exact Finset.measurable_fun_sum _ fun i _ => hf.comp (measurable_pi_apply i)

def childCount {k : ℕ} (t : Depth (k+1)) : ℕ := Multiset.card t

theorem childCount_node {k n : ℕ} (x : Fin n → ℝ × Depth k) : childCount (node n x) = n := by
  simp [childCount, node, ofBatch, unorderedBatch]

theorem measurable_childCount (k : ℕ) : Measurable (childCount (k := k)) := by
  apply measurable_ofBatch_iff.mpr
  apply measurable_on_poissonBatch
  intro n
  change Measurable (fun x => childCount (node n x))
  simp only [childCount_node]
  exact measurable_const

noncomputable def countChildrenWhere {k : ℕ} (p : ℝ × Depth k → Prop) : Depth (k+1) → ℕ :=
  by classical exact sumChildren (fun x => if p x then 1 else 0)

theorem measurable_countChildrenWhere {k : ℕ} {p : ℝ × Depth k → Prop}
    (hp : MeasurableSet {x | p x}) : Measurable (countChildrenWhere p) := by
  classical
  exact measurable_sumChildren (Measurable.ite hp measurable_const measurable_const)

end Certificate.UnorderedTree

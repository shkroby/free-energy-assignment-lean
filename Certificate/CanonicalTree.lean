import Certificate.Arrivals
import Certificate.TreeBoundary
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Tactic.FinCases

/-!
# Extremal messages on the canonical Poisson tree

A vertex is a finite word of child labels. Each vertex carries its own
independent sequence of exponential spacings. Prefixing by a child label
extracts a copy of the full environment and commutes with the depth recursion.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace Certificate

namespace CanonicalTree

abbrev Spacings := ℕ → ℝ
abbrev Vertex := List ℕ
abbrev Environment := Vertex → Spacings

/-- Product law of the independent spacing sequences at the vertices. -/
noncomputable def law : Measure Environment :=
  Measure.infinitePi (fun _ : Vertex => exponentialSpacings)

theorem isProbabilityMeasure_law : IsProbabilityMeasure law := by
  let : IsProbabilityMeasure exponentialSpacings := isProbabilityMeasure_exponentialSpacings
  unfold law
  infer_instance

/-- The child of a vertex is obtained by appending its label. -/
def child (v : Vertex) (i : ℕ) : Vertex := v ++ [i]

/-- The environment in the (i)-th branch, viewed from its root. -/
def branch (i : ℕ) (ω : Environment) (v : Vertex) : Spacings := ω (i :: v)

theorem measurable_branch (i : ℕ) : Measurable (branch i) :=
  measurable_pi_iff.mpr fun v => measurable_pi_apply (i :: v)

/-- The branch environment has the same product law as the whole tree. -/
theorem measurePreserving_branch (i : ℕ) : MeasurePreserving (branch i) law law := by
  let : IsProbabilityMeasure exponentialSpacings := isProbabilityMeasure_exponentialSpacings
  refine ⟨measurable_branch i, ?_⟩
  exact Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : Vertex => exponentialSpacings)
    (f := fun v : Vertex => i :: v) (fun _ _ h => (List.cons.inj h).2)

/-- Weight of a child edge in the specified environment. -/
noncomputable def weight (β d : ℝ) (ω : Environment) (v : Vertex) (i : ℕ) : ℝ :=
  Real.exp (-β * arrivalLength d (ω v) i)

theorem weight_nonneg (β d : ℝ) (ω : Environment) (v : Vertex) (i : ℕ) :
    0 ≤ weight β d ω v i := Real.exp_nonneg _

theorem measurable_weight (β d : ℝ) (v : Vertex) (i : ℕ) :
    Measurable (fun ω => weight β d ω v i) := by
  unfold weight arrivalLength
  fun_prop

theorem ae_summable_weight {β d : ℝ} (hβ : 0 < β) (hd : 0 < d) :
    ∀ᵐ ω ∂law, ∀ v, Summable (weight β d ω v) := by
  let : IsProbabilityMeasure exponentialSpacings := isProbabilityMeasure_exponentialSpacings
  apply ae_all_iff.mpr
  intro v
  have hp := measurePreserving_eval_infinitePi (fun _ : Vertex => exponentialSpacings) v
  exact hp.quasiMeasurePreserving.tendsto_ae.eventually (ae_summable_arrival_weights hd hβ)

/-- The lower and upper cavity values at finite truncation depth. -/
noncomputable def depth (β d z : ℝ) (n : ℕ) (v : Vertex) (ω : Environment) : ℝ × ℝ :=
  TreeBoundary.bounds z child (weight β d ω) n v

theorem measurable_depth (β d z : ℝ) (n : ℕ) (v : Vertex) :
    Measurable (depth β d z n v) := by
  induction n generalizing v with
  | zero => exact measurable_const
  | succ n ih =>
    unfold depth
    simp only [TreeBoundary.bounds]
    have hL : Measurable (fun ω => TreeBoundary.update z (weight β d ω v)
        (fun i => (depth β d z n (child v i) ω).2)) := by
      unfold TreeBoundary.update
      exact (measurable_const.add (Measurable.tsum fun i =>
        (measurable_weight β d v i).mul (ih (child v i)).snd)).inv
    have hU : Measurable (fun ω => TreeBoundary.update z (weight β d ω v)
        (fun i => (depth β d z n (child v i) ω).1)) := by
      unfold TreeBoundary.update
      exact (measurable_const.add (Measurable.tsum fun i =>
        (measurable_weight β d v i).mul (ih (child v i)).fst)).inv
    exact hL.prodMk hU

theorem depth_branch (β d z : ℝ) (n : ℕ) (v : Vertex) (ω : Environment) (i : ℕ) :
    depth β d z n v (branch i ω) = depth β d z n (i :: v) ω := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    change
      (TreeBoundary.update z (weight β d (branch i ω) v)
          (fun j => (depth β d z n (child v j) (branch i ω)).2),
        TreeBoundary.update z (weight β d (branch i ω) v)
          (fun j => (depth β d z n (child v j) (branch i ω)).1)) =
      (TreeBoundary.update z (weight β d ω (i :: v))
          (fun j => (depth β d z n (child (i :: v) j) ω).2),
        TreeBoundary.update z (weight β d ω (i :: v))
          (fun j => (depth β d z n (child (i :: v) j) ω).1))
    have hchild (j : ℕ) : child (i :: v) j = i :: child v j := rfl
    have hweight : weight β d (branch i ω) v = weight β d ω (i :: v) := rfl
    simp only [ih, hchild, hweight]

/-- Lower extremal limit of the depth recursion. -/
noncomputable def lower (β d z : ℝ) (v : Vertex) (ω : Environment) : ℝ :=
  ⨆ n, (depth β d z n v ω).1

/-- Upper extremal limit of the depth recursion. -/
noncomputable def upper (β d z : ℝ) (v : Vertex) (ω : Environment) : ℝ :=
  ⨅ n, (depth β d z n v ω).2

theorem measurable_lower (β d z : ℝ) (v : Vertex) : Measurable (lower β d z v) :=
  Measurable.iSup fun n => (measurable_depth β d z n v).fst

theorem measurable_upper (β d z : ℝ) (v : Vertex) : Measurable (upper β d z v) :=
  Measurable.iInf fun n => (measurable_depth β d z n v).snd

theorem lower_branch (β d z : ℝ) (v : Vertex) (ω : Environment) (i : ℕ) :
    lower β d z v (branch i ω) = lower β d z (i :: v) ω := by
  simp only [lower, depth_branch]

theorem upper_branch (β d z : ℝ) (v : Vertex) (ω : Environment) (i : ℕ) :
    upper β d z v (branch i ω) = upper β d z (i :: v) ω := by
  simp only [upper, depth_branch]

/-- Pair of extremal messages at the root, on the common tree realization. -/
noncomputable def rootPair (β d z : ℝ) (ω : Environment) : ℝ × ℝ :=
  (lower β d z [] ω, upper β d z [] ω)

theorem measurable_rootPair (β d z : ℝ) : Measurable (rootPair β d z) :=
  (measurable_lower β d z []).prodMk (measurable_upper β d z [])

noncomputable def rootPairLaw (β d z : ℝ) : Measure (ℝ × ℝ) :=
  law.map (rootPair β d z)

theorem isProbabilityMeasure_rootPairLaw (β d z : ℝ) :
    IsProbabilityMeasure (rootPairLaw β d z) := by
  let : IsProbabilityMeasure law := isProbabilityMeasure_law
  exact Measure.isProbabilityMeasure_map (measurable_rootPair β d z).aemeasurable

theorem boundary_limits_of_summable_weight {β d z : ℝ} {ω : Environment}
    (hz : 0 < z) (hw : ∀ v, Summable (weight β d ω v)) :
    ∀ v,
      Tendsto (fun n => (depth β d z n v ω).1) atTop (𝓝 (lower β d z v ω)) ∧
      Tendsto (fun n => (depth β d z n v ω).2) atTop (𝓝 (upper β d z v ω)) ∧
      0 < lower β d z v ω ∧ lower β d z v ω ≤ upper β d z v ω ∧
      upper β d z v ω ≤ z⁻¹ ∧
      lower β d z v ω = TreeBoundary.update z (weight β d ω v)
        (fun i => upper β d z (child v i) ω) ∧
      upper β d z v ω = TreeBoundary.update z (weight β d ω v)
        (fun i => lower β d z (child v i) ω) := by
  let hw₀ := weight_nonneg β d ω
  obtain ⟨L, U, h⟩ := TreeBoundary.exists_boundary_limits z child (weight β d ω) hz hw hw₀
  have hL (v : Vertex) : lower β d z v ω = L v := by
    refine tendsto_nhds_unique ?_ (h v).1
    refine tendsto_atTop_ciSup
      (monotone_nat_of_le_succ fun n =>
        (TreeBoundary.bounds_step z child (weight β d ω) hz hw hw₀ n v).1) ?_
    refine ⟨z⁻¹, fun x ⟨n, hn⟩ => ?_⟩
    rw [← hn]
    exact (TreeBoundary.bounds_mem z child (weight β d ω) hz hw hw₀ n v).2.1.trans
      (TreeBoundary.bounds_mem z child (weight β d ω) hz hw hw₀ n v).2.2
  have hU (v : Vertex) : upper β d z v ω = U v := by
    refine tendsto_nhds_unique ?_ (h v).2.1
    refine tendsto_atTop_ciInf
      (antitone_nat_of_succ_le fun n =>
        (TreeBoundary.bounds_step z child (weight β d ω) hz hw hw₀ n v).2) ?_
    refine ⟨0, fun x ⟨n, hn⟩ => ?_⟩
    rw [← hn]
    exact (TreeBoundary.bounds_mem z child (weight β d ω) hz hw hw₀ n v).1.trans
      (TreeBoundary.bounds_mem z child (weight β d ω) hz hw hw₀ n v).2.1
  intro v
  simp only [hL, hU]
  exact h v

theorem ae_boundary_limits {β d z : ℝ} (hβ : 0 < β) (hd : 0 < d) (hz : 0 < z) :
    ∀ᵐ ω ∂law, ∀ v,
      Tendsto (fun n => (depth β d z n v ω).1) atTop (𝓝 (lower β d z v ω)) ∧
      Tendsto (fun n => (depth β d z n v ω).2) atTop (𝓝 (upper β d z v ω)) ∧
      0 < lower β d z v ω ∧ lower β d z v ω ≤ upper β d z v ω ∧
      upper β d z v ω ≤ z⁻¹ ∧
      lower β d z v ω = TreeBoundary.update z (weight β d ω v)
        (fun i => upper β d z (child v i) ω) ∧
      upper β d z v ω = TreeBoundary.update z (weight β d ω v)
        (fun i => lower β d z (child v i) ω) :=
  (ae_summable_weight hβ hd).mono fun _ hw => boundary_limits_of_summable_weight hz hw

/-- At the root the child messages can be evaluated as root messages of
the corresponding branch environments. -/
theorem ae_root_cross_recursions {β d z : ℝ} (hβ : 0 < β) (hd : 0 < d) (hz : 0 < z) :
    ∀ᵐ ω ∂law,
      lower β d z [] ω = TreeBoundary.update z (weight β d ω [])
        (fun i => (rootPair β d z (branch i ω)).2) ∧
      upper β d z [] ω = TreeBoundary.update z (weight β d ω [])
        (fun i => (rootPair β d z (branch i ω)).1) := by
  filter_upwards [ae_boundary_limits hβ hd hz] with ω hw
  have h := hw []
  simpa only [rootPair, upper_branch, lower_branch, child, List.nil_append] using h.2.2.2.2.2

private def side (j : Fin 2) : Type :=
  Fin.cases Unit (fun _ : Fin 1 => ℕ × Vertex) j

private def addr : (j : Fin 2) → side j → Vertex :=
  Fin.cases (motive := fun j => side j → Vertex)
    (fun _ => []) (fun _ p => p.1 :: p.2)

private theorem addr_injective : Function.Injective (fun p : Σ j, side j => addr p.1 p.2) := by
  rintro ⟨i,x⟩ ⟨j,y⟩
  fin_cases i <;> fin_cases j
  · intro _
    exact congrArg (fun u : Unit => (⟨0,u⟩ : Σ j, side j))
      (@Subsingleton.elim Unit inferInstance x y)
  · intro h
    have h' : ([] : Vertex) = (y : ℕ × Vertex).1 :: y.2 := h
    cases h'
  · intro h
    have h' : (x : ℕ × Vertex).1 :: x.2 = ([] : Vertex) := h
    cases h'
  · intro h
    have hxy : (x : ℕ × Vertex) = y := Prod.ext (List.cons.inj h).1 (List.cons.inj h).2
    exact congrArg (Sigma.mk 1) hxy

private def splitSides {A : Type*} (ω : Vertex → A) (j : Fin 2) (x : side j) : A :=
  ω (addr j x)

private theorem measurable_splitSides {A : Type*} [MeasurableSpace A] :
    Measurable (splitSides (A := A)) := by
  exact measurable_pi_iff.mpr fun j => measurable_pi_iff.mpr fun x => measurable_pi_apply (addr j x)

private noncomputable def sideLaw {A : Type*} [MeasurableSpace A]
    (P : Measure A) (j : Fin 2) : Measure (side j → A) :=
  Measure.infinitePi (fun _ : side j => P)

private theorem map_splitSides {A : Type*} [MeasurableSpace A] (P : Measure A)
    [IsProbabilityMeasure P] :
    (Measure.infinitePi (fun _ : Vertex => P)).map splitSides = Measure.pi (sideLaw P) := by
  let : ∀ j, IsProbabilityMeasure (sideLaw P j) := fun j => by unfold sideLaw; infer_instance
  let e : ((Σ j, side j) → A) ≃ᵐ ((j : Fin 2) → side j → A) :=
    MeasurableEquiv.piCurry (fun _ _ => A)
  let unc (ω : Vertex → A) (p : Σ j, side j) := ω (addr p.1 p.2)
  have hunc : Measurable unc :=
    measurable_pi_iff.mpr fun p => measurable_pi_apply (addr p.1 p.2)
  have hm : (Measure.infinitePi (fun _ : Vertex => P)).map unc =
      Measure.infinitePi (fun _ : Σ j, side j => P) :=
    Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : Vertex => P) addr_injective
  change (Measure.infinitePi (fun _ : Vertex => P)).map (e ∘ unc) = _
  rw [← Measure.map_map e.measurable hunc, hm, ← Measure.infinitePi_eq_pi]
  exact Measure.infinitePi_map_piCurry (fun (_ : Fin 2) _ => P)

/-- Splitting an iid annotated tree into its root annotation and its child
subtrees gives the corresponding independent product law. -/
theorem map_annotated_root_branches {A : Type*} [MeasurableSpace A]
    (P : Measure A) [IsProbabilityMeasure P] :
    (Measure.infinitePi (fun _ : Vertex => P)).map
        (fun ω => (ω [], fun i v => ω (i :: v))) =
      P.prod (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : Vertex => P))) := by
  let : ∀ j, IsProbabilityMeasure (sideLaw P j) := fun j => by unfold sideLaw; infer_instance
  let e : ((j : Fin 2) → side j → A) ≃ᵐ (side 0 → A) × (side 1 → A) :=
    MeasurableEquiv.piFinTwo (fun j => side j → A)
  let p0 : (side 0 → A) → A := fun X => X ()
  let p1 : (side 1 → A) → (ℕ → Vertex → A) :=
    MeasurableEquiv.curry ℕ Vertex A
  have hp0 : Measurable p0 := measurable_pi_apply ()
  have hp1 : Measurable p1 := (MeasurableEquiv.curry ℕ Vertex A).measurable
  have h0 : (sideLaw P 0).map p0 = P :=
    Measure.infinitePi_map_eval (fun _ : Unit => P) ()
  have h1 : (sideLaw P 1).map p1 =
      Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : Vertex => P)) :=
    Measure.infinitePi_map_curry (fun (_ : ℕ) (_ : Vertex) => P)
  change (Measure.infinitePi (fun _ : Vertex => P)).map (Prod.map p0 p1 ∘ e ∘ splitSides) = _
  rw [← Measure.map_map (hp0.prodMap hp1) (e.measurable.comp measurable_splitSides),
    ← Measure.map_map e.measurable measurable_splitSides, map_splitSides,
    show (Measure.pi (sideLaw P)).map e = (sideLaw P 0).prod (sideLaw P 1) from
      (measurePreserving_piFinTwo (sideLaw P)).map_eq,
    ← Measure.map_prod_map _ _ hp0 hp1, h0, h1]

/-- The root spacings and all branch environments have the indicated
independent product law. -/
theorem map_root_branches :
    law.map (fun ω => (ω [], fun i => branch i ω)) =
      exponentialSpacings.prod (Measure.infinitePi (fun _ : ℕ => law)) := by
  let : IsProbabilityMeasure exponentialSpacings := isProbabilityMeasure_exponentialSpacings
  exact map_annotated_root_branches exponentialSpacings

/-- The root spacings are independent of any iid family of marks
obtained by applying the same measurable map to each branch environment. -/
theorem map_root_marks {A : Type*} [MeasurableSpace A] {g : Environment → A}
    (hg : Measurable g) :
    law.map (fun ω => (ω [], fun i => g (branch i ω))) =
      exponentialSpacings.prod (Measure.infinitePi (fun _ : ℕ => law.map g)) := by
  let : IsProbabilityMeasure exponentialSpacings := isProbabilityMeasure_exponentialSpacings
  let : IsProbabilityMeasure law := isProbabilityMeasure_law
  let f : (ℕ → Environment) → ℕ → A := fun X i => g (X i)
  have hf : Measurable f := measurable_pi_iff.mpr fun i => hg.comp (measurable_pi_apply i)
  have hr : Measurable (fun ω : Environment => (ω [], fun i => branch i ω)) :=
    (measurable_pi_apply []).prodMk (measurable_pi_iff.mpr measurable_branch)
  change law.map (Prod.map id f ∘ (fun ω => (ω [], fun i => branch i ω))) = _
  rw [← Measure.map_map (measurable_id.prodMap hf) hr, map_root_branches,
    ← Measure.map_prod_map _ _ measurable_id hf, Measure.map_id]
  rw [show (Measure.infinitePi (fun _ : ℕ => law)).map f =
    Measure.infinitePi (fun _ : ℕ => law.map g) from
    Measure.infinitePi_map_pi (fun _ : ℕ => law) (fun _ => hg)]

/-- The root spacings are independent of the iid sequence of child message
pairs. Each pair has the joint law of the lower and upper messages at the root. -/
theorem map_root_childPairs (β d z : ℝ) :
    law.map (fun ω => (ω [], fun i => rootPair β d z (branch i ω))) =
      exponentialSpacings.prod (Measure.infinitePi (fun _ : ℕ => rootPairLaw β d z)) :=
  map_root_marks (measurable_rootPair β d z)

end CanonicalTree
end Certificate

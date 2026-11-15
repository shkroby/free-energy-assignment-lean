import Certificate.IndependentCutoffBrackets
import Certificate.CanonicalShapeMass
import Certificate.LocalPlaneBrackets

/-! The canonical bracket expectation is the mixture over plane shapes with iid edge lengths. -/

open Filter Function MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Certificate.CanonicalTree

open LocalExploration

private def parentCoordinate {shape : PlaneShape} (v : shape.NonRootSlot) : Vertex × ℕ :=
  (v.val.val.dropLast, v.val.val.getLast v.property)

private theorem parentCoordinate_injective (shape : PlaneShape) :
    Injective (parentCoordinate (shape := shape)) := by
  intro u v h
  apply Subtype.ext
  apply Subtype.ext
  calc
    _ = u.val.val.dropLast ++ [u.val.val.getLast u.property] := (List.dropLast_append_getLast _).symm
    _ = v.val.val.dropLast ++ [v.val.val.getLast v.property] :=
      congrArg (fun p : Vertex × ℕ => p.1 ++ [p.2]) h
    _ = _ := List.dropLast_append_getLast _

private def readShapeMarks (shape : PlaneShape) (T : Environment) (v : shape.NonRootSlot) : ℝ :=
  T (parentCoordinate v).1 (parentCoordinate v).2

private theorem measurable_readShapeMarks (shape : PlaneShape) : Measurable (readShapeMarks shape) :=
  measurable_pi_iff.mpr fun v =>
    (measurable_pi_apply (parentCoordinate v).2).comp (measurable_pi_apply (parentCoordinate v).1)

private theorem map_readShapeMarks {d R : ℝ} (hd : 0 < d) (hR : 0 < R) (shape : PlaneShape) :
    (Measure.infinitePi (fun _ : Vertex => independentLengthSequence d R)).map (readShapeMarks shape) =
      Measure.infinitePi (fun _ : shape.NonRootSlot => truncatedIntensity d R) := by
  let μ := truncatedIntensity d R
  let : IsProbabilityMeasure μ := isProbabilityMeasure_truncatedIntensity hd hR
  let ν : Measure Environment := Measure.infinitePi (fun _ : Vertex => independentLengthSequence d R)
  let F := (MeasurableEquiv.curry Vertex ℕ ℝ).symm
  let f (x : Vertex × ℕ → ℝ) (v : shape.NonRootSlot) := x (parentCoordinate v)
  have hf : Measurable f := measurable_pi_iff.mpr fun v => measurable_pi_apply (parentCoordinate v)
  have hF : ν.map F = Measure.infinitePi (fun _ : Vertex × ℕ => μ) :=
    Measure.infinitePi_map_curry_symm (fun (_ : Vertex) (_ : ℕ) => μ)
  change ν.map (f ∘ F) = _
  rw [← Measure.map_map hf F.measurable, hF]
  exact Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : Vertex × ℕ => μ) (parentCoordinate_injective shape)

private theorem independentDepth_eq_shape (β d R z : ℝ) (shape : PlaneShape)
    {E T : Environment}
    (hOff : ∀ v ∈ shape.slots, v.length < shape.depth →
      cutoffOffspring d R (E v) = (shape.childCount v : ℝ≥0∞)) :
    independentCutoffDepth β d R z shape.depth [] (fun v => (E v,T v)) =
      shape.shapeBracket β z (readShapeMarks shape T) := by
  classical
  let W := independentCutoffWeight β d R (fun v => (E v,T v))
  let w := shape.shapeWeight β (readShapeMarks shape T)
  have hw (v : Vertex) (hv : v ∈ shape.slots) (hd : v.length < shape.depth) (i : ℕ) :
      W v i = w v i := by
    dsimp only [W, independentCutoffWeight, w, PlaneShape.shapeWeight]
    rw [hOff v hv hd]
    by_cases hi : i < shape.childCount v
    · have hs := (shape.child_mem v i).mpr ⟨hv, hd, hi⟩
      rw [if_pos (by exact_mod_cast hi), dif_pos hs]
      simp [readShapeMarks, parentCoordinate]
    · have hs : v ++ [i] ∉ shape.slots := fun h => hi ((shape.child_mem v i).mp h).2.2
      rw [if_neg (by exact_mod_cast hi), dif_neg hs]
  have he (k : ℕ) (v : Vertex) (hv : v ∈ shape.slots) (hdepth : k + v.length ≤ shape.depth) :
      TreeBoundary.bounds z child W k v = TreeBoundary.bounds z child w k v := by
    induction k generalizing v with
    | zero => rfl
    | succ k ih =>
      have hd : v.length < shape.depth := by omega
      have hsum (p : Bracket → ℝ) :
          (∑' i, W v i * p (TreeBoundary.bounds z child W k (child v i))) =
            ∑' i, w v i * p (TreeBoundary.bounds z child w k (child v i)) := by
        apply tsum_congr
        intro i
        rw [hw v hv hd i]
        by_cases hi : i < shape.childCount v
        · have hs := (shape.child_mem v i).mpr ⟨hv, hd, hi⟩
          rw [ih (child v i) hs (by simp [child]; omega)]
        · have hz' := shape.shapeWeight_eq_zero_of_notMem β (readShapeMarks shape T) v i
            (show i ∉ Finset.range (shape.childCount v) by simpa using hi)
          rw [show w v i = 0 from hz', zero_mul, zero_mul]
      simp only [TreeBoundary.bounds, TreeBoundary.update]
      rw [hsum Prod.snd, hsum Prod.fst]
  exact he shape.depth [] shape.root_mem (by simp)

private theorem ae_finite_counts {d R : ℝ} (hd : 0 < d) (hR : 0 < R) :
    ∀ᵐ E ∂law, ∀ v, ∃ j : ℕ, cutoffOffspring d R (E v) = (j : ℝ≥0∞) := by
  let : IsProbabilityMeasure exponentialSpacings := isProbabilityMeasure_exponentialSpacings
  apply ae_all_iff.mpr
  intro v
  have hp := measurePreserving_eval_infinitePi (fun _ : Vertex => exponentialSpacings) v
  exact hp.quasiMeasurePreserving.tendsto_ae.eventually (ae_cutoffOffspring_eq_nat hd hR.le)

private theorem independentCutoffDepth_eq_shapeCode (β d R z : ℝ) (k : ℕ) (E T : Environment)
    (hE : ∀ v, ∃ j : ℕ, cutoffOffspring d R (E v) = (j : ℝ≥0∞))
    (c : PlaneShapeCode k) (hc : cutoffShapeCode d R k E = c) :
    independentCutoffDepth β d R z k [] (fun v => (E v,T v)) =
      c.shape.shapeBracket β z (readShapeMarks c.shape T) := by
  have hs := congrArg Subtype.val hc
  change (cutoffPlaneShape d R k E).slots = c.val at hs
  have hshape : (PlaneShape.ofOffspring c.shape.depth
        (fun v => cutoffOffspringNat d R (E v))).slots = c.shape.slots := by
    rw [c.shape_depth, c.shape_slots]
    exact hs
  have hcount := (c.shape.ofOffspring_slots_eq_iff _).mp hshape
  have hOff (v : Vertex) (hv : v ∈ c.shape.slots) (hdep : v.length < c.shape.depth) :
      cutoffOffspring d R (E v) = (c.shape.childCount v : ℝ≥0∞) := by
    rw [← hcount v hv hdep]
    unfold cutoffOffspringNat
    rw [dif_pos (hE v)]
    exact (hE v).choose_spec
  simpa only [c.shape_depth] using independentDepth_eq_shape β d R z c.shape (T := T) hOff

/-- The canonical bracket integrates as a Poisson mixture of the same
bounded marked shape tests as in the finite assignment graph. -/
theorem integral_depthFor_eq_cutoffShapeMixture {β d R z : ℝ}
    (hd : 0 < d) (hR : 0 < R) (hz : 0 < z) (k : ℕ)
    (P : Bracket → ℝ) (hP : Continuous P) (hB : ∀ x : Bracket, 0 ≤ x.1 → x.1 ≤ x.2 →
      x.2 ≤ z⁻¹ → P x ∈ Icc 0 z⁻¹) :
    (∫ ω, P (depthFor (cutoffKernel β R) d z k [] ω) ∂law) =
      ∑' c : PlaneShapeCode k, cutoffShapeMass d R c *
        ∫ marks, P (c.shape.shapeBracket β z marks)
          ∂Measure.infinitePi (fun _ : c.shape.NonRootSlot => truncatedIntensity d R) := by
  let : IsProbabilityMeasure law := isProbabilityMeasure_law
  let : IsProbabilityMeasure exponentialSpacings := isProbabilityMeasure_exponentialSpacings
  let : IsProbabilityMeasure (independentLengthSequence d R) :=
    isProbabilityMeasure_independentLengthSequence hd hR
  let ν : Measure Environment := Measure.infinitePi (fun _ : Vertex => independentLengthSequence d R)
  let Z (p : Environment × Environment) (v : Vertex) := (p.1 v,p.2 v)
  have hZ : Measurable Z := measurable_pi_iff.mpr fun v =>
    ((measurable_pi_apply v).comp measurable_fst).prodMk
      ((measurable_pi_apply v).comp measurable_snd)
  have hmap : (law.prod ν).map Z = independentMarkTreeLaw d R := map_zip_infinitePi _ _
  let B := independentCutoffDepth β d R z k []
  let f (p : Environment × Environment) := P (B (Z p))
  have hf : Measurable f := hP.measurable.comp
    ((measurable_independentCutoffDepth β d R z k []).comp hZ)
  have hfb : ∀ᵐ p ∂law.prod ν, f p ∈ Icc 0 z⁻¹ := by
    apply (Measure.ae_prod_iff_ae_ae (hf measurableSet_Icc)).mpr
    filter_upwards [ae_finite_counts hd hR] with E hE
    apply Eventually.of_forall
    intro T
    let c := cutoffShapeCode d R k E
    have heq := independentCutoffDepth_eq_shapeCode β d R z k E T hE c rfl
    obtain ⟨h₀,h₁,h₂⟩ := c.shape.shapeBracket_mem β hz (readShapeMarks c.shape T)
    change P (independentCutoffDepth β d R z k [] (fun v => (E v,T v))) ∈ Icc 0 z⁻¹
    rw [heq]
    exact hB _ h₀ h₁ h₂
  have hfi : Integrable f (law.prod ν) :=
    (integrable_const (μ := law.prod ν) z⁻¹).mono' hf.aestronglyMeasurable
      (hfb.mono fun _ h => (Real.norm_of_nonneg h.1).trans_le h.2)
  let g (E : Environment) := ∫ T, f (E,T) ∂ν
  have hToAux : (∫ ω, P (depthFor (cutoffKernel β R) d z k [] ω) ∂law) =
      ∫ p, f p ∂law.prod ν := by
    rw [← integral_map (measurable_depthFor (measurable_cutoffKernel β R) d z k []).aemeasurable
      hP.measurable.aestronglyMeasurable, ← map_independentCutoffDepth_eq hd hR k,
      integral_map (measurable_independentCutoffDepth β d R z k []).aemeasurable
        hP.measurable.aestronglyMeasurable, ← hmap]
    have hPB : Measurable (fun ω : IndependentMarkEnvironment => P (B ω)) :=
      hP.measurable.comp (measurable_independentCutoffDepth β d R z k [])
    exact integral_map hZ.aemeasurable hPB.aestronglyMeasurable
  let A (c : PlaneShapeCode k) : Set Environment := {E | cutoffShapeCode d R k E = c}
  have hA : ∀ c, MeasurableSet (A c) := measurableSet_cutoffShapeCode_eq d R
  have hdisjoint : Pairwise (Disjoint on A) := fun _ _ h =>
    Set.disjoint_left.mpr fun _ ha hb => h (ha.symm.trans hb)
  have hU : (⋃ c, A c) = univ := eq_univ_of_forall fun E =>
    mem_iUnion.mpr ⟨cutoffShapeCode d R k E,rfl⟩
  rw [hToAux, integral_prod _ hfi]
  change (∫ E, g E ∂law) = _
  rw [← setIntegral_univ, ← hU, integral_iUnion hA hdisjoint hfi.integral_prod_left.integrableOn]
  apply tsum_congr
  intro c
  let a := ∫ marks, P (c.shape.shapeBracket β z marks)
    ∂Measure.infinitePi (fun _ : c.shape.NonRootSlot => truncatedIntensity d R)
  have hEq : g =ᵐ[law.restrict (A c)] fun _ => a := by
    have ha := ae_restrict_mem (μ := law) (hA c)
    filter_upwards [ae_mono Measure.restrict_le_self (ae_finite_counts hd hR), ha] with E hE hc
    unfold g
    rw [show (fun T => f (E,T)) = fun T => P (c.shape.shapeBracket β z (readShapeMarks c.shape T)) from
      funext fun T => congrArg P (independentCutoffDepth_eq_shapeCode β d R z k E T hE c hc)]
    unfold a
    have hPshape : Measurable (fun marks => P (c.shape.shapeBracket β z marks)) :=
      hP.measurable.comp (c.shape.continuous_shapeBracket β hz).measurable
    rw [← map_readShapeMarks hd hR c.shape,
      integral_map (measurable_readShapeMarks c.shape).aemeasurable hPshape.aestronglyMeasurable]
  rw [integral_congr_ae hEq, integral_const, measureReal_restrict_apply_univ, smul_eq_mul]
  rfl

end Certificate.CanonicalTree

import Certificate.OverlapUnorderedTreeLaw
import Certificate.OverlapUnorderedShape
import Certificate.IndependentShapeBracketMixture

/-! Any measurable unordered marked-neighborhood test has the iid plane
shape mixture law. -/

open Filter MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal

namespace Certificate.CanonicalTree

open LocalExploration UnorderedTree

private theorem independentUnorderedTree_eq_shapeCode (d R : ℝ) (k : ℕ) (E T : Environment)
    (c : PlaneShapeCode k) (hc : cutoffShapeCode d R k E = c) :
    independentUnorderedTree d R k (fun v => (E v,T v)) [] =
      c.shape.encodeUnorderedAt c.shape_depth (readShapeMarks c.shape T) := by
  have hs := congrArg Subtype.val hc
  change (cutoffPlaneShape d R k E).slots = c.val at hs
  have hshape : (PlaneShape.ofOffspring c.shape.depth
        (fun v => cutoffOffspringNat d R (E v))).slots = c.shape.slots := by
    rw [c.shape_depth, c.shape_slots]
    exact hs
  have hcount := (c.shape.ofOffspring_slots_eq_iff _).mp hshape
  unfold independentUnorderedTree
  refine c.shape.encodeUnorderedAt_ofChildren c.shape_depth hcount (fun v _ i hi => ?_)
  rw [PlaneShape.childLength, dif_pos hi]
  exact (readShapeMarks_child c.shape T v i hi).symm

/-- On each plane shape, the canonical unordered test integrates against
independent normalized intensity marks. The sum is over the Poisson shape law. -/
theorem lintegral_canonicalUnorderedTree_eq_shapeMixture {d R : ℝ}
    (hd : 0 < d) (hR : 0 < R) (k : ℕ) (P : Depth k → ℝ≥0∞) (hP : Measurable P) :
    (∫⁻ ω, P (canonicalUnorderedTree d R k ω []) ∂law) =
      ∑' c : PlaneShapeCode k, law {ω | cutoffShapeCode d R k ω = c} *
        ∫⁻ marks, P (c.shape.encodeUnorderedAt c.shape_depth marks)
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
  let B := fun ω => independentUnorderedTree d R k ω []
  let f (p : Environment × Environment) := P (B (Z p))
  have hPB : Measurable (fun ω => P (B ω)) :=
    hP.comp (measurable_independentUnorderedTree d R k [])
  have hf : Measurable f := hPB.comp hZ
  have hAux : (∫⁻ ω, P (canonicalUnorderedTree d R k ω []) ∂law) =
      ∫⁻ p, f p ∂law.prod ν := by
    rw [← lintegral_map hP (measurable_canonicalUnorderedTree d R k []),
      ← map_independentUnorderedTree_eq hd hR k, lintegral_map hP (measurable_independentUnorderedTree d R k []),
      ← hmap]
    exact lintegral_map hPB hZ
  let A (c : PlaneShapeCode k) : Set Environment := {E | cutoffShapeCode d R k E = c}
  have hA : ∀ c, MeasurableSet (A c) := measurableSet_cutoffShapeCode_eq d R
  have hdisjoint : Pairwise (Disjoint on A) := fun _ _ h =>
    Set.disjoint_left.mpr fun _ ha hb => h (ha.symm.trans hb)
  have hU : (⋃ c, A c) = univ := eq_univ_of_forall fun E =>
    mem_iUnion.mpr ⟨cutoffShapeCode d R k E,rfl⟩
  rw [hAux, lintegral_prod _ hf.aemeasurable]
  change (∫⁻ E, ∫⁻ T, f (E,T) ∂ν ∂law) = _
  rw [← setLIntegral_univ, ← hU, lintegral_iUnion hA hdisjoint]
  apply tsum_congr
  intro c
  let g (marks : c.shape.NonRootSlot → ℝ) := P (c.shape.encodeUnorderedAt c.shape_depth marks)
  have hg : Measurable g := hP.comp (c.shape.measurable_encodeUnorderedAt c.shape_depth)
  let a := ∫⁻ marks, g marks ∂Measure.infinitePi (fun _ : c.shape.NonRootSlot => truncatedIntensity d R)
  have heq : ∀ᵐ E ∂law.restrict (A c), (∫⁻ T, f (E,T) ∂ν) = a := by
    filter_upwards [ae_restrict_mem (μ := law) (hA c)] with E hc
    have h (T : Environment) : f (E,T) = g (readShapeMarks c.shape T) := by
      change P (independentUnorderedTree d R k (fun v => (E v,T v)) []) = _
      exact congrArg P (independentUnorderedTree_eq_shapeCode d R k E T c hc)
    simp_rw [h]
    unfold a
    rw [← map_readShapeMarks hd hR c.shape, lintegral_map hg (measurable_readShapeMarks c.shape)]
  rw [lintegral_congr_ae heq, lintegral_const, Measure.restrict_apply_univ, mul_comm]

/-- The real expectation of a bounded nonnegative unordered tree test
is the same plane-shape mixture used for finite-graph local convergence. -/
theorem integral_canonicalUnorderedTree_eq_shapeMixture {d R : ℝ}
    (hd : 0 < d) (hR : 0 < R) (k : ℕ) (P : Depth k → ℝ) (hP : Measurable P)
    (hB : ∀ a, P a ∈ Icc 0 1) :
    (∫ ω, P (canonicalUnorderedTree d R k ω []) ∂law) =
      ∑' c : PlaneShapeCode k, cutoffShapeMass d R c *
        ∫ marks, P (c.shape.encodeUnorderedAt c.shape_depth marks)
          ∂Measure.infinitePi (fun _ : c.shape.NonRootSlot => truncatedIntensity d R) := by
  let : IsProbabilityMeasure law := isProbabilityMeasure_law
  let : IsProbabilityMeasure (truncatedIntensity d R) := isProbabilityMeasure_truncatedIntensity hd hR
  let Q (c : PlaneShapeCode k) := Measure.infinitePi (fun _ : c.shape.NonRootSlot => truncatedIntensity d R)
  let F (c : PlaneShapeCode k) (marks : c.shape.NonRootSlot → ℝ) := P (c.shape.encodeUnorderedAt c.shape_depth marks)
  have hF (c : PlaneShapeCode k) : Measurable (F c) := hP.comp (c.shape.measurable_encodeUnorderedAt c.shape_depth)
  let J (c : PlaneShapeCode k) := ∫⁻ marks, ENNReal.ofReal (F c marks) ∂Q c
  have hJ (c : PlaneShapeCode k) : J c ≠ ∞ := by
    let : IsProbabilityMeasure (Q c) := inferInstanceAs (IsProbabilityMeasure
      (Measure.infinitePi (fun _ : c.shape.NonRootSlot => truncatedIntensity d R)))
    have hle : J c ≤ 1 := calc
      _ ≤ ∫⁻ _marks, (1 : ℝ≥0∞) ∂Q c := lintegral_mono fun marks => by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (hB _).2
      _ = _ := by simp
    exact ne_top_of_le_ne_top ENNReal.one_ne_top hle
  have hfin (c : PlaneShapeCode k) : law {ω | cutoffShapeCode d R k ω = c} * J c ≠ ∞ :=
    ENNReal.mul_ne_top (measure_ne_top _ _) (hJ c)
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (fun _ => (hB _).1))
      (hP.comp (measurable_canonicalUnorderedTree d R k [])).aestronglyMeasurable,
    lintegral_canonicalUnorderedTree_eq_shapeMixture hd hR k _ hP.ennreal_ofReal]
  change (∑' c : PlaneShapeCode k, law {ω | cutoffShapeCode d R k ω = c} * J c).toReal = _
  rw [ENNReal.tsum_toReal_eq hfin]
  apply tsum_congr
  intro c
  rw [ENNReal.toReal_mul]
  congr 1
  exact (integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (fun _ => (hB _).1))
    (hF c).aestronglyMeasurable).symm

end Certificate.CanonicalTree

import Certificate.CanonicalSoftUniqueness
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Any bounded soft fixed point is trapped by the canonical boundary limits. -/

open Filter MeasureTheory Set
open scoped Topology ENNReal

namespace Certificate.CanonicalTree

private abbrev Annotated := Vertex → Spacings × ℝ

private noncomputable def annotatedLaw (μ : Measure ℝ) : Measure Annotated :=
  Measure.infinitePi (fun _ : Vertex => exponentialSpacings.prod μ)

private theorem isProbabilityMeasure_annotatedLaw (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (annotatedLaw μ) := by
  let : IsProbabilityMeasure exponentialSpacings := isProbabilityMeasure_exponentialSpacings
  unfold annotatedLaw
  infer_instance

private def spacings (ω : Annotated) : Environment := fun v => (ω v).1
private def terminals (ω : Annotated) : Vertex → ℝ := fun v => (ω v).2
private def subBranch (i : ℕ) (ω : Annotated) : Annotated := fun v => ω (i :: v)

private theorem measurable_spacings : Measurable spacings :=
  measurable_pi_iff.mpr fun v => measurable_fst.comp (measurable_pi_apply v)
private theorem measurable_terminals : Measurable terminals :=
  measurable_pi_iff.mpr fun v => measurable_snd.comp (measurable_pi_apply v)
private theorem measurable_subBranch (i : ℕ) : Measurable (subBranch i) :=
  measurable_pi_iff.mpr fun v => measurable_pi_apply (i :: v)

private theorem map_spacings (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (annotatedLaw μ).map spacings = law := by
  let : IsProbabilityMeasure exponentialSpacings := isProbabilityMeasure_exponentialSpacings
  change (Measure.infinitePi (fun _ : Vertex => exponentialSpacings.prod μ)).map
    (fun x : Annotated => fun i : Vertex => (x i).1) =
      Measure.infinitePi (fun _ : Vertex => exponentialSpacings)
  rw [Measure.infinitePi_map_pi (fun _ : Vertex => exponentialSpacings.prod μ)
    (fun _ => measurable_fst)]
  simp only [Measure.map_fst_prod, measure_univ, one_smul]

private theorem map_terminals (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (annotatedLaw μ).map terminals = Measure.infinitePi (fun _ : Vertex => μ) := by
  let : IsProbabilityMeasure exponentialSpacings := isProbabilityMeasure_exponentialSpacings
  change (Measure.infinitePi (fun _ : Vertex => exponentialSpacings.prod μ)).map
    (fun x : Annotated => fun i : Vertex => (x i).2) = Measure.infinitePi (fun _ : Vertex => μ)
  rw [Measure.infinitePi_map_pi (fun _ : Vertex => exponentialSpacings.prod μ)
    (fun _ => measurable_snd)]
  simp only [Measure.map_snd_prod, measure_univ, one_smul]

private theorem map_annotated_marks (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {g : Annotated → ℝ} (hg : Measurable g) :
    (annotatedLaw μ).map (fun ω => ((ω []).1, fun i => g (subBranch i ω))) =
      markedSpacings ((annotatedLaw μ).map g) := by
  let : IsProbabilityMeasure exponentialSpacings := isProbabilityMeasure_exponentialSpacings
  let : IsProbabilityMeasure (annotatedLaw μ) := isProbabilityMeasure_annotatedLaw μ
  let f : (ℕ → Annotated) → ℕ → ℝ := fun X i => g (X i)
  have hf : Measurable f := measurable_pi_iff.mpr fun i => hg.comp (measurable_pi_apply i)
  have hdata : Measurable (fun ω : Annotated => (ω [], fun i => subBranch i ω)) :=
    (measurable_pi_apply []).prodMk (measurable_pi_iff.mpr measurable_subBranch)
  have hmap : (annotatedLaw μ).map (fun ω => (ω [], fun i => subBranch i ω)) =
      (exponentialSpacings.prod μ).prod (Measure.infinitePi (fun _ : ℕ => annotatedLaw μ)) :=
    map_annotated_root_branches (exponentialSpacings.prod μ)
  change (annotatedLaw μ).map (Prod.map Prod.fst f ∘
      (fun ω => (ω [], fun i => subBranch i ω))) = _
  rw [← Measure.map_map (measurable_fst.prodMap hf) hdata, hmap,
    ← Measure.map_prod_map _ _ measurable_fst hf, Measure.map_fst_prod, measure_univ, one_smul]
  unfold markedSpacings
  rw [show (Measure.infinitePi (fun _ : ℕ => annotatedLaw μ)).map f =
    Measure.infinitePi (fun _ : ℕ => (annotatedLaw μ).map g) from
    Measure.infinitePi_map_pi (fun _ : ℕ => annotatedLaw μ) (fun _ => hg)]

private noncomputable def withTerminals (β d z : ℝ) (n : ℕ) (v : Vertex) (ω : Annotated) : ℝ :=
  TreeBoundary.fromBoundary z child (weight β d (spacings ω)) (terminals ω) n v

private theorem measurable_withTerminals (β d z : ℝ) (n : ℕ) (v : Vertex) :
    Measurable (withTerminals β d z n v) := by
  induction n generalizing v with
  | zero => exact (measurable_pi_apply v).snd
  | succ n ih =>
    unfold withTerminals
    simp only [TreeBoundary.fromBoundary]
    unfold TreeBoundary.update
    exact (measurable_const.add (Measurable.tsum fun i =>
      ((measurable_weight β d v i).comp measurable_spacings).mul (ih (child v i)))).inv

private theorem withTerminals_branch (β d z : ℝ) (n : ℕ) (v : Vertex) (ω : Annotated) (i : ℕ) :
    withTerminals β d z n v (subBranch i ω) = withTerminals β d z n (i :: v) ω := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    change TreeBoundary.update z (weight β d (spacings (subBranch i ω)) v)
          (fun j => withTerminals β d z n (child v j) (subBranch i ω)) =
      TreeBoundary.update z (weight β d (spacings ω) (i :: v))
          (fun j => withTerminals β d z n (child (i :: v) j) ω)
    have hchild (j : ℕ) : child (i :: v) j = i :: child v j := rfl
    have hweight : weight β d (spacings (subBranch i ω)) v = weight β d (spacings ω) (i :: v) := rfl
    simp only [ih, hchild, hweight]

private theorem ae_annotated_good {β d z : ℝ} (hβ : 0 < β) (hd : 0 < d)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hb : ∀ᵐ h ∂μ, h ∈ Icc 0 z⁻¹) :
    ∀ᵐ ω ∂annotatedLaw μ, (∀ v, Summable (weight β d (spacings ω) v)) ∧
      ∀ v, terminals ω v ∈ Icc 0 z⁻¹ := by
  let hSp : MeasurePreserving spacings (annotatedLaw μ) law :=
    ⟨measurable_spacings, map_spacings μ⟩
  let hT : MeasurePreserving terminals (annotatedLaw μ)
      (Measure.infinitePi (fun _ : Vertex => μ)) := ⟨measurable_terminals, map_terminals μ⟩
  have htb : ∀ᵐ X ∂Measure.infinitePi (fun _ : Vertex => μ), ∀ v, X v ∈ Icc 0 z⁻¹ := by
    apply ae_all_iff.mpr
    intro v
    have H := measurePreserving_eval_infinitePi (fun _ : Vertex => μ) v
    exact H.quasiMeasurePreserving.tendsto_ae.eventually hb
  filter_upwards [hSp.quasiMeasurePreserving.tendsto_ae.eventually (ae_summable_weight hβ hd),
    hT.quasiMeasurePreserving.tendsto_ae.eventually htb] with ω h₁ h₂
  exact ⟨h₁,h₂⟩

private theorem mapped_withTerminals {β d z : ℝ} (hβ : 0 < β) (hd : 0 < d) (hz : 0 < z)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hb : ∀ᵐ h ∂μ, h ∈ Icc 0 z⁻¹)
    (hfix : (markedSpacings μ).map (arrivalSoftOutput β d z) = μ) (n : ℕ) :
    (annotatedLaw μ).map (withTerminals β d z n []) = μ := by
  let : IsProbabilityMeasure exponentialSpacings := isProbabilityMeasure_exponentialSpacings
  induction n with
  | zero =>
    change (annotatedLaw μ).map (Prod.snd ∘ (fun ω : Annotated => ω [])) = μ
    rw [← Measure.map_map measurable_snd (measurable_pi_apply []),
      show (annotatedLaw μ).map (fun ω : Annotated => ω []) = exponentialSpacings.prod μ from
        Measure.infinitePi_map_eval (fun _ : Vertex => exponentialSpacings.prod μ) [],
      Measure.map_snd_prod, measure_univ, one_smul]
  | succ n ih =>
    let F (ω : Annotated) : ArrivalConfiguration :=
      ((ω []).1, fun i => withTerminals β d z n [] (subBranch i ω))
    have hF : Measurable F := (measurable_pi_apply []).fst.prodMk (measurable_pi_iff.mpr fun i =>
      (measurable_withTerminals β d z n []).comp (measurable_subBranch i))
    have hmap : (annotatedLaw μ).map F = markedSpacings μ :=
      (map_annotated_marks μ (measurable_withTerminals β d z n [])).trans (congrArg markedSpacings ih)
    refine Eq.trans ?_ hfix
    rw [← hmap, Measure.map_map (measurable_arrivalSoftOutput β d z) hF]
    apply Measure.map_congr
    filter_upwards [ae_annotated_good hβ hd μ hb] with ω hw
    have hmark (i : ℕ) : (F ω).2 i ∈ Icc 0 z⁻¹ := by
      change withTerminals β d z n [] (subBranch i ω) ∈ _
      rw [withTerminals_branch]
      have hb₁ := TreeBoundary.bounds_mem z child _ hz hw.1
        (weight_nonneg β d (spacings ω)) n (i :: [])
      have hb₂ := TreeBoundary.fromBoundary_between z child _ hz hw.1
        (weight_nonneg β d (spacings ω)) (terminals ω) hw.2 n (i :: [])
      exact ⟨hb₁.1.trans hb₂.1, hb₂.2.trans hb₁.2.2⟩
    have hNN (i : ℕ) : 0 ≤ cavityTerm β d (F ω) i :=
      mul_nonneg (weight_nonneg β d (spacings ω) [] i) (hmark i).1
    have hsum : Summable (cavityTerm β d (F ω)) :=
      ((hw.1 []).mul_right z⁻¹).of_nonneg_of_le hNN
        (fun i => mul_le_mul_of_nonneg_left (hmark i).2 (weight_nonneg β d (spacings ω) [] i))
    have heq (i : ℕ) : withTerminals β d z n (child [] i) ω = (F ω).2 i :=
      (withTerminals_branch β d z n [] ω i).symm
    change (z + ∑' i, weight β d (spacings ω) [] i *
        withTerminals β d z n (child [] i) ω)⁻¹ =
      (z + (∑' i, ENNReal.ofReal (cavityTerm β d (F ω) i)).toReal)⁻¹
    simp_rw [heq]
    rw [← ENNReal.ofReal_tsum_of_nonneg hNN hsum, ENNReal.toReal_ofReal (tsum_nonneg hNN)]
    rfl

/-- Every bounded soft fixed-point law is the canonical boundary limit law. -/
theorem soft_cavity_law_eq_canonical {β d z : ℝ} (hβ : 0 < β) (hd : 0 < d) (hz : 0 < z)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hb : ∀ᵐ h ∂μ, h ∈ Icc 0 z⁻¹)
    (hfix : (markedSpacings μ).map (arrivalSoftOutput β d z) = μ) :
    μ = law.map (lower β d z []) := by
  let : IsProbabilityMeasure law := isProbabilityMeasure_law
  let : IsProbabilityMeasure (annotatedLaw μ) := isProbabilityMeasure_annotatedLaw μ
  let : IsProbabilityMeasure (law.map (lower β d z [])) :=
    Measure.isProbabilityMeasure_map (measurable_lower β d z []).aemeasurable
  let hSp : MeasurePreserving spacings (annotatedLaw μ) law :=
    ⟨measurable_spacings, map_spacings μ⟩
  let F (ω : Annotated) := lower β d z [] (spacings ω)
  have hF : Measurable F := (measurable_lower β d z []).comp measurable_spacings
  have hmapF : (annotatedLaw μ).map F = law.map (lower β d z []) := by
    change (annotatedLaw μ).map ((lower β d z []) ∘ spacings) = _
    rw [← Measure.map_map (measurable_lower β d z []) measurable_spacings, map_spacings μ]
  have hc : ∀ᵐ ω ∂annotatedLaw μ, Tendsto (fun n => withTerminals β d z n [] ω) atTop (𝓝 (F ω)) := by
    filter_upwards [ae_annotated_good hβ hd μ hb,
      hSp.quasiMeasurePreserving.tendsto_ae.eventually (ae_root_depth_same_limit hβ hd hz)] with ω hw hl
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le hl.1 hl.2
    · intro n
      exact (TreeBoundary.fromBoundary_between z child _ hz hw.1
        (weight_nonneg β d (spacings ω)) (terminals ω) hw.2 n []).1
    · intro n
      exact (TreeBoundary.fromBoundary_between z child _ hz hw.1
        (weight_nonneg β d (spacings ω)) (terminals ω) hw.2 n []).2
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  have hm₀ (n : ℕ) :
      ∫ ω, f (withTerminals β d z n [] ω) ∂annotatedLaw μ = ∫ h, f h ∂μ := by
    rw [← integral_map (measurable_withTerminals β d z n []).aemeasurable
      f.continuous.measurable.aestronglyMeasurable,
      mapped_withTerminals hβ hd hz μ hb hfix]
  have hm₁ :
      ∫ ω, f (F ω) ∂annotatedLaw μ = ∫ h, f h ∂law.map (lower β d z []) := by
    rw [← integral_map hF.aemeasurable f.continuous.measurable.aestronglyMeasurable, hmapF]
  have hDCT : Tendsto (fun n : ℕ => ∫ ω, f (withTerminals β d z n [] ω) ∂annotatedLaw μ)
      atTop (𝓝 (∫ ω, f (F ω) ∂annotatedLaw μ)) := tendsto_integral_of_dominated_convergence
    (μ := annotatedLaw μ) (fun _ : Annotated => ‖f‖)
    (fun n => (f.continuous.measurable.comp (measurable_withTerminals β d z n [])).aestronglyMeasurable)
    (integrable_const _) (fun n => .of_forall fun ω => f.norm_coe_le_norm _)
    (hc.mono fun ω h => (f.continuous.continuousAt (x := F ω)).tendsto.comp h)
  have heq :
      (fun n : ℕ => ∫ ω, f (withTerminals β d z n [] ω) ∂annotatedLaw μ) =
        fun _ => ∫ h, f h ∂μ := funext hm₀
  rw [heq] at hDCT
  exact (tendsto_nhds_unique tendsto_const_nhds hDCT).trans hm₁

/-- The positive-fugacity cavity equation has exactly one solution law with
support in the interval required by the manuscript. -/
theorem existsUnique_soft_cavity_law {β d z : ℝ} (hβ : 0 < β) (hd : 0 < d) (hz : 0 < z) :
    ∃! μ : Measure ℝ, IsProbabilityMeasure μ ∧
      (∀ᵐ h ∂μ, h ∈ Icc 0 z⁻¹) ∧
      (markedSpacings μ).map (arrivalSoftOutput β d z) = μ := by
  obtain ⟨μ, hprob, hsupp, hfixed⟩ := exists_soft_cavity_law hβ hd hz
  let : IsProbabilityMeasure μ := hprob
  have hsupp' : ∀ᵐ h ∂μ, h ∈ Icc 0 z⁻¹ := hsupp.mono fun _ h => ⟨h.1.le, h.2⟩
  refine ⟨μ, ⟨hprob, hsupp', hfixed⟩, fun ν hν => ?_⟩
  let : IsProbabilityMeasure ν := hν.1
  exact (soft_cavity_law_eq_canonical hβ hd hz ν hν.2.1 hν.2.2).trans
    (soft_cavity_law_eq_canonical hβ hd hz μ hsupp' hfixed).symm

end Certificate.CanonicalTree

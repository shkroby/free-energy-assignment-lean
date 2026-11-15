import Certificate.OverlapCanonicalOccupation
import Certificate.OverlapEmpiricalAssembly
import Certificate.OverlapEmpiricalLimits

/-! Removal of the degree and length cutoffs in the empirical occupation tests. -/

open Filter Finset MeasureTheory Set ProbabilityTheory
open scoped Topology

namespace Certificate.Overlap

open LocalExploration CanonicalTree

/-- The two occupation tests needed on each bounded-degree, finite-length tree. -/
def CanonicalOccupationTests (β d : ℝ) : Prop :=
  ∀ {z : ℝ} (hz : 0 < z) {R : ℕ}, 0 < R → ∀ D : ℕ,
    Tendsto (fun k => ∑' c : PlaneShapeCode (k+3), cutoffShapeMass d R c *
      ∫ x, c.shape.squareRowTestBCF D k β hz x
        ∂Measure.infinitePi (fun _ : c.shape.NonRootSlot => truncatedIntensity d R))
      atTop (𝓝 (∫ ω, min 1 (∑' i, (trimmedRootOccupation β d R z D ω i)^2) ∂law)) ∧
    ∀ {η : ℝ}, 0 < η → ∃ L : ℝ,
      Tendsto (fun k => ∑' c : PlaneShapeCode (k+3), cutoffShapeMass d R c *
        ∫ x, c.shape.smallOccupationTestBCF D k β η hz x
          ∂Measure.infinitePi (fun _ : c.shape.NonRootSlot => truncatedIntensity d R))
        atTop (𝓝 L) ∧
      L ≤ ∫ ω, firstThreeScore η (trimmedRootOccupation β d R z D ω) ∂law

/-- Cutoff removal and the hard limit give the uniform empirical estimates. -/
theorem retainedOverlapTestInput_of_canonicalTests
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {β d κ : ℝ}
    (hβ : 0 < β) (hd : 0 < d) (hκ : 0 < κ) (hμ : SmallCostTail μ κ d)
    (H : ProbabilityMeasure ℝ) (hH : IsCavityLaw β d (H : Measure ℝ))
    (hUnique : ∀ ν : Measure ℝ, IsCavityLaw β d ν → ν = (H : Measure ℝ))
    (hRoots : ∀ R : ℕ, 0 < R → ∀ D k : ℕ, ∀ᵐ C ∂iidCosts μ,
      Tendsto (fun n : ℕ =>
        let G := trimmedAssignmentGraph β d κ R n D C
        (((G.vertices \ trimmedAssignmentGoodRoots β d κ R n D k C).card : ℝ) / (n : ℝ)))
          atTop (𝓝 0))
    (hTests : CanonicalOccupationTests β d) :
    RetainedOverlapTestInput μ β d κ (cavityOverlap β d (H : Measure ℝ)) := by
  apply retainedOverlapTestInput_of_empirical hβ.le hκ.le hμ.1 hRoots
  intro δ hδ
  have hδ₄ : 0 < δ/4 := by positivity
  have hδ₆₄ : 0 < δ/64 := by positivity
  obtain ⟨η,hη,hηz⟩ := eventually_integral_firstThreeScore_full_lt hβ hd H hH hUnique hδ₆₄
  refine ⟨η,hη,?_⟩
  have hsz := (Metric.tendsto_nhds.mp
    (tendsto_cavityOverlap_of_hard_unique hβ hd H hH hUnique)) _ hδ₄
  filter_upwards [self_mem_nhdsWithin, hηz, hsz] with z hz hzThird hzSq
  have hz' : 0 < z := hz
  refine ⟨hz',?_⟩
  let Q := cavityOverlap β d (H : Measure ℝ)
  let sq (p : Environment → ℕ → ℝ) := ∫ ω, min 1 (∑' i, (p ω i)^2) ∂law
  let third (p : Environment → ℕ → ℝ) := ∫ ω, firstThreeScore η (p ω) ∂law
  let full := fullRootOccupation β d z
  let cut (R : ℕ) := cutoffRootOccupation β d R z
  let trim (R D : ℕ) := trimmedRootOccupation β d R z D
  have hzs : |sq full - Q| < δ/4 := by
    change |(∫ ω, min 1 (∑' i, (fullRootOccupation β d z ω i)^2) ∂law) - Q| < δ/4
    rw [integral_fullRootSquare_eq_cavityOverlap hβ hd hz']
    simpa only [Real.dist_eq] using hzSq
  have hrs : ∀ᶠ R : ℕ in atTop, |sq (cut R) - sq full| < δ/4 := by
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp
      (tendsto_integral_square_of_sqSum (fun R i => measurable_cutoffRootOccupation β d R z i)
        (ae_tendsto_cutoff_squareSum hβ hd hz'))) _ hδ₄
  have hrt := (tendsto_integral_firstThreeScore (η := η)
    (fun R i => measurable_cutoffRootOccupation β d R z i)
    (ae_tendsto_cutoff_occupations hβ hd hz')).eventually_lt_const
      (show third full < δ/32 by
        have hh : third full < δ/64 := hzThird
        linarith)
  filter_upwards [hrs, hrt, eventually_gt_atTop (0:ℕ)] with R hRs hRt hR
  have hds : ∀ᶠ D : ℕ in atTop, |sq (trim R D) - sq (cut R)| < δ/4 := by
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp
      (tendsto_integral_square_of_sqSum (fun D i => measurable_trimmedRootOccupation β d R z D i)
        (ae_tendsto_trimmed_squareSum hβ hd hz' R))) _ hδ₄
  have hdt := (tendsto_integral_firstThreeScore (η := η)
    (fun D i => measurable_trimmedRootOccupation β d R z D i)
    (ae_tendsto_trimmed_occupations hβ hd hz' R)).eventually_lt_const
      (show third (cut R) < δ/16 by
        have hh : third (cut R) < δ/32 := hRt
        linarith)
  filter_upwards [hds,hdt] with D hDs hDt
  have hQ : |sq (trim R D) - Q| < δ := by
    have h₁ := abs_sub_le (sq (trim R D)) (sq (cut R)) Q
    have h₂ := abs_sub_le (sq (cut R)) (sq full) Q
    linarith
  have hR' : 0 < (R:ℝ) := by exact_mod_cast hR
  obtain ⟨hSquare,hThird⟩ := hTests hz' hR D
  obtain ⟨L,hThird,hL⟩ := hThird hη
  constructor
  · have ha := ae_tendsto_centerSquare_of_treeTests hβ.le hd hκ hR' hz' hμ D hSquare
    filter_upwards [ha] with C hC
    have hlim := (continuous_abs.comp (continuous_id.sub
      (continuous_const (y := Q)))).continuousAt.tendsto.comp hC
    exact hlim.eventually_lt_const hQ
  · exact ae_eventually_badRows_fraction_le_of_treeTests hβ.le hd hκ hR' hz' hη hμ D
      (hL.trans_lt hDt) hThird

end Certificate.Overlap

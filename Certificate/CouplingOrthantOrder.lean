import Certificate.CouplingQuantiles
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-! The lower-orthant order on joint laws is closed for weak convergence. -/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

namespace Certificate

/-- Lower-orthant comparison for laws of two real coordinates. -/
def orthantLE (ρ σ : ProbabilityMeasure (ℝ × ℝ)) : Prop :=
  ∀ x y : ℝ, (ρ : Measure (ℝ × ℝ)) (Iic x ×ˢ Iic y) ≤
    (σ : Measure (ℝ × ℝ)) (Iic x ×ˢ Iic y)

theorem commonQuantileCoupling_greatest {ρ : ProbabilityMeasure (ℝ × ℝ)}
    {μ ν : ProbabilityMeasure ℝ} (hρ : ρ ∈ couplingLaws μ ν) :
    orthantLE ρ (commonQuantileCoupling μ ν) := by
  intro x y
  have hfst : (ρ : Measure (ℝ × ℝ)).map Prod.fst = (μ : Measure ℝ) :=
    congrArg (fun p : ProbabilityMeasure ℝ ↦ (p : Measure ℝ)) hρ.1
  have hsnd : (ρ : Measure (ℝ × ℝ)).map Prod.snd = (ν : Measure ℝ) :=
    congrArg (fun p : ProbabilityMeasure ℝ ↦ (p : Measure ℝ)) hρ.2
  have hL : (ρ : Measure (ℝ × ℝ)) (Iic x ×ˢ Iic y) ≤ (μ : Measure ℝ) (Iic x) := by
    rw [← hfst, Measure.map_apply measurable_fst measurableSet_Iic]
    exact measure_mono (fun _ hp ↦ hp.1)
  have hR : (ρ : Measure (ℝ × ℝ)) (Iic x ×ˢ Iic y) ≤ (ν : Measure ℝ) (Iic y) := by
    rw [← hsnd, Measure.map_apply measurable_snd measurableSet_Iic]
    exact measure_mono (fun _ hp ↦ hp.2)
  rw [commonQuantileCoupling_orthant, ENNReal.ofReal_min, cdf_eq_real, cdf_eq_real, Measure.real,
    Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _), ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact le_min hL hR

/-- Lower-orthant inequalities survive weak limits, including at atoms
of either limiting law. -/
theorem orthantLE_of_tendsto {ρ σ : ℕ → ProbabilityMeasure (ℝ × ℝ)}
    {r s : ProbabilityMeasure (ℝ × ℝ)}
    (hr : Tendsto ρ atTop (𝓝 r)) (hs : Tendsto σ atTop (𝓝 s))
    (h : ∀ n, orthantLE (ρ n) (σ n)) :
    orthantLE r s := by
  intro x y
  let c (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hc (n : ℕ) : 0 < c n := by dsimp [c]; positivity
  have hcLim : Tendsto c atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hcAnti : Antitone c := by
    intro a b h
    apply one_div_le_one_div_of_le (by positivity : 0 < (a : ℝ) + 1)
    exact add_le_add_left (Nat.cast_le.mpr h) 1
  let C (n : ℕ) := Iic (x + c n) ×ˢ Iic (y + c n)
  let O (n : ℕ) := Iio (x + c n) ×ˢ Iio (y + c n)
  have hCanti : Antitone C := by
    intro i j hij p hp
    exact ⟨hp.1.trans (add_le_add_right (hcAnti hij) x),
      hp.2.trans (add_le_add_right (hcAnti hij) y)⟩
  have hInter : (⋂ n, C n) = Iic x ×ˢ Iic y := by
    ext p
    constructor
    · intro hp
      have hpx : p.1 ≤ x + 0 := ge_of_tendsto (tendsto_const_nhds.add hcLim)
        (.of_forall fun n ↦ (mem_iInter.mp hp n).1)
      have hpy : p.2 ≤ y + 0 := ge_of_tendsto (tendsto_const_nhds.add hcLim)
        (.of_forall fun n ↦ (mem_iInter.mp hp n).2)
      exact ⟨mem_Iic.mpr (by simpa only [add_zero] using hpx),
        mem_Iic.mpr (by simpa only [add_zero] using hpy)⟩
    · intro hp
      exact mem_iInter.mpr fun n ↦ ⟨hp.1.trans (le_add_of_nonneg_right (hc n).le),
        hp.2.trans (le_add_of_nonneg_right (hc n).le)⟩
  have hlim := tendsto_measure_iInter_atTop (μ := (s : Measure (ℝ × ℝ))) (s := C)
    (fun _ ↦ (measurableSet_Iic.prod measurableSet_Iic).nullMeasurableSet) hCanti
    ⟨0, measure_ne_top _ _⟩
  rw [hInter] at hlim
  apply ge_of_tendsto hlim
  refine .of_forall fun n ↦ ?_
  have h₁ : (r : Measure (ℝ × ℝ)) (Iic x ×ˢ Iic y) ≤ (r : Measure (ℝ × ℝ)) (O n) :=
    measure_mono fun _ hp ↦ ⟨hp.1.trans_lt (lt_add_of_pos_right _ (hc n)),
      hp.2.trans_lt (lt_add_of_pos_right _ (hc n))⟩
  have h₂ := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hr (G := O n)
    (isOpen_Iio.prod isOpen_Iio)
  have h₃ : liminf (fun i ↦ (ρ i : Measure (ℝ × ℝ)) (O n)) atTop ≤
      limsup (fun i ↦ (σ i : Measure (ℝ × ℝ)) (C n)) atTop := by
    refine liminf_le_limsup_of_frequently_le ?_
      ⟨0, Eventually.of_forall fun _ ↦ zero_le⟩
      ⟨∞, Eventually.of_forall fun _ ↦ le_top⟩
    exact (Eventually.of_forall fun i ↦
      (measure_mono (show O n ⊆ C n from fun _ hp ↦
        ⟨mem_Iic.mpr (mem_Iio.mp hp.1).le, mem_Iic.mpr (mem_Iio.mp hp.2).le⟩)).trans
        (h i (x + c n) (y + c n))).frequently
  have h₄ := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hs (F := C n)
    (isClosed_Iic.prod isClosed_Iic)
  exact h₁.trans (h₂.trans (h₃.trans h₄))

theorem isClosed_orthantLE :
    IsClosed {p : ProbabilityMeasure (ℝ × ℝ) × ProbabilityMeasure (ℝ × ℝ) | orthantLE p.1 p.2} := by
  apply IsSeqClosed.isClosed
  intro p q hp hq
  exact orthantLE_of_tendsto ((continuous_fst.tendsto q).comp hq)
    ((continuous_snd.tendsto q).comp hq) hp

theorem orthantLE_antisymm {ρ σ : ProbabilityMeasure (ℝ × ℝ)}
    (h : orthantLE ρ σ) (h' : orthantLE σ ρ) : ρ = σ := by
  apply Subtype.ext
  change (ρ : Measure (ℝ × ℝ)) = (σ : Measure (ℝ × ℝ))
  let S : Set (Set ℝ) := range Iic
  let C := image2 (· ×ˢ ·) S S
  have hS : IsCountablySpanning S := by
    refine ⟨fun n ↦ Iic (n : ℝ), fun n ↦ mem_range_self _, ?_⟩
    apply eq_univ_of_forall
    intro x
    obtain ⟨n, hn⟩ := exists_nat_ge x
    exact mem_iUnion.mpr ⟨n, hn⟩
  have hsGen : MeasurableSpace.generateFrom S = (inferInstance : MeasurableSpace ℝ) :=
    (borel_eq_generateFrom_Iic (α := ℝ)).symm.trans BorelSpace.measurable_eq.symm
  obtain ⟨B, hB, hCover⟩ := hS.prod hS
  have hPi : IsPiSystem C := by
    rintro _ ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩ _ ⟨_, ⟨c, rfl⟩, _, ⟨d, rfl⟩, rfl⟩ _
    refine ⟨_, mem_range_self (min a c), _, mem_range_self (min b d), ?_⟩
    ext p
    simp only [mem_inter_iff, mem_prod, mem_Iic, le_min_iff]
    tauto
  apply Measure.ext_of_generateFrom_of_iUnion C B
    (generateFrom_eq_prod hsGen hsGen hS hS).symm hPi hCover hB
    (fun i ↦ measure_ne_top (ρ : Measure (ℝ × ℝ)) (B i))
  rintro _ ⟨_, ⟨x, rfl⟩, _, ⟨y, rfl⟩, rfl⟩
  exact le_antisymm (h x y) (h' x y)

end Certificate

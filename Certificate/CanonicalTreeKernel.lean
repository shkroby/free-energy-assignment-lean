import Certificate.CanonicalTree
import Certificate.WeightedSoftExchange

/-! The canonical boundary argument for cutoff edge weights. -/

open Filter MeasureTheory Set
open scoped Topology ENNReal

namespace Certificate.CanonicalTree

/-- A scalar length weight applied to each arrival in the tree. -/
noncomputable def weightFor (K : ℝ → ℝ) (d : ℝ) (ω : Environment) (v : Vertex) (i : ℕ) : ℝ :=
  K (arrivalLength d (ω v) i)

theorem ae_summable_weightFor {K : ℝ → ℝ} {d : ℝ}
    (hK : ∀ᵐ E ∂exponentialSpacings, Summable (fun i => K (arrivalLength d E i))) :
    ∀ᵐ ω ∂law, ∀ v, Summable (weightFor K d ω v) := by
  let : IsProbabilityMeasure exponentialSpacings := isProbabilityMeasure_exponentialSpacings
  apply ae_all_iff.mpr
  intro v
  have H := measurePreserving_eval_infinitePi (fun _ : Vertex => exponentialSpacings) v
  exact H.quasiMeasurePreserving.tendsto_ae.eventually hK

/-- The two extremal approximants with a prescribed length weight. -/
noncomputable def depthFor (K : ℝ → ℝ) (d z : ℝ) (n : ℕ) (v : Vertex) (ω : Environment) :
    ℝ × ℝ := TreeBoundary.bounds z child (weightFor K d ω) n v

theorem measurable_depthFor {K : ℝ → ℝ} (hK : Measurable K)
    (d z : ℝ) (n : ℕ) (v : Vertex) : Measurable (depthFor K d z n v) := by
  have hweight (v : Vertex) (i : ℕ) : Measurable (fun ω => weightFor K d ω v i) := by
    apply hK.comp
    unfold arrivalLength
    fun_prop
  induction n generalizing v with
  | zero => exact measurable_const
  | succ n ih =>
    unfold depthFor
    simp only [TreeBoundary.bounds]
    exact
      ((measurable_const.add (Measurable.tsum fun i =>
        (hweight v i).mul (ih (child v i)).snd)).inv).prodMk
      ((measurable_const.add (Measurable.tsum fun i =>
        (hweight v i).mul (ih (child v i)).fst)).inv)

private theorem depthFor_branch (K : ℝ → ℝ) (d z : ℝ) (n : ℕ)
    (v : Vertex) (ω : Environment) (i : ℕ) :
    depthFor K d z n v (branch i ω) = depthFor K d z n (i :: v) ω := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    change
      (TreeBoundary.update z (weightFor K d (branch i ω) v)
          (fun j => (depthFor K d z n (child v j) (branch i ω)).2),
        TreeBoundary.update z (weightFor K d (branch i ω) v)
          (fun j => (depthFor K d z n (child v j) (branch i ω)).1)) =
      (TreeBoundary.update z (weightFor K d ω (i :: v))
          (fun j => (depthFor K d z n (child (i :: v) j) ω).2),
        TreeBoundary.update z (weightFor K d ω (i :: v))
          (fun j => (depthFor K d z n (child (i :: v) j) ω).1))
    have hchild (j : ℕ) : child (i :: v) j = i :: child v j := rfl
    have hweight : weightFor K d (branch i ω) v = weightFor K d ω (i :: v) := rfl
    simp only [ih, hchild, hweight]

noncomputable def lowerFor (K : ℝ → ℝ) (d z : ℝ) (v : Vertex) (ω : Environment) : ℝ :=
  ⨆ n, (depthFor K d z n v ω).1

noncomputable def upperFor (K : ℝ → ℝ) (d z : ℝ) (v : Vertex) (ω : Environment) : ℝ :=
  ⨅ n, (depthFor K d z n v ω).2

theorem measurable_lowerFor {K : ℝ → ℝ} (hK : Measurable K) (d z : ℝ) (v : Vertex) :
    Measurable (lowerFor K d z v) :=
  Measurable.iSup fun n => (measurable_depthFor hK d z n v).fst

theorem measurable_upperFor {K : ℝ → ℝ} (hK : Measurable K) (d z : ℝ) (v : Vertex) :
    Measurable (upperFor K d z v) :=
  Measurable.iInf fun n => (measurable_depthFor hK d z n v).snd

private theorem lowerFor_branch (K : ℝ → ℝ) (d z : ℝ) (v : Vertex) (ω : Environment) (i : ℕ) :
    lowerFor K d z v (branch i ω) = lowerFor K d z (i :: v) ω := by
  simp only [lowerFor, depthFor_branch]

private theorem upperFor_branch (K : ℝ → ℝ) (d z : ℝ) (v : Vertex) (ω : Environment) (i : ℕ) :
    upperFor K d z v (branch i ω) = upperFor K d z (i :: v) ω := by
  simp only [upperFor, depthFor_branch]

theorem ae_boundary_limitsFor {K : ℝ → ℝ} {d z : ℝ} (hz : 0 < z)
    (hK₀ : ∀ x, 0 ≤ K x)
    (hKS : ∀ᵐ E ∂exponentialSpacings, Summable (fun i => K (arrivalLength d E i))) :
    ∀ᵐ ω ∂law, ∀ v,
      Tendsto (fun n => (depthFor K d z n v ω).1) atTop (𝓝 (lowerFor K d z v ω)) ∧
      Tendsto (fun n => (depthFor K d z n v ω).2) atTop (𝓝 (upperFor K d z v ω)) ∧
      0 < lowerFor K d z v ω ∧ lowerFor K d z v ω ≤ upperFor K d z v ω ∧
      upperFor K d z v ω ≤ z⁻¹ ∧
      lowerFor K d z v ω = TreeBoundary.update z (weightFor K d ω v)
        (fun i => upperFor K d z (child v i) ω) ∧
      upperFor K d z v ω = TreeBoundary.update z (weightFor K d ω v)
        (fun i => lowerFor K d z (child v i) ω) := by
  filter_upwards [ae_summable_weightFor hKS] with ω hw
  have hw₀ (v : Vertex) (i : ℕ) : 0 ≤ weightFor K d ω v i := hK₀ _
  obtain ⟨L, U, h⟩ := TreeBoundary.exists_boundary_limits z child (weightFor K d ω) hz hw hw₀
  have hL (v : Vertex) : lowerFor K d z v ω = L v := by
    refine tendsto_nhds_unique ?_ (h v).1
    refine tendsto_atTop_ciSup
      (monotone_nat_of_le_succ fun n =>
        (TreeBoundary.bounds_step z child (weightFor K d ω) hz hw hw₀ n v).1) ?_
    refine ⟨z⁻¹, fun x ⟨n, hn⟩ => ?_⟩
    rw [← hn]
    exact (TreeBoundary.bounds_mem z child (weightFor K d ω) hz hw hw₀ n v).2.1.trans
      (TreeBoundary.bounds_mem z child (weightFor K d ω) hz hw hw₀ n v).2.2
  have hU (v : Vertex) : upperFor K d z v ω = U v := by
    refine tendsto_nhds_unique ?_ (h v).2.1
    refine tendsto_atTop_ciInf
      (antitone_nat_of_succ_le fun n =>
        (TreeBoundary.bounds_step z child (weightFor K d ω) hz hw hw₀ n v).2) ?_
    refine ⟨0, fun x ⟨n, hn⟩ => ?_⟩
    rw [← hn]
    exact (TreeBoundary.bounds_mem z child (weightFor K d ω) hz hw hw₀ n v).1.trans
      (TreeBoundary.bounds_mem z child (weightFor K d ω) hz hw hw₀ n v).2.1
  intro v
  simp only [hL, hU]
  exact h v

private theorem map_updateFor {g : Environment → ℝ} (hg : Measurable g)
    {K : ℝ → ℝ} {d z : ℝ} (hK : Measurable K) (hK₀ : ∀ x, 0 ≤ K x)
    (hKS : ∀ᵐ E ∂exponentialSpacings, Summable (fun i => K (arrivalLength d E i)))
    (hgb : ∀ᵐ ω ∂law, g ω ∈ Icc 0 z⁻¹) :
    (markedSpacings (law.map g)).map (kernelSoftOutput K d z) =
      law.map (fun ω => TreeBoundary.update z (weightFor K d ω [])
        (fun i => g (branch i ω))) := by
  let F (ω : Environment) : ArrivalConfiguration := (ω [], fun i => g (branch i ω))
  have hf : Measurable F :=
    (measurable_pi_apply []).prodMk
      (measurable_pi_iff.mpr fun i => hg.comp (measurable_branch i))
  have hm : law.map F = markedSpacings (law.map g) := map_root_marks hg
  rw [← hm, Measure.map_map (measurable_kernelSoftOutput d z hK) hf]
  apply Measure.map_congr
  have hbranch : ∀ᵐ ω ∂law, ∀ i, g (branch i ω) ∈ Icc 0 z⁻¹ := by
    apply ae_all_iff.mpr
    exact fun i => (measurePreserving_branch i).quasiMeasurePreserving.tendsto_ae.eventually hgb
  filter_upwards [hbranch, ae_summable_weightFor hKS] with ω hmarks hw
  let f (i : ℕ) := weightFor K d ω [] i * g (branch i ω)
  have hnn (i : ℕ) : 0 ≤ f i := mul_nonneg (hK₀ _) (hmarks i).1
  have hsum : Summable f := ((hw []).mul_right z⁻¹).of_nonneg_of_le hnn
    (fun i => mul_le_mul_of_nonneg_left (hmarks i).2 (hK₀ _))
  change (z + (∑' i, ENNReal.ofReal (f i)).toReal)⁻¹ = (z + ∑' i, f i)⁻¹
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn hsum, ENNReal.toReal_ofReal (tsum_nonneg hnn)]

/-- Coalescence for a general summable length kernel, including a hard length cutoff. -/
theorem ae_lowerFor_eq_upperFor {K : ℝ → ℝ} {d z : ℝ}
    (hK : Measurable K) (hK₀ : ∀ x, 0 ≤ K x) (hd : 0 < d) (hz : 0 < z)
    (hKS : ∀ᵐ E ∂exponentialSpacings, Summable (fun i => K (arrivalLength d E i))) :
    lowerFor K d z [] =ᵐ[law] upperFor K d z [] := by
  let : IsProbabilityMeasure law := isProbabilityMeasure_law
  have hs := ae_boundary_limitsFor hz hK₀ hKS
  have hbL : ∀ᵐ ω ∂law, lowerFor K d z [] ω ∈ Icc 0 z⁻¹ :=
    hs.mono fun _ h => ⟨(h []).2.2.1.le, (h []).2.2.2.1.trans (h []).2.2.2.2.1⟩
  have hbU : ∀ᵐ ω ∂law, upperFor K d z [] ω ∈ Icc 0 z⁻¹ :=
    hs.mono fun _ h => ⟨(h []).2.2.1.le.trans (h []).2.2.2.1, (h []).2.2.2.2.1⟩
  have hb : ∀ᵐ ω ∂law, 0 ≤ lowerFor K d z [] ω ∧
      lowerFor K d z [] ω ≤ upperFor K d z [] ω ∧ upperFor K d z [] ω ≤ z⁻¹ :=
    hs.mono fun _ h => ⟨(h []).2.2.1.le, (h []).2.2.2.1, (h []).2.2.2.2.1⟩
  apply ae_eq_of_ordered_crossed_kernel_recursions law hK hK₀ hd hz hKS
    (measurable_lowerFor hK d z []) (measurable_upperFor hK d z []) hb
  · rw [map_updateFor (measurable_upperFor hK d z []) hK hK₀ hKS hbU]
    apply Measure.map_congr
    filter_upwards [hs] with ω h
    simpa only [upperFor_branch, child, List.nil_append] using (h []).2.2.2.2.2.1.symm
  · rw [map_updateFor (measurable_lowerFor hK d z []) hK hK₀ hKS hbL]
    apply Measure.map_congr
    filter_upwards [hs] with ω h
    simpa only [lowerFor_branch, child, List.nil_append] using (h []).2.2.2.2.2.2.symm

/-- The length cut keeps all arrivals at distance at most `R`. -/
noncomputable def cutoffKernel (β R : ℝ) (x : ℝ) : ℝ :=
  if x ≤ R then Real.exp (-β * x) else 0

theorem measurable_cutoffKernel (β R : ℝ) : Measurable (cutoffKernel β R) := by
  unfold cutoffKernel
  exact (by fun_prop : Measurable (fun x : ℝ => Real.exp (-β * x))).ite
    measurableSet_Iic measurable_const

theorem cutoffKernel_nonneg (β R x : ℝ) : 0 ≤ cutoffKernel β R x := by
  unfold cutoffKernel
  split <;> positivity

theorem ae_summable_cutoffKernel {β d : ℝ} (hβ : 0 < β) (hd : 0 < d) (R : ℝ) :
    ∀ᵐ E ∂exponentialSpacings, Summable (fun i => cutoffKernel β R (arrivalLength d E i)) := by
  filter_upwards [ae_summable_arrival_weights hd hβ] with E h
  apply h.of_nonneg_of_le (fun i => cutoffKernel_nonneg β R _) (fun i => ?_)
  unfold cutoffKernel
  split
  · exact le_rfl
  · exact Real.exp_nonneg _

theorem ae_cutoff_lower_eq_upper {β d z : ℝ} (hβ : 0 < β) (hd : 0 < d)
    (hz : 0 < z) (R : ℝ) :
    lowerFor (cutoffKernel β R) d z [] =ᵐ[law] upperFor (cutoffKernel β R) d z [] :=
  ae_lowerFor_eq_upperFor (measurable_cutoffKernel β R) (cutoffKernel_nonneg β R)
    hd hz (ae_summable_cutoffKernel hβ hd R)

end Certificate.CanonicalTree

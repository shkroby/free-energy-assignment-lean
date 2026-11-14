import Certificate.CanonicalSoftUniqueness
import Certificate.CanonicalTreeRegularity

/-! Coalescence on a single tree realization for all positive fugacities. -/

open Filter Set MeasureTheory
open scoped Topology

namespace Certificate.CanonicalTree

theorem ae_lower_eq_upper_at_vertices {β d z : ℝ} (hβ : 0 < β) (hd : 0 < d) (hz : 0 < z) :
    ∀ᵐ ω ∂law, ∀ v, lower β d z v ω = upper β d z v ω := by
  apply ae_all_iff.mpr
  intro v
  induction v with
  | nil => exact ae_lower_eq_upper hβ hd hz
  | cons i v ih =>
    have hb := (measurePreserving_branch i).quasiMeasurePreserving.tendsto_ae.eventually ih
    filter_upwards [hb] with ω hω
    change lower β d z v (branch i ω) = upper β d z v (branch i ω) at hω
    simpa only [lower_branch, upper_branch] using hω

/-- The canonical extrema coincide on one almost-sure event simultaneously at
all vertices and all positive fugacities. -/
theorem ae_extremal_eq_all_logFugacities {β d : ℝ} (hβ : 0 < β) (hd : 0 < d) :
    ∀ᵐ ω ∂law, ∀ t : ℝ, ∀ v, lower β d (Real.exp t) v ω = upper β d (Real.exp t) v ω := by
  have hrat : ∀ᵐ ω ∂law, ∀ q : ℚ, ∀ v,
      lower β d (Real.exp (q : ℝ)) v ω = upper β d (Real.exp (q : ℝ)) v ω :=
    ae_all_iff.mpr fun _ => ae_lower_eq_upper_at_vertices hβ hd (Real.exp_pos _)
  filter_upwards [hrat, ae_extremal_logLipschitz hβ hd] with ω hω hreg
  intro t v
  let f (s : ℝ) := Real.log (lower β d (Real.exp s) v ω)
  let g (s : ℝ) := Real.log (upper β d (Real.exp s) v ω)
  have hclosed : IsClosed {s | f s = g s} :=
    isClosed_eq (hreg v).2.1.continuous (hreg v).2.2.continuous
  have hsubset : Set.range ((↑) : ℚ → ℝ) ⊆ {s | f s = g s} := by
    rintro _ ⟨q, rfl⟩
    exact congrArg Real.log (hω q v)
  have ht : t ∈ closure (Set.range ((↑) : ℚ → ℝ)) := by rw [Rat.denseRange_cast.closure_range]; trivial
  exact Real.log_injOn_pos ((hreg v).1 t).1 ((hreg v).1 t).2
    (hclosed.closure_subset_iff.mpr hsubset ht)

end Certificate.CanonicalTree

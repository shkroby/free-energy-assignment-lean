import Certificate.CanonicalCutoffBracketLaw
import Certificate.CanonicalPlaneShapeLaw

/-! The finite interval of retained child indices on the Poisson tree. -/

open Filter MeasureTheory Set
open scoped ENNReal

namespace Certificate.CanonicalTree

theorem ae_arrivalLength_le_iff_lt_cutoffOffspringNat {d R : ℝ} (hd : 0 < d) (hR : 0 ≤ R) :
    ∀ᵐ ω ∂law, ∀ v i, arrivalLength d (ω v) i ≤ R ↔ i < cutoffOffspringNat d R (ω v) := by
  let : IsProbabilityMeasure exponentialSpacings := isProbabilityMeasure_exponentialSpacings
  apply ae_all_iff.mpr
  intro v
  have hp := (measurePreserving_eval_infinitePi (fun _ : Vertex => exponentialSpacings) v)
    |>.quasiMeasurePreserving.tendsto_ae
  filter_upwards [hp.eventually ae_expSpacing_pos, hp.eventually (ae_cutoffOffspring_eq_nat hd hR)]
    with ω hpos hfinite
  unfold cutoffOffspringNat
  rw [dif_pos hfinite]
  let p : Spacings × (ℕ → Unit) := (ω v, fun _ => ())
  have hcount : p ∈ arrivalWindowCountEvent d R hfinite.choose := hfinite.choose_spec
  intro i
  have hlen : 0 < arrivalLength d (ω v) i := by
    unfold arrivalLength
    exact Real.rpow_pos_of_pos (Finset.sum_pos (fun j _ => hpos j) Finset.nonempty_range_add_one) _
  have h := markedArrivalPoint_mem_window_iff_of_count (i := i) hd hpos hcount
  simpa only [p, arrivalWindow, markedArrivalPoint, Set.mem_prod, Set.mem_univ, and_true,
    Set.mem_Ioc, hlen, true_and] using h

theorem ae_cutoffKernel_eq_zero_off_range {d R : ℝ} (hd : 0 < d) (hR : 0 ≤ R) (β : ℝ) :
    ∀ᵐ ω ∂law, ∀ v i, i ∉ Finset.range (cutoffOffspringNat d R (ω v)) →
      weightFor (cutoffKernel β R) d ω v i = 0 := by
  filter_upwards [ae_arrivalLength_le_iff_lt_cutoffOffspringNat hd hR] with ω hω v i hi
  exact if_neg (fun h => hi (Finset.mem_range.mpr ((hω v i).mp h)))

end Certificate.CanonicalTree

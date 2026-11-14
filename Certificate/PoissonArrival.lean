import Certificate.Arrivals
import Certificate.PoissonIndexedGap
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Partitioning positive time by the exponential arrivals

The intervals between consecutive arrivals cover positive time up to their
null endpoints. This identifies the sum of the split-gap integrals with a
single integral over `(0,∞)`.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators

namespace Certificate

/-- The cumulative time after the first `n` spacings. -/
def arrivalPrefix (ω : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, ω j

@[simp] theorem arrivalPrefix_zero (ω : ℕ → ℝ) : arrivalPrefix ω 0 = 0 := by
  simp [arrivalPrefix]

theorem arrivalPrefix_succ (ω : ℕ → ℝ) (n : ℕ) :
    arrivalPrefix ω (n+1) = arrivalPrefix ω n + ω n :=
  Finset.sum_range_succ ..

@[fun_prop] theorem measurable_arrivalPrefix (n : ℕ) :
    Measurable (fun (ω : ℕ → ℝ) => arrivalPrefix ω n) := by
  unfold arrivalPrefix
  fun_prop

private theorem arrivalPrefix_mono (ω : ℕ → ℝ) (hpos : ∀ n, 0 < ω n) :
    Monotone (arrivalPrefix ω) :=
  monotone_nat_of_le_succ (fun n => by
    rw [arrivalPrefix_succ]
    exact le_add_of_nonneg_right (hpos n).le)

private theorem arrivalPrefix_ioc_disjoint (ω : ℕ → ℝ) (hpos : ∀ n, 0 < ω n) :
    Pairwise (fun i j : ℕ =>
      Disjoint (Ioc (arrivalPrefix ω i) (arrivalPrefix ω (i+1)))
        (Ioc (arrivalPrefix ω j) (arrivalPrefix ω (j+1)))) := by
  have h (i j : ℕ) (hij : i < j) :
      Disjoint (Ioc (arrivalPrefix ω i) (arrivalPrefix ω (i+1)))
        (Ioc (arrivalPrefix ω j) (arrivalPrefix ω (j+1))) := by
    exact Set.disjoint_left.mpr (fun _ hi hj =>
      hj.1.not_ge (hi.2.trans (arrivalPrefix_mono ω hpos (Nat.succ_le_of_lt hij))))
  intro i j hij
  rcases lt_or_gt_of_ne hij with hj | hj
  · exact h i j hj
  · exact (h j i hj).symm

private theorem arrivalPrefix_ioc_union (ω : ℕ → ℝ) (hpos : ∀ n, 0 < ω n)
    (hunbounded : ∀ t : ℝ, ∃ n, t ≤ arrivalPrefix ω n) :
    (⋃ i, Ioc (arrivalPrefix ω i) (arrivalPrefix ω (i+1))) = Ioi 0 := by
  ext x
  simp only [mem_iUnion, mem_Ioc, mem_Ioi]
  constructor
  · rintro ⟨i, hlo, _⟩
    have hp := arrivalPrefix_mono ω hpos (Nat.zero_le i)
    rw [arrivalPrefix_zero] at hp
    exact hp.trans_lt hlo
  · intro hx
    let n := Nat.find (hunbounded x)
    have hn : x ≤ arrivalPrefix ω n := Nat.find_spec (hunbounded x)
    have hn0 : n ≠ 0 := by
      rintro h
      rw [h, arrivalPrefix_zero] at hn
      exact hx.not_ge hn
    obtain ⟨i, hni⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    refine ⟨i, ?_, ?_⟩
    · apply lt_of_not_ge
      have hlt : i < n := by rw [hni]; exact Nat.lt_succ_self i
      exact Nat.find_min (hunbounded x) hlt
    · change x ≤ arrivalPrefix ω i.succ
      rw [← hni]
      exact hn

private theorem lintegral_translate_gap (p s : ℝ)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ a in Ioo 0 s, f (p+a)) = ∫⁻ t in Ioc p (p+s), f t := by
  rw [← Measure.restrict_congr_set (Ioo_ae_eq_Ioc (μ := volume)),
    ← lintegral_indicator measurableSet_Ioo, ← lintegral_indicator measurableSet_Ioo]
  have hmf : Measurable ((Ioo p (p+s)).indicator f) := hf.indicator measurableSet_Ioo
  calc
    _ = ∫⁻ a, (Ioo p (p+s)).indicator f (p+a) := by
      apply lintegral_congr
      intro a
      have h : p+a ∈ Ioo p (p+s) ↔ a ∈ Ioo 0 s := by
        simp only [mem_Ioo, lt_add_iff_pos_right, add_lt_add_iff_left]
      by_cases ha : a ∈ Ioo 0 s
      · simp only [indicator_of_mem ha, indicator_of_mem (h.mpr ha)]
      · simp only [indicator_of_notMem ha, indicator_of_notMem (mt h.mp ha)]
    _ = _ := (measurePreserving_add_left (volume : Measure ℝ) p).lintegral_comp hmf

/-- Summing the test integrals over the split position in each gap is the
integral of the test over all positive time. -/
theorem arrivalGap_partition_lintegral (ω : ℕ → ℝ) (hpos : ∀ n, 0 < ω n)
    (hunbounded : ∀ t : ℝ, ∃ n, t ≤ arrivalPrefix ω n)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∑' i, ∫⁻ a in Ioo 0 (ω i), f (arrivalPrefix ω i + a)) =
      ∫⁻ t in Ioi (0:ℝ), f t := by
  have h (i : ℕ) : (∫⁻ a in Ioo 0 (ω i), f (arrivalPrefix ω i + a)) =
      ∫⁻ t in Ioc (arrivalPrefix ω i) (arrivalPrefix ω (i+1)), f t := by
    rw [arrivalPrefix_succ]
    exact lintegral_translate_gap _ _ f hf
  simp_rw [h]
  rw [← lintegral_iUnion (fun _ => measurableSet_Ioc) (arrivalPrefix_ioc_disjoint ω hpos),
    arrivalPrefix_ioc_union ω hpos hunbounded]

/-- The cumulative exponential spacings are unbounded almost surely. -/
theorem ae_arrivalPrefix_unbounded :
    ∀ᵐ ω ∂exponentialSpacings, ∀ t : ℝ, ∃ n, t ≤ arrivalPrefix ω n := by
  obtain ⟨c, hc, hlin⟩ := ae_arrival_partial_sum_linear
  filter_upwards [hlin] with ω hω
  obtain ⟨N, hN⟩ := eventually_atTop.mp hω
  intro t
  obtain ⟨k, hk⟩ := exists_nat_ge (t/c)
  refine ⟨max k N, ?_⟩
  have hmul : t ≤ (k : ℝ) * c := (div_le_iff₀ hc).mp hk
  have hn : (k : ℝ) ≤ (max k N : ℕ) := Nat.cast_le.mpr (le_max_left k N)
  have hle : c * (max k N : ℕ) ≤ arrivalPrefix ω (max k N) :=
    hN (max k N) (le_max_right k N)
  exact (hmul.trans (mul_le_mul_of_nonneg_right hn hc.le)).trans
    (by rw [mul_comm]; exact hle)

/-- The split positions partition positive time for almost every canonical
spacing sequence. The statement is simultaneous for all measurable
nonnegative tests. -/
theorem ae_arrivalGap_partition_lintegral :
    ∀ᵐ ω ∂exponentialSpacings, ∀ f : ℝ → ℝ≥0∞, Measurable f →
      (∑' i, ∫⁻ a in Ioo 0 (ω i), f (arrivalPrefix ω i + a)) =
        ∫⁻ t in Ioi (0:ℝ), f t := by
  filter_upwards [ae_expSpacing_pos, ae_arrivalPrefix_unbounded] with ω hp hu
  exact arrivalGap_partition_lintegral ω hp hu

end Certificate

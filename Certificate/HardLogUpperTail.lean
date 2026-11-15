import Certificate.ArrivalHardCoupling
import Certificate.ArrivalMedianTail

/-!
# Upper logarithmic tail of a hard cavity law

Positive marks supply a fixed threshold exceeded by at least half their
mass. The first qualifying child then gives a stretched exponential upper
tail on the canonical arrival law. The threshold can depend on the law.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace Certificate

/-- A positive law has a nonpositive lower bound for a log median. -/
theorem exists_nonpositive_log_median_lower_bound {β : ℝ} (hβ : 0 < β)
    (μ : Measure ℝ) (hpos : μ (Ioi 0) = 1) :
    ∃ b : ℝ, b ≤ 0 ∧ 1 / 2 ≤ (μ (Ici (Real.exp (β*b)))).toReal := by
  let S (b : ℝ) := Ici (Real.exp (β*b))
  have hm : Antitone S := by
    intro a b hab
    apply Ici_subset_Ici.mpr
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hab hβ.le)
  have hS : (⋃ b, S b) = Ioi 0 := by
    ext x
    simp only [mem_iUnion, mem_Ioi]
    constructor
    · rintro ⟨b, hb⟩
      exact (Real.exp_pos (β*b)).trans_le hb
    · intro hx
      refine ⟨Real.log x / β, ?_⟩
      change Real.exp (β * (Real.log x / β)) ≤ x
      rw [show β * (Real.log x / β) = Real.log x by field_simp,
        Real.exp_log hx]
  have hμ : Tendsto (fun b => μ (S b)) atBot (𝓝 1) := by
    simpa only [Function.comp_def, hS, hpos] using
      (tendsto_measure_iUnion_atBot (μ := μ) hm)
  have hReal : Tendsto (fun b => (μ (S b)).toReal) atBot (𝓝 1) := by
    simpa only [Function.comp_def, ENNReal.toReal_one] using
      (ENNReal.continuousAt_toReal ENNReal.one_ne_top).tendsto.comp hμ
  have hev : ∀ᶠ b in (atBot : Filter ℝ), 1 / 2 < (μ (S b)).toReal :=
    (tendsto_order.mp hReal).1 (1 / 2) (by norm_num)
  obtain ⟨b, hb⟩ := eventually_atBot.mp hev
  exact ⟨min b 0, min_le_right _ _, (hb _ (min_le_left _ _)).le⟩

/-- A hard cavity law has a finite positive extended outgoing sum almost
surely. This follows even by comparing the positive part of the real series
against its unsigned absolute series. -/
theorem ae_hard_arrivalWeightedSum_spec {β d : ℝ} {μ : Measure ℝ}
    (h : IsCavityLaw β d μ) :
    ∀ᵐ ω ∂markedSpacings μ, arrivalWeightedSum β d ω ≠ ∞ ∧
      0 < (arrivalWeightedSum β d ω).toReal := by
  filter_upwards [h.2.2.1] with ω hω
  let f := cavityTerm β d ω
  let g (i : ℕ) := max (f i) 0
  have hg (i : ℕ) : 0 ≤ g i := le_max_right _ _
  have hs : Summable g := hω.1.abs.of_nonneg_of_le hg (fun i =>
    max_le (le_abs_self (f i)) (abs_nonneg (f i)))
  have hg_pos : 0 < ∑' i, g i :=
    hω.2.trans_le (hω.1.tsum_le_tsum (fun i => le_max_left _ _) hs)
  have he (i : ℕ) : ENNReal.ofReal (f i) = ENNReal.ofReal (g i) :=
    by simp [g, ENNReal.ofReal_max]
  have hsum : arrivalWeightedSum β d ω = ENNReal.ofReal (∑' i, g i) := by
    change (∑' i, ENNReal.ofReal (f i)) = _
    simp_rw [he]
    exact (ENNReal.ofReal_tsum_of_nonneg hg hs).symm
  rw [hsum, ENNReal.toReal_ofReal hg_pos.le]
  exact ⟨ENNReal.ofReal_ne_top, hg_pos⟩

/-- Beyond a law-dependent threshold, the upper tail has the stretched
exponential form of the first qualifying child estimate. -/
theorem hard_cavity_log_upperTail_eventually {β d : ℝ} (hd : 0 < d) (hβ : 0 < β)
    {μ : Measure ℝ} (h : IsCavityLaw β d μ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, 2*B ≤ x →
      μ (Ioi (Real.exp (β*x))) ≤ ENNReal.ofReal (Real.exp (-((x / 2)^d / 2))) := by
  let : IsProbabilityMeasure μ := h.1
  obtain ⟨b, hb, hm⟩ := exists_nonpositive_log_median_lower_bound hβ μ h.2.1
  refine ⟨-b, neg_nonneg.mpr hb, fun x hx => ?_⟩
  exact arrival_log_upperTail_of_median_lower_bound hd hβ le_rfl (neg_nonneg.mpr hb)
    μ ((ae_hard_arrivalWeightedSum_spec h).mono (fun _ hω => hω.1))
    (map_arrivalSoftOutput_zero_of_IsCavityLaw h) hm (by rw [neg_neg]) hx

/-- An arbitrary hard cavity law has a stretched exponential upper log tail on
the whole nonnegative axis, with a law-dependent prefactor. -/
theorem hard_cavity_log_upperTail {β d : ℝ} (hd : 0 < d) (hβ : 0 < β)
    {μ : Measure ℝ} (h : IsCavityLaw β d μ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ x : ℝ, 0 ≤ x →
      μ (Ioi (Real.exp (β*x))) ≤ ENNReal.ofReal (K * Real.exp (-((x / 2)^d / 2))) := by
  let : IsProbabilityMeasure μ := h.1
  obtain ⟨B, hB, hb⟩ := hard_cavity_log_upperTail_eventually hd hβ h
  let K := Real.exp (B^d / 2)
  have hK : 1 ≤ K := Real.one_le_exp_iff.mpr (by positivity)
  refine ⟨K, hK, fun x hx => ?_⟩
  by_cases hxb : 2*B ≤ x
  · exact (hb x hxb).trans (ENNReal.ofReal_le_ofReal (le_mul_of_one_le_left (Real.exp_nonneg _) hK))
  · have hpow : (x / 2)^d ≤ B^d := Real.rpow_le_rpow (by positivity) (by linarith) hd.le
    have hle : 1 ≤ K * Real.exp (-((x / 2)^d / 2)) := by
      dsimp [K]
      rw [← Real.exp_add]
      exact Real.one_le_exp_iff.mpr (by linarith)
    exact (prob_le_one).trans (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hle)

end Certificate

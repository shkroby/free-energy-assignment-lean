import Certificate.Simplex
import Certificate.Endpoints

/-!
# Concluding the coupled comparison

Given the identity and signed exchange supplied by a marked process, this module
turns them into equality of occupations almost surely. The exchange is an explicit
hypothesis; no point-process theorem is smuggled into the conclusion.
-/

open MeasureTheory ProbabilityTheory

namespace Certificate

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The root term of the comparison cancels because both occupations sum to one. -/
theorem comparison_sum_eq_child {a b Δ : ℕ → ℝ} {D : ℝ}
    (ha : HasSum a 1) (hb : HasSum b 1)
    (hf : ∀ i, simplexTerm a b i = (a i - b i) * (D + Δ i))
    (hΔ : Summable (fun i ↦ (a i - b i) * Δ i)) :
    HasSum (simplexTerm a b) (∑' i, (a i - b i) * Δ i) := by
  have hroot : HasSum (fun i ↦ (a i - b i) * D) 0 := by
    simpa only [sub_self, zero_mul] using (ha.sub hb).mul_right D
  have h := hroot.add hΔ.hasSum
  simp only [zero_add] at h
  refine h.congr_fun ?_
  intro i
  rw [hf, mul_add]

/-- The signed endpoint exchange forces equal occupation vectors. -/
theorem ae_occupations_eq_of_exchange {μ : Measure Ω} {a b Δ : Ω → ℕ → ℝ} {D : Ω → ℝ}
    (hprob : ∀ᵐ ω ∂μ, HasSum (a ω) 1 ∧ HasSum (b ω) 1 ∧
      (∀ i, 0 < a ω i) ∧ (∀ i, 0 < b ω i))
    (hfactor : ∀ᵐ ω ∂μ, ∀ i,
      simplexTerm (a ω) (b ω) i = (a ω i - b ω i) * (D ω + Δ ω i))
    (hchild : ∀ᵐ ω ∂μ, Summable (fun i ↦ (a ω i - b ω i) * Δ ω i))
    (hint : Integrable (fun ω ↦ ∑' i, (a ω i - b ω i) * Δ ω i) μ)
    (hexchange :
      (∫ ω, ∑' i, (a ω i - b ω i) * Δ ω i ∂μ) =
        ∫ ω, (∑' i, (a ω i - b ω i)) * D ω ∂μ) :
    ∀ᵐ ω ∂μ, a ω = b ω := by
  have three : ∀ i j : ℕ, ∃ k, k ≠ i ∧ k ≠ j := by
    intro i j
    exact ⟨i + j + 1, by omega, by omega⟩
  have hsum : ∀ᵐ ω ∂μ,
      HasSum (simplexTerm (a ω) (b ω)) (∑' i, (a ω i - b ω i) * Δ ω i) := by
    filter_upwards [hprob, hfactor, hchild] with ω hp hf hc
    exact comparison_sum_eq_child hp.1 hp.2.1 hf hc
  have hnonneg : 0 ≤ᵐ[μ] (fun ω ↦ ∑' i, (a ω i - b ω i) * Δ ω i) := by
    filter_upwards [hprob, hsum] with ω hp hs
    change 0 ≤ ∑' i, (a ω i - b ω i) * Δ ω i
    rw [← hs.tsum_eq]
    exact simplex_divergence_nonneg three hp.1 hp.2.1 hp.2.2.1 hp.2.2.2 hs.summable
  have hroot_zero : (fun ω ↦ (∑' i, (a ω i - b ω i)) * D ω) =ᵐ[μ] 0 := by
    filter_upwards [hprob] with ω hp
    change (∑' i, (a ω i - b ω i)) * D ω = 0
    rw [(hp.1.sub hp.2.1).tsum_eq, sub_self, zero_mul]
  have hzero : (∫ ω, ∑' i, (a ω i - b ω i) * Δ ω i ∂μ) = 0 := by
    rw [hexchange, integral_congr_ae hroot_zero]
    simp
  have hchild_zero := (integral_eq_zero_iff_of_nonneg_ae hnonneg hint).mp hzero
  filter_upwards [hprob, hsum, hchild_zero] with ω hp hs hz
  by_contra hne
  have hpos := simplex_divergence_pos three hp.1 hp.2.1 hp.2.2.1 hp.2.2.2 hs.summable hne
  rw [hs.tsum_eq] at hpos
  exact hpos.ne' hz

end Certificate

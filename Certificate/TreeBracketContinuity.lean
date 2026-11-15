import Certificate.TreeBoundary
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! Fixed-shape tree brackets are bounded continuous tests of their marks. -/

open Filter MeasureTheory Set
open scoped Topology

namespace Certificate.TreeBoundary

section FiniteSupport

variable {X A : Type*} [TopologicalSpace X]

omit [TopologicalSpace X] in
private theorem summable_weight_of_support {W : X → A → ℕ → ℝ} {support : A → Finset ℕ}
    (hW : ∀ x a i, i ∉ support a → W x a i = 0) (x : X) (a : A) :
    Summable (W x a) := by
  apply summable_of_hasFiniteSupport
  exact (support a).finite_toSet.subset fun i hi => by
    by_contra hin
    exact hi (hW x a i hin)

/-- Continuous nonnegative weights on a fixed, finitely branching shape make
both finite-depth brackets continuous. -/
theorem continuous_bounds_of_finite_support {z : ℝ} (hz : 0 < z)
    (child : A → ℕ → A) (W : X → A → ℕ → ℝ) (support : A → Finset ℕ)
    (hW : ∀ x a i, i ∉ support a → W x a i = 0)
    (h₀ : ∀ x a i, 0 ≤ W x a i) (hC : ∀ a i, Continuous (fun x => W x a i))
    (k : ℕ) (a : A) :
    Continuous (fun x => bounds z child (W x) k a) := by
  have hs := summable_weight_of_support hW
  induction k generalizing a with
  | zero => exact continuous_const
  | succ k ih =>
    let B (i : ℕ) (x : X) := bounds z child (W x) k (child a i)
    have hn (i : ℕ) (x : X) := bounds_mem z child (W x) hz (hs x) (h₀ x) k (child a i)
    have hl (i : ℕ) : Continuous (fun x => (B i x).1) := (ih (child a i)).fst
    have hu (i : ℕ) : Continuous (fun x => (B i x).2) := (ih (child a i)).snd
    have hsum (p : ℝ × ℝ → ℝ) (hp : ∀ i, Continuous (fun x => p (B i x)))
        (hp₀ : ∀ i x, 0 ≤ p (B i x)) :
        Continuous (fun x => update z (W x a) (fun i => p (B i x))) := by
      have heq (x : X) :
          (∑' i, W x a i * p (B i x)) = ∑ i ∈ support a, W x a i * p (B i x) :=
        tsum_eq_sum fun i hi => by rw [hW x a i hi, zero_mul]
      unfold update
      simp_rw [heq]
      refine (continuous_const.add (continuous_finsetSum _ fun i _ => (hC a i).mul (hp i))).inv₀ ?_
      intro x
      exact (add_pos_of_pos_of_nonneg hz (Finset.sum_nonneg fun i _ => mul_nonneg (h₀ x a i) (hp₀ i x))).ne'
    simp only [bounds]
    exact (hsum Prod.snd hu (fun i x => (hn i x).1.trans (hn i x).2.1)).prodMk
      (hsum Prod.fst hl (fun i x => (hn i x).1))

/-- For a fixed finite-depth tree shape, convergence in law of its weight
marks implies convergence of the mean lower and upper messages. -/
theorem tendsto_expected_bounds_of_weak {z : ℝ} (hz : 0 < z)
    (child : A → ℕ → A) (W : X → A → ℕ → ℝ) (support : A → Finset ℕ)
    (hW : ∀ x a i, i ∉ support a → W x a i = 0)
    (h₀ : ∀ x a i, 0 ≤ W x a i) (hC : ∀ a i, Continuous (fun x => W x a i))
    (k : ℕ) (a : A)
    [MeasurableSpace X] [OpensMeasurableSpace X]
    {ι : Type*} {l : Filter ι} {μ : ι → ProbabilityMeasure X} {ν : ProbabilityMeasure X}
    (hμ : Tendsto μ l (𝓝 ν)) :
    Tendsto (fun i => ∫ x, (bounds z child (W x) k a).1 ∂(μ i : Measure X)) l
      (𝓝 (∫ x, (bounds z child (W x) k a).1 ∂(ν : Measure X))) ∧
    Tendsto (fun i => ∫ x, (bounds z child (W x) k a).2 ∂(μ i : Measure X)) l
      (𝓝 (∫ x, (bounds z child (W x) k a).2 ∂(ν : Measure X))) := by
  let B (x : X) := bounds z child (W x) k a
  have h := continuous_bounds_of_finite_support hz child W support hW h₀ hC k a
  have hb (x : X) := bounds_mem z child (W x) hz (summable_weight_of_support hW x) (h₀ x) k a
  have hc {f : X → ℝ} (hf : Continuous f) (h₀ : ∀ x, 0 ≤ f x) (h₁ : ∀ x, f x ≤ z⁻¹) :
      Tendsto (fun i => ∫ x, f x ∂(μ i : Measure X)) l (𝓝 (∫ x, f x ∂(ν : Measure X))) := by
    let g := BoundedContinuousFunction.mkOfBound ⟨f, hf⟩ z⁻¹ (fun x y => by
      change dist (f x) (f y) ≤ z⁻¹
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith [h₀ x, h₀ y, h₁ x, h₁ y])
    exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ g
  exact ⟨hc (f := fun x => (B x).1) h.fst (fun x => (hb x).1)
      (fun x => (hb x).2.1.trans (hb x).2.2),
    hc (f := fun x => (B x).2) h.snd (fun x => (hb x).1.trans (hb x).2.1)
      (fun x => (hb x).2.2)⟩

end FiniteSupport
end Certificate.TreeBoundary

namespace Certificate

/-- Mixtures of bounded nonnegative expectations converge when the shape
probabilities converge pointwise to a probability mass function and the
expectations converge on each shape. -/
theorem tendsto_tsum_of_shape_masses {I : Type*} {p : ℕ → I → ℝ} {q : I → ℝ}
    {a : ℕ → I → ℝ} {b : I → ℝ} {M : ℝ}
    (hp : ∀ n, Summable (p n)) (hq : Summable q)
    (hp₀ : ∀ n i, 0 ≤ p n i) (hq₀ : ∀ i, 0 ≤ q i)
    (hp₁ : ∀ n, ∑' i, p n i = 1) (hq₁ : ∑' i, q i = 1)
    (ha : ∀ n i, a n i ∈ Icc 0 M)
    (hplim : ∀ i, Tendsto (fun n => p n i) atTop (𝓝 (q i)))
    (halim : ∀ i, Tendsto (fun n => a n i) atTop (𝓝 (b i))) :
    Tendsto (fun n => ∑' i, p n i * a n i) atTop (𝓝 (∑' i, q i * b i)) := by
  let m (n : ℕ) (i : I) := min (p n i) (q i)
  let r (n : ℕ) (i : I) := p n i - m n i
  have hm₀ (n : ℕ) (i : I) : 0 ≤ m n i := le_min (hp₀ n i) (hq₀ i)
  have hm₁ (n : ℕ) (i : I) : m n i ≤ q i := min_le_right _ _
  have hm (n : ℕ) : Summable (m n) := Summable.of_nonneg_of_le (hm₀ n) (hm₁ n) hq
  have hmlim (i : I) : Tendsto (fun n => m n i) atTop (𝓝 (q i)) := by
    have hc : Tendsto (fun _ : ℕ => q i) atTop (𝓝 (q i)) := tendsto_const_nhds
    simpa only [m, min_self] using (hplim i).min hc
  have hmass : Tendsto (fun n => ∑' i, m n i) atTop (𝓝 1) := by
    rw [← hq₁]
    exact tendsto_tsum_of_dominated_convergence hq hmlim
      (Eventually.of_forall fun n i => (Real.norm_of_nonneg (hm₀ n i)).trans_le (hm₁ n i))
  have hr₀ (n : ℕ) (i : I) : 0 ≤ r n i := sub_nonneg.mpr (min_le_left _ _)
  have hr (n : ℕ) : Summable (r n) := (hp n).sub (hm n)
  have hrw (n : ℕ) : Summable (fun i => r n i * a n i) :=
    Summable.of_nonneg_of_le (fun i => mul_nonneg (hr₀ n i) (ha n i).1)
      (fun i => mul_le_mul_of_nonneg_left (ha n i).2 (hr₀ n i)) ((hr n).mul_right M)
  have hmw (n : ℕ) : Summable (fun i => m n i * a n i) :=
    Summable.of_nonneg_of_le (fun i => mul_nonneg (hm₀ n i) (ha n i).1)
      (fun i => mul_le_mul_of_nonneg_left (ha n i).2 (hm₀ n i)) ((hm n).mul_right M)
  have hmain : Tendsto (fun n => ∑' i, m n i * a n i) atTop (𝓝 (∑' i, q i * b i)) :=
    tendsto_tsum_of_dominated_convergence (hq.mul_right M) (fun i => (hmlim i).mul (halim i))
      (Eventually.of_forall fun n i =>
        (Real.norm_of_nonneg (mul_nonneg (hm₀ n i) (ha n i).1)).trans_le
          (mul_le_mul (hm₁ n i) (ha n i).2 (ha n i).1 (hq₀ i)))
  have hrest : Tendsto (fun n => ∑' i, r n i * a n i) atTop (𝓝 0) := by
    have hbound : Tendsto (fun n => (1 - ∑' i, m n i) * M) atTop (𝓝 0) := by
      simpa only [sub_self, zero_mul] using (hmass.const_sub 1).mul_const M
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
      (fun n => tsum_nonneg fun i => mul_nonneg (hr₀ n i) (ha n i).1) (fun n => ?_)
    have hu := (hrw n).tsum_le_tsum (fun i => mul_le_mul_of_nonneg_left (ha n i).2 (hr₀ n i))
      ((hr n).mul_right M)
    rw [tsum_mul_right] at hu
    have hrsum : (∑' i, r n i) = 1 - ∑' i, m n i := by
      dsimp only [r]
      rw [(hp n).tsum_sub (hm n), hp₁ n]
    rwa [hrsum] at hu
  refine (by simpa only [add_zero] using hmain.add hrest :
    Tendsto (fun n => (∑' i, m n i * a n i) + (∑' i, r n i * a n i)) atTop _).congr fun n => ?_
  rw [← (hmw n).tsum_add (hrw n)]
  exact tsum_congr fun i => by dsimp only [r]; ring

end Certificate

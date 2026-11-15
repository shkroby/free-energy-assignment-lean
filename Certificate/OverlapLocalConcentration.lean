import Certificate.SoftConcentrationLimit

/-! Bounded row effects give almost-sure concentration of empirical local tests. -/

open Finset Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

namespace Certificate.Overlap

/-- The mean of a local statistic evaluated at the (n) row roots. -/
noncomputable def rowObservableMean (n : ℕ)
    (F : (Fin n → Fin n → ℝ) → Fin n → ℝ) (x : Fin n → Fin n → ℝ) : ℝ :=
  (∑ i, F x i) / (n : ℝ)

private theorem rowObservableMean_mem (n : ℕ)
    {F : (Fin n → Fin n → ℝ) → Fin n → ℝ} (hF : ∀ x i, F x i ∈ Icc (0:ℝ) 1)
    (x : Fin n → Fin n → ℝ) : rowObservableMean n F x ∈ Icc (0:ℝ) 1 := by
  have hsum := Finset.sum_le_sum (f := fun i : Fin n => F x i) (g := fun _ => (1:ℝ))
    (s := Finset.univ) fun i _ => (hF x i).2
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hsum
  exact ⟨div_nonneg (sum_nonneg fun i _ => (hF x i).1) (Nat.cast_nonneg _),
    div_le_one_of_le₀ hsum (Nat.cast_nonneg _)⟩

/-- If changing one input row can alter only a fixed number of bounded
observables, the mean of the observables concentrates almost surely. -/
theorem ae_tendsto_centered_rowObservableMean
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (F : ∀ n : ℕ, (Fin n → Fin n → ℝ) → Fin n → ℝ)
    (hMeas : ∀ n i, Measurable (fun x => F n x i))
    (hB : ∀ n x i, F n x i ∈ Icc (0:ℝ) 1)
    {K : ℕ} (hK : 0 < K)
    (hchange : ∀ n (x y : Fin n → Fin n → ℝ) (r : Fin n), (∀ i ≠ r, x i = y i) →
      (Finset.univ.filter (fun i => F n x i ≠ F n y i)).card ≤ K) :
    ∀ᵐ C ∂iidCosts μ,
      Tendsto (fun n => rowObservableMean n (F n) (costRows n C) -
        ∫ C', rowObservableMean n (F n) (costRows n C') ∂iidCosts μ) atTop (𝓝 0) := by
  let : IsProbabilityMeasure (iidCosts μ) := by unfold iidCosts; infer_instance
  let f (n : ℕ) := rowObservableMean n (F n)
  let g (n : ℕ) (C : CostArray) := f n (costRows n C)
  let c (n : ℕ) : ℝ≥0 := (K : ℝ≥0) / n
  let v (n : ℕ) : ℝ≥0 := (n : ℝ≥0) * (c n)^2
  have hF (n : ℕ) : Measurable (f n) :=
    (Finset.measurable_fun_sum _ (fun i _ => hMeas n i)).div_const _
  have hg (n : ℕ) : HasSubgaussianMGF (fun C => g n C - ∫ C', g n C' ∂iidCosts μ)
      (v n) (iidCosts μ) := by
    let Q := Measure.pi (fun _ : Fin n => μ)
    let : IsProbabilityMeasure Q := by unfold Q; infer_instance
    apply centered_mgf_pullback (measurePreserving_costRows μ n) (hF n) (EventuallyEq.rfl)
    apply hasSubgaussianMGF_of_bounded_differences Q n (a := 0) (b := 1) _ (hF n)
    · exact rowObservableMean_mem n (hB n)
    · intro x y r he
      let S := Finset.univ.filter (fun i => F n x i ≠ F n y i)
      have hs : S.card ≤ K := hchange n x y r he
      have hsum : |∑ i : Fin n, (F n x i - F n y i)| ≤ (K : ℝ) := by
        calc
          _ ≤ ∑ i : Fin n, |F n x i - F n y i| := Finset.abs_sum_le_sum_abs _ _
          _ = ∑ i ∈ S, |F n x i - F n y i| := by
            symm
            apply Finset.sum_subset (Finset.subset_univ _)
            intro i _ hi
            have h : F n x i = F n y i := by simpa [S] using hi
            simp [h]
          _ ≤ ∑ _i ∈ S, (1:ℝ) := sum_le_sum fun i _ => by
            rw [abs_le]
            have hx := hB n x i
            have hy := hB n y i
            exact ⟨by linarith [hx.1, hy.2], by linarith [hx.2, hy.1]⟩
          _ ≤ _ := by simpa [nsmul_eq_mul] using (show (S.card : ℝ) ≤ K from Nat.cast_le.mpr hs)
      change |(∑ i, F n x i) / (n : ℝ) - (∑ i, F n y i) / (n : ℝ)| ≤ (K : ℝ) / (n : ℝ)
      rw [← sub_div, abs_div, abs_of_nonneg (show 0 ≤ (n:ℝ) from Nat.cast_nonneg n), ← Finset.sum_sub_distrib]
      exact div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)
  have hv : ∀ᶠ n in atTop, 0 < v n ∧ (v n : ℝ) ≤ ((K : ℝ)^2) / (n : ℝ) ^ (1/2 : ℝ) := by
    filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
    have hn₀ : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    have hKn : 0 < (K : ℝ) := Nat.cast_pos.mpr hK
    have hc : 0 < c n := by exact_mod_cast (div_pos hKn hn₀)
    refine ⟨mul_pos (Nat.cast_pos.mpr hn) (pow_pos hc _), ?_⟩
    have hval : (v n : ℝ) = (K:ℝ)^2 / n := by
      change (n:ℝ) * ((K:ℝ) / n)^2 = _
      field_simp
    have hhalf : (n:ℝ) ^ (1/2 : ℝ) ≤ n := by
      conv_rhs => rw [← Real.rpow_one (n : ℝ)]
      exact Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hn) (by norm_num)
    rw [hval]
    exact div_le_div_of_nonneg_left (sq_nonneg _) (Real.rpow_pos_of_pos hn₀ _) hhalf
  exact ae_tendsto_zero_of_subgaussian_stretched_decay (iidCosts μ) hg
    (pow_pos (Nat.cast_pos.mpr hK) _) hv

/-- Uniformity over a variable pinned root is enough for convergence of
the mean over all roots. -/
theorem tendsto_rowMean_of_variable_roots
    (f : ∀ n : ℕ, Fin n → ℝ) {a : ℝ}
    (hf : ∀ roots : ∀ n : ℕ, Fin (n+1),
      Tendsto (fun n => f (n+1) (roots n)) atTop (𝓝 a)) :
    Tendsto (fun n => (∑ i : Fin n, f n i) / (n:ℝ)) atTop (𝓝 a) := by
  classical
  choose lo hlo using fun n : ℕ => exists_min_image (Finset.univ : Finset (Fin (n+1)))
    (f (n+1)) ⟨0,Finset.mem_univ _⟩
  choose hi hhi using fun n : ℕ => exists_max_image (Finset.univ : Finset (Fin (n+1)))
    (f (n+1)) ⟨0,Finset.mem_univ _⟩
  apply (tendsto_add_atTop_iff_nat 1).mp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le (hf lo) (hf hi) ?_ ?_
  · intro n
    have hn : 0 < ((n+1 : ℕ):ℝ) := Nat.cast_pos.mpr (Nat.succ_pos n)
    apply (le_div_iff₀ hn).mpr
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i hi => (hlo n).2 i hi)
    simpa [nsmul_eq_mul,mul_comm] using h
  · intro n
    have hn : 0 < ((n+1 : ℕ):ℝ) := Nat.cast_pos.mpr (Nat.succ_pos n)
    apply (div_le_iff₀ hn).mpr
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i hi => (hhi n).2 i hi)
    simpa [nsmul_eq_mul,mul_comm] using h

/-- When the expected pinned-root statistic converges, the same convergence
holds almost surely for its mean across the sampled assignment graph. -/
theorem ae_tendsto_rowObservableMean_of_expected_roots
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (F : ∀ n : ℕ, (Fin n → Fin n → ℝ) → Fin n → ℝ)
    (hMeas : ∀ n i, Measurable (fun x => F n x i))
    (hB : ∀ n x i, F n x i ∈ Icc (0:ℝ) 1)
    {K : ℕ} (hK : 0 < K)
    (hchange : ∀ n (x y : Fin n → Fin n → ℝ) (r : Fin n), (∀ i ≠ r, x i = y i) →
      (Finset.univ.filter (fun i => F n x i ≠ F n y i)).card ≤ K)
    {a : ℝ}
    (hlim : ∀ roots : ∀ n : ℕ, Fin (n+1),
      Tendsto (fun n => ∫ C, F (n+1) (costRows (n+1) C) (roots n) ∂iidCosts μ) atTop (𝓝 a)) :
    ∀ᵐ C ∂iidCosts μ, Tendsto (fun n => rowObservableMean n (F n) (costRows n C)) atTop (𝓝 a) := by
  let : IsProbabilityMeasure (iidCosts μ) := by unfold iidCosts; infer_instance
  have hI (n : ℕ) (i : Fin n) : Integrable (fun C => F n (costRows n C) i) (iidCosts μ) :=
    Integrable.of_bound (((hMeas n i).comp (measurePreserving_costRows μ n).measurable).aestronglyMeasurable) 1
      (Eventually.of_forall fun C => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hB n _ i).1]
        exact (hB n _ i).2)
  have hmean (n : ℕ) : (∫ C, rowObservableMean n (F n) (costRows n C) ∂iidCosts μ) =
      (∑ i : Fin n, ∫ C, F n (costRows n C) i ∂iidCosts μ) / (n:ℝ) := by
    simp only [rowObservableMean, integral_div, integral_finset_sum _ (fun i _ => hI n i)]
  have hb := tendsto_rowMean_of_variable_roots
    (fun n i => ∫ C, F n (costRows n C) i ∂iidCosts μ) hlim
  simp_rw [← hmean] at hb
  filter_upwards [ae_tendsto_centered_rowObservableMean F hMeas hB hK hchange] with C hC
  simpa only [sub_add_cancel,zero_add] using hC.add hb

end Certificate.Overlap

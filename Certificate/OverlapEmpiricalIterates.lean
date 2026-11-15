import Certificate.OverlapTrimGeometry
import Certificate.OverlapRowTests

/-! Root tests of finite BP iterates on the trimmed graph concentrate
around their expected marked shape limits. -/

open Filter Finset MeasureTheory Set
open scoped Topology

namespace Certificate.Overlap

open OverlapBelief

/-- The normalized empirical mean of a test of the row's incident occupations. -/
noncomputable def trimmedIterateRowTest (β d κ R u : ℝ) (n D k : ℕ)
    (P : Finset (Fin n × Fin n) → (Fin n × Fin n → ℝ) → ℝ)
    (C : CostArray) (i : Fin n) : ℝ :=
  let G := trimmedAssignmentGraph β d κ R n D C
  P (incidentEdges G (Sum.inl i)) (incidentOccupationIterate G u k (Sum.inl i))

theorem squareRowTest_congr {E : Type*} {s : Finset E} {f g : E → ℝ}
    (h : EqOn f g s) : squareRowTest s f = squareRowTest s g := by
  unfold squareRowTest
  congr 1
  exact Finset.sum_congr rfl (fun e he => congrArg (fun a : ℝ => a^2) (h he))

theorem thirdOccupation_congr {E : Type*} [DecidableEq E] {s : Finset E} {f g : E → ℝ}
    (h : EqOn f g s) : thirdOccupation s f = thirdOccupation s g := by
  have he := abs_thirdOccupation_sub_le (s := s) (a := f) (b := g) (ε := 0) le_rfl
    (fun e he => by rw [h he,sub_self,abs_zero])
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm he (abs_nonneg _)))

set_option maxHeartbeats 800000 in
/-- A bounded test of the retained incident occupations converges almost
surely after averaging across rows if its pinned-root expectations converge. -/
theorem ae_tendsto_trimmedIterateRowTest_mean_of_expected
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {β d κ R u : ℝ} (hu : 0 < u) (D k : ℕ)
    (P : ∀ n : ℕ, Finset (Fin n × Fin n) → (Fin n × Fin n → ℝ) → ℝ)
    (hB : ∀ n s a, P n s a ∈ Icc (0:ℝ) 1)
    (hLocal : ∀ n {s : Finset (Fin n × Fin n)} {a b}, EqOn a b s → P n s a = P n s b)
    (hM : ∀ n i, Measurable (fun C => trimmedIterateRowTest β d κ R u n D k (P n) C i))
    {L : ℝ} (hLimit : ∀ roots : ∀ n : ℕ, Fin (n+1), Tendsto
      (fun n => ∫ C, trimmedIterateRowTest β d κ R u (n+1) D k (P (n+1)) C (roots n) ∂iidCosts μ)
      atTop (𝓝 L)) :
    ∀ᵐ C ∂iidCosts μ, Tendsto (fun n => (∑ i, trimmedIterateRowTest β d κ R u n D k (P n) C i) /
        (n : ℝ)) atTop (𝓝 L) := by
  classical
  let F (n : ℕ) (x : Fin n → Fin n → ℝ) (i : Fin n) :=
    let G := trimmedGraphOfRows β d κ R n D x
    P n (incidentEdges G (Sum.inl i)) (incidentOccupationIterate G u k (Sum.inl i))
  have hF' (n : ℕ) (x : Fin n → Fin n → ℝ) (i : Fin n) :
      F n x i = trimmedIterateRowTest β d κ R u n D k (P n) (extendCostRows n x) i := by
    have he : trimmedAssignmentGraph β d κ R n D (extendCostRows n x) =
        trimmedGraphOfRows β d κ R n D x := by
      rw [← trimmedGraphOfRows_costRows, costRows_extendCostRows]
    simp only [F, trimmedIterateRowTest, he]
  have hF (n : ℕ) (C : CostArray) (i : Fin n) :
      F n (costRows n C) i = trimmedIterateRowTest β d κ R u n D k (P n) C i := rfl
  let K := 2 * (4*D^2 + 2*D) * (1+2*(2*D))^(k+1) + 1
  have hchange (n : ℕ) (x y : Fin n → Fin n → ℝ) (r : Fin n)
      (hr : ∀ i ≠ r, x i = y i) :
      (Finset.univ.filter (fun i => F n x i ≠ F n y i)).card ≤ K := by
    let G := trimmedGraphOfRows β d κ R n D x
    let H := trimmedGraphOfRows β d κ R n D y
    obtain ⟨bad,hagree,hcard⟩ :=
      exists_trimmedGraphOfRows_affectedVertices (β := β) (d := d) (κ := κ) (R := R)
        D (k+1) x y r hr
    let A := affectedVertices G.ends (G.edges ∪ H.edges) bad (k+1)
    let I := Finset.univ.filter (fun i => F n x i ≠ F n y i)
    have hsub : I.image (Sum.inl : Fin n → Fin n ⊕ Fin n) ⊆ A := by
      intro v hv
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hv
      have hn : F n x i ≠ F n y i := (mem_filter.mp hi).2
      by_contra hnot
      have heq := incidentOccupationIterate_agree_of_notMem_affectedVertices
        (G := G) (H := H) rfl bad hagree hu k (Sum.inl i) hnot
      apply hn
      change
        P n (incidentEdges G (Sum.inl i)) (incidentOccupationIterate G u k (Sum.inl i)) =
          P n (incidentEdges H (Sum.inl i)) (incidentOccupationIterate H u k (Sum.inl i))
      rw [← heq.1]
      exact hLocal n heq.2
    change I.card ≤ K
    rw [← Finset.card_image_of_injective I (Sum.inl_injective : Function.Injective
      (Sum.inl : Fin n → Fin n ⊕ Fin n))]
    exact (Finset.card_le_card hsub).trans (hcard.trans (Nat.le_succ _))
  have hm (n : ℕ) (i : Fin n) : Measurable (fun x => F n x i) := by
    simp_rw [hF']
    exact (hM n i).comp (measurable_extendCostRows n)
  have hlim : ∀ roots : ∀ n : ℕ, Fin (n+1), Tendsto
      (fun n => ∫ C, F (n+1) (costRows (n+1) C) (roots n) ∂iidCosts μ) atTop (𝓝 L) := by
    intro roots
    simpa only [hF] using hLimit roots
  have h := ae_tendsto_rowObservableMean_of_expected_roots F hm
    (fun n x i => hB n _ _) (Nat.zero_lt_succ _) hchange hlim
  simpa only [rowObservableMean,hF] using h

end Certificate.Overlap

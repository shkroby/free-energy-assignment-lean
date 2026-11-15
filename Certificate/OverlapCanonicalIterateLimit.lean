import Certificate.OverlapCanonicalIterates
import Certificate.OverlapCanonicalSupport
import Certificate.OverlapTreeBoundaryContraction

/-! Fixed-degree convergence of the canonical finite-depth occupations. -/

open Filter Finset MeasureTheory Set
open scoped Topology

namespace Certificate.CanonicalTree

private theorem ae_trimmedWeight_finite_bound {β d R : ℝ}
    (hβ : 0 ≤ β) (hd : 0 < d) (hR : 0 ≤ R) (D : ℕ) :
    ∀ᵐ ω ∂law, ∀ v, ∃ s : Finset ℕ,
      (∀ i ∉ s, trimmedWeight β d R D ω v i = 0) ∧
      (∑ i ∈ s, trimmedWeight β d R D ω v i) ≤ (D : ℝ) := by
  classical
  let : IsProbabilityMeasure exponentialSpacings := isProbabilityMeasure_exponentialSpacings
  have hSp : ∀ᵐ ω ∂law, ∀ v i, 0 < ω v i := by
    apply ae_all_iff.mpr
    intro v
    have hm := measurePreserving_eval_infinitePi (fun _ : Vertex => exponentialSpacings) v
    exact hm.quasiMeasurePreserving.ae ae_expSpacing_pos
  filter_upwards [ae_cutoffKernel_eq_zero_off_range hd hR β, hSp] with ω hω hPos
  intro v
  let W := trimmedWeight β d R D ω
  let s := (Finset.range (cutoffOffspringNat d R (ω v))).filter fun i => W v i ≠ 0
  have hOff (i : ℕ) (hi : i ∉ s) : W v i = 0 := by
    by_contra h
    by_cases hic : i < cutoffOffspringNat d R (ω v)
    · exact hi (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hic,h⟩)
    · have hw := (trimmedWeight_bounds β d R D ω v i).2
      rw [hω v i (fun hi => hic (Finset.mem_range.mp hi))] at hw
      exact h (le_antisymm hw (trimmedWeight_bounds β d R D ω v i).1)
  refine ⟨s,hOff,?_⟩
  have hW₁ (i : ℕ) : W v i ≤ 1 := by
    refine (trimmedWeight_bounds β d R D ω v i).2.trans ?_
    change cutoffKernel β R (arrivalLength d (ω v) i) ≤ 1
    unfold cutoffKernel
    split_ifs
    · have hlen : 0 < arrivalLength d (ω v) i := by
        unfold arrivalLength
        exact Real.rpow_pos_of_pos
          (Finset.sum_pos (fun j _ => hPos v j) Finset.nonempty_range_add_one) _
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hβ) hlen.le)
    · norm_num
  have hCard : s.card ≤ D := by
    by_cases hv : v.length % 2 = 0
    · by_cases hdv : cutoffDegree d R ω v ≤ D
      · calc
          s.card ≤ (Finset.range (cutoffOffspringNat d R (ω v))).card :=
            Finset.card_le_card (Finset.filter_subset _ _)
          _ ≤ D := by
            rw [Finset.card_range]
            exact (Nat.le_add_right _ _).trans hdv
      · have hs : s = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro i hi
          exact ((Finset.mem_filter.mp hi).2)
            (by simp [W, trimmedWeight, hv, hdv])
        simp [hs]
    · by_cases hdv : cutoffColumnDegree d R D ω v ≤ D
      · have hsub : s ⊆ (Finset.range (cutoffOffspringNat d R (ω v))).filter
            (fun i => cutoffDegree d R ω (child v i) ≤ D) := by
          intro i hi
          obtain ⟨hir,hW⟩ := Finset.mem_filter.mp hi
          refine Finset.mem_filter.mpr ⟨hir,?_⟩
          by_contra hc
          exact hW (by simp [W, trimmedWeight, hv, hc])
        exact (Finset.card_le_card hsub).trans ((Nat.le_add_right _ _).trans hdv)
      · have hs : s = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro i hi
          exact ((Finset.mem_filter.mp hi).2)
            (by simp [W, trimmedWeight, hv, hdv])
        simp [hs]
  calc
    _ ≤ ∑ i ∈ s, (1 : ℝ) := Finset.sum_le_sum fun i _ => hW₁ i
    _ ≤ (D : ℝ) := by simpa using (Nat.cast_le (α := ℝ)).mpr hCard

private theorem tendsto_trimmedRootCavityIterate_of_downward {β d R z : ℝ}
    (hz : 0 < z) (D : ℕ) (ω : Environment) (i : ℕ)
    (H : Vertex → ℝ) (hHpos : ∀ v, 0 < H v)
    (s : Finset ℕ) (hOff : ∀ j ∉ s, trimmedWeight β d R D ω [] j = 0)
    (hH : ∀ v, Tendsto (fun k => trimmedDownwardIterate β d R z D k ω v) atTop (𝓝 (H v))) :
    Tendsto (fun k => trimmedRootCavityIterate β d R z D ω k i) atTop
      (𝓝 (TreeBoundary.update z
        (fun j => if j = i then 0 else trimmedWeight β d R D ω [] j)
        (fun j => H (child [] j)))) := by
  let w (j : ℕ) := if j = i then 0 else trimmedWeight β d R D ω [] j
  have hzW (j : ℕ) : 0 ≤ w j := by
    dsimp only [w]
    split_ifs
    · exact le_rfl
    · exact (trimmedWeight_bounds β d R D ω [] j).1
  have hof (T : ℕ → ℝ) :
      (∑' j, w j * T j) = ∑ j ∈ s, w j * T j := by
    apply tsum_eq_sum
    intro j hj
    simp [w, hOff j hj]
  apply (tendsto_add_atTop_iff_nat 1).mp
  simp only [trimmedRootCavityIterate, TreeBoundary.update]
  change Tendsto (fun k => (z + ∑' j, w j * trimmedDownwardIterate β d R z D k ω
    (child [] j))⁻¹) atTop (𝓝 (z + ∑' j, w j * H (child [] j))⁻¹)
  simp_rw [hof]
  have hS : Tendsto (fun k => ∑ j ∈ s, w j * trimmedDownwardIterate β d R z D k ω
      (child [] j)) atTop (𝓝 (∑ j ∈ s, w j * H (child [] j))) :=
    tendsto_finsetSum s fun j _ => (hH (child [] j)).const_mul (w j)
  exact (hS.const_add z).inv₀ (add_pos_of_pos_of_nonneg hz
    (Finset.sum_nonneg fun j _ => mul_nonneg (hzW j) (hHpos _).le)).ne'

set_option maxHeartbeats 1200000 in
/-- At a fixed degree and length cutoff the canonical finite-depth BP
occupations converge to the occupations used in cutoff removal. -/
theorem ae_tendsto_trimmedRootOccupationIterate
    {β d R z : ℝ} (hβ : 0 ≤ β) (hd : 0 < d) (hR : 0 ≤ R) (hz : 0 < z) (D : ℕ) :
    ∀ᵐ ω ∂law, ∀ i, Tendsto (fun k => trimmedRootOccupationIterate β d R z D k ω i)
      atTop (𝓝 (trimmedRootOccupation β d R z D ω i)) := by
  classical
  filter_upwards [ae_trimmedWeight_finite_bound hβ hd hR D] with ω hω
  let W := trimmedWeight β d R D ω
  choose s hOff hMass using hω
  have hw (v : Vertex) (i : ℕ) : 0 ≤ W v i := (trimmedWeight_bounds β d R D ω v i).1
  have hS (v : Vertex) : Summable (W v) := (hasSum_sum_of_ne_finset_zero (hOff v)).summable
  obtain ⟨H,hH⟩ := TreeBoundary.exists_common_boundary_limit_of_bounded_mass child W s hz
    (Nat.cast_nonneg D) hw hOff hMass
  have hL (v : Vertex) : trimmedLower β d R z D v ω = H v := by
    have h := TreeBoundary.bounds_mem z child W hz hS hw
    apply tendsto_nhds_unique _ (hH v).1
    exact tendsto_atTop_ciSup
      (monotone_nat_of_le_succ fun j => (TreeBoundary.bounds_step z child W hz hS hw j v).1)
      ⟨z⁻¹, fun _ ⟨j,hj⟩ => hj ▸ (h j v).2.1.trans (h j v).2.2⟩
  have hU (v : Vertex) : trimmedUpper β d R z D v ω = H v := by
    have h := TreeBoundary.bounds_mem z child W hz hS hw
    apply tendsto_nhds_unique _ (hH v).2.1
    exact tendsto_atTop_ciInf
      (antitone_nat_of_succ_le fun j => (TreeBoundary.bounds_step z child W hz hS hw j v).2)
      ⟨0, fun _ ⟨j,hj⟩ => hj ▸ (h j v).1.trans (h j v).2.1⟩
  have hD (v : Vertex) :
      Tendsto (fun k => trimmedDownwardIterate β d R z D k ω v) atTop (𝓝 (H v)) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le (hH v).1 (hH v).2.1
    · intro n
      exact (TreeBoundary.fromBoundary_between z child W hz hS hw (fun _ => z⁻¹)
        (fun _ => ⟨inv_nonneg.mpr hz.le,le_rfl⟩) n v).1
    · intro n
      exact (TreeBoundary.fromBoundary_between z child W hz hS hw (fun _ => z⁻¹)
        (fun _ => ⟨inv_nonneg.mpr hz.le,le_rfl⟩) n v).2
  intro i
  let w (j : ℕ) := if j = i then 0 else W [] j
  let B := ∑' j, w j * H (child [] j)
  let a := (z + B)⁻¹
  have hB₀ : 0 ≤ B := by
    apply tsum_nonneg
    intro j
    apply mul_nonneg _ (hH _).2.2.1.le
    unfold w
    split_ifs
    · exact le_rfl
    · exact hw [] j
  have hZ : 0 < z + B := add_pos_of_pos_of_nonneg hz hB₀
  have hc := tendsto_trimmedRootCavityIterate_of_downward hz D ω i H
    (fun v => (hH v).2.2.1) (s []) (hOff []) hD
  have hp : Tendsto (fun k => W [] i * trimmedRootCavityIterate β d R z D ω k i *
      trimmedDownwardIterate β d R z D k ω (child [] i)) atTop
      (𝓝 (W [] i * a * H (child [] i))) := (hc.const_mul _).mul (hD _)
  have hprod : 0 ≤ W [] i * a * H (child [] i) :=
    mul_nonneg (mul_nonneg (hw [] i) (inv_nonneg.mpr hZ.le)) (hH _).2.2.1.le
  have ht := hp.div (hp.const_add 1) (add_pos_of_pos_of_nonneg zero_lt_one hprod).ne'
  have hSumm : Summable (fun j => W [] j * H (child [] j)) :=
    (hasSum_sum_of_ne_finset_zero (s := s []) (fun j hj => by
      have hj' : W [] j = 0 := hOff [] j hj
      rw [hj', zero_mul])).summable
  have hsplit : (∑' j, W [] j * H (child [] j)) = W [] i * H (child [] i) + B := by
    rw [hSumm.tsum_eq_add_tsum_ite i]
    congr 1
    apply tsum_congr
    intro j
    by_cases hj : j = i <;> simp [w,hj]
  have hRec : H [] = (z + (W [] i * H (child [] i) + B))⁻¹ := by
    have h := (hH []).2.2.2.2
    unfold TreeBoundary.update at h
    rwa [hsplit] at h
  have heq : W [] i * a * H (child [] i) / (1 + W [] i * a * H (child [] i)) =
      trimmedRootOccupation β d R z D ω i := by
    unfold trimmedRootOccupation
    rw [hU [], hL (child [] i), hRec]
    change W [] i * (z+B)⁻¹ * H (child [] i) / (1+W [] i * (z+B)⁻¹ * H (child [] i)) =
      W [] i * (z+(W [] i * H (child [] i)+B))⁻¹ * H (child [] i)
    let X := W [] i * H (child [] i)
    let Y := z+B
    have hy : 0 < Y := hZ
    have hxy : 0 < Y+X := add_pos_of_pos_of_nonneg hy
      (mul_nonneg (hw [] i) (hH _).2.2.1.le)
    have hleft : W [] i * (z+B)⁻¹ * H (child [] i) = X/Y := by
      dsimp only [X,Y]
      rw [div_eq_mul_inv]
      ring
    have hright :
        W [] i * (z+(W [] i * H (child [] i)+B))⁻¹ * H (child [] i) = X/(Y+X) := by
      rw [show z+(W [] i * H (child [] i)+B) = Y+X by dsimp only [Y,X]; ring]
      rw [div_eq_mul_inv]
      dsimp only [X]
      ring
    rw [hleft, hright, show 1+X/Y = (Y+X)/Y by field_simp [hy.ne']]
    field_simp [hy.ne', hxy.ne']
  rw [← heq]
  exact ht

end Certificate.CanonicalTree

import Certificate.OverlapRowTests

/-! A countable threshold representation of the third-largest occupation. -/

open Finset Set

namespace Certificate.Overlap

variable {I : Type*} [DecidableEq I]

/-- Count thresholds only in the range of a probability. -/
noncomputable def rationalThird (s : Finset I) (a : I → ℝ) : ℝ :=
  ⨆ q : ℚ, if 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ 1 ∧ 3 ≤ (s.filter (fun i => (q : ℝ) ≤ a i)).card
    then (q : ℝ) else 0

omit [DecidableEq I] in
theorem three_le_card_filter_iff (s : Finset I) (a : I → ℝ) (q : ℝ) :
    3 ≤ (s.filter (fun i => q ≤ a i)).card ↔ ThreeLargeOn s a q := by
  change 2 < (s.filter (fun i => q ≤ a i)).card ↔ _
  rw [Finset.two_lt_card]
  constructor
  · rintro ⟨i,hi,j,hj,k,hk,hij,hik,hjk⟩
    exact ⟨i,(mem_filter.mp hi).1,j,(mem_filter.mp hj).1,k,(mem_filter.mp hk).1,
      hij,hik,hjk,(mem_filter.mp hi).2,(mem_filter.mp hj).2,(mem_filter.mp hk).2⟩
  · rintro ⟨i,hi,j,hj,k,hk,hij,hik,hjk,hqi,hqj,hqk⟩
    exact ⟨i,mem_filter.mpr ⟨hi,hqi⟩,j,mem_filter.mpr ⟨hj,hqj⟩,k,
      mem_filter.mpr ⟨hk,hqk⟩,hij,hik,hjk⟩

theorem rationalThird_eq_thirdOccupation (s : Finset I) (a : I → ℝ)
    (ha : ∀ i ∈ s, a i ≤ 1) : rationalThird s a = thirdOccupation s a := by
  let b := thirdOccupation s a
  let F (q : ℚ) : ℝ :=
    if 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ 1 ∧ 3 ≤ (s.filter (fun i => (q : ℝ) ≤ a i)).card
    then (q : ℝ) else 0
  have hF (q : ℚ) : F q ∈ Set.Icc 0 1 := by
    unfold F
    split_ifs with h
    · exact ⟨h.1,h.2.1⟩
    · exact ⟨le_rfl,zero_le_one⟩
  have hB : BddAbove (Set.range F) := by
    refine ⟨1, ?_⟩
    rintro y ⟨q,hq⟩
    rw [← hq]
    exact (hF q).2
  have h0 : 0 ≤ b := NNReal.coe_nonneg _
  have h1 : b ≤ 1 := by
    by_contra! h
    have ht := (threeLargeOn_iff_le_thirdOccupation (s := s) (a := a)
      (zero_lt_one.trans h)).mpr (show b ≤ b from le_rfl)
    obtain ⟨i,his,_,_,_,_,_,_,_,hi,_,_⟩ := ht
    exact (not_lt_of_ge (ha i his)) (h.trans_le hi)
  change (⨆ q, F q) = b
  refine le_antisymm ?_ ?_
  · apply ciSup_le
    intro q
    by_cases hq : 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ 1 ∧ 3 ≤ (s.filter (fun i => (q : ℝ) ≤ a i)).card
    · rw [show F q = (q : ℝ) from if_pos hq]
      by_cases hpos : 0 < (q : ℝ)
      · exact (threeLargeOn_iff_le_thirdOccupation hpos).mp ((three_le_card_filter_iff s a q).mp hq.2.2)
      · exact (le_of_not_gt hpos).trans h0
    · rw [show F q = 0 from if_neg hq]
      exact h0
  · by_contra! h
    obtain ⟨q,hq₁,hq₂⟩ := exists_rat_btwn h
    have hsup0 : 0 ≤ ⨆ q, F q := (hF (0:ℚ)).1.trans (le_ciSup hB (0:ℚ))
    have hq0 : 0 < (q : ℝ) := hsup0.trans_lt hq₁
    have hq1 : (q : ℝ) ≤ 1 := hq₂.le.trans h1
    have hlarge := (threeLargeOn_iff_le_thirdOccupation (s := s) (a := a) hq0).mpr hq₂.le
    have hc := (three_le_card_filter_iff s a q).mpr hlarge
    exact (not_lt_of_ge ((show F q = (q : ℝ) from if_pos ⟨hq0.le,hq1,hc⟩).symm.trans_le
      (le_ciSup hB q))) hq₁

end Certificate.Overlap

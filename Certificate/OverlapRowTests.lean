import Certificate.OverlapSimplexCurvature
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Algebra.Order.Group.MinMax

/-! Continuous row statistics for the empirical occupation tests. -/

open Finset Set
open scoped NNReal

namespace Certificate.Overlap

variable {E A : Type*} [DecidableEq E]

/-- A bounded form of the row occupation square sum. -/
noncomputable def squareRowTest (s : Finset E) (a : E → ℝ) : ℝ :=
  min 1 (∑ e ∈ s, (a e)^2)

theorem squareRowTest_mem (s : Finset E) (a : E → ℝ) :
    squareRowTest s a ∈ Icc (0:ℝ) 1 :=
  ⟨le_min zero_le_one (sum_nonneg fun e _ => sq_nonneg (a e)), min_le_left _ _⟩

theorem squareRowTest_eq_of_subprobability (s : Finset E) (a : E → ℝ)
    (h₀ : ∀ e ∈ s, 0 ≤ a e) (h₁ : (∑ e ∈ s, a e) ≤ 1) :
    squareRowTest s a = ∑ e ∈ s, (a e)^2 := by
  apply min_eq_right
  refine (sum_le_sum fun e he => ?_).trans h₁
  have he₁ : a e ≤ 1 := (single_le_sum (fun j hj => h₀ j hj) he).trans h₁
  nlinarith [mul_nonneg (h₀ e he) (sub_nonneg.mpr he₁)]

theorem continuous_squareRowTest {X : Type*} [TopologicalSpace X]
    (s : Finset E) (a : X → E → ℝ) (ha : ∀ e ∈ s, Continuous (fun x => a x e)) :
    Continuous (fun x => squareRowTest s (a x)) :=
  continuous_const.min (continuous_finset_sum _ fun e he => (ha e he).pow 2)

theorem abs_squareRowTest_sub_le {s : Finset E} {a b : E → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (ha : ∀ e ∈ s, a e ∈ Icc (0:ℝ) 1) (hb : ∀ e ∈ s, b e ∈ Icc (0:ℝ) 1)
    (he : ∀ e ∈ s, |a e - b e| ≤ ε) :
    |squareRowTest s a - squareRowTest s b| ≤ 2 * (s.card : ℝ) * ε := by
  unfold squareRowTest
  refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le (by simp; positivity) ?_)
  rw [← sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ _e ∈ s, 2*ε := sum_le_sum fun e hes => by
      rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg (ha e hes).1 (hb e hes).1)]
      have h := add_le_add (ha e hes).2 (hb e hes).2
      have hn := add_nonneg (ha e hes).1 (hb e hes).1
      calc
        _ ≤ (a e + b e) * ε := mul_le_mul_of_nonneg_left (he e hes) hn
        _ ≤ (1+1) * ε := mul_le_mul_of_nonneg_right h hε
        _ = _ := by ring
    _ = _ := by simp only [sum_const,nsmul_eq_mul]; ring

private def distinctTriples (s : Finset E) : Finset (E × E × E) :=
  (s.product (s.product s)).filter fun p => p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2 ∧ p.2.1 ≠ p.2.2

private theorem mem_distinctTriples_iff {s : Finset E} {p : E × E × E} :
    p ∈ distinctTriples s ↔ p.1 ∈ s ∧ p.2.1 ∈ s ∧ p.2.2 ∈ s ∧
      p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2 ∧ p.2.1 ≠ p.2.2 := by
  rcases p with ⟨i,j,k⟩
  simp only [distinctTriples,mem_filter]
  constructor
  · rintro ⟨hp, hn⟩
    obtain ⟨hi,hjk⟩ := Finset.mem_product.mp hp
    obtain ⟨hj,hk⟩ := Finset.mem_product.mp hjk
    exact ⟨hi,hj,hk,hn⟩
  · rintro ⟨hi,hj,hk,hn⟩
    exact ⟨Finset.mk_mem_product hi (Finset.mk_mem_product hj hk),hn⟩

private noncomputable def tripleValue (a : E → ℝ) (p : E × E × E) : ℝ≥0 :=
  (min (a p.1) (min (a p.2.1) (a p.2.2))).toNNReal

/-- The third largest nonnegative occupation, with value zero if there
are fewer than three coordinates. -/
noncomputable def thirdOccupation (s : Finset E) (a : E → ℝ) : ℝ :=
  ((distinctTriples s).sup (tripleValue a) : ℝ≥0)

theorem threeLargeOn_iff_le_thirdOccupation {s : Finset E} {a : E → ℝ} {η : ℝ}
    (hη : 0 < η) : ThreeLargeOn s a η ↔ η ≤ thirdOccupation s a := by
  have hη' : 0 < η.toNNReal := Real.toNNReal_pos.mpr hη
  have hcut (x : ℝ≥0) : η ≤ (x:ℝ) ↔ η.toNNReal ≤ x := Real.toNNReal_le_iff_le_coe.symm
  unfold thirdOccupation
  rw [hcut, Finset.le_sup_iff hη']
  constructor
  · rintro ⟨i, hi, j, hj, k, hk, hij, hik, hjk, hηi, hηj, hηk⟩
    refine ⟨(i,j,k), mem_distinctTriples_iff.mpr ⟨hi,hj,hk,hij,hik,hjk⟩,?_⟩
    exact Real.toNNReal_mono (le_min hηi (le_min hηj hηk))
  · rintro ⟨⟨i,j,k⟩, he, hle⟩
    obtain ⟨hi,hj,hk,hij,hik,hjk⟩ := mem_distinctTriples_iff.mp he
    have h' : η ≤ min (a i) (min (a j) (a k)) := by
      have hm : η.toNNReal ≤ (min (a i) (min (a j) (a k))).toNNReal := hle
      by_contra hn
      have hlt := (Real.toNNReal_lt_toNNReal_iff hη).mpr (lt_of_not_ge hn)
      exact (not_lt_of_ge hm) hlt
    exact ⟨i,hi,j,hj,k,hk,hij,hik,hjk,(le_min_iff.mp h').1,
      (le_min_iff.mp (le_min_iff.mp h').2).1,(le_min_iff.mp (le_min_iff.mp h').2).2⟩

private theorem coe_sup_nnreal (x y : ℝ≥0) : ((x ⊔ y : ℝ≥0):ℝ) = max (x:ℝ) (y:ℝ) := by
  rcases le_total x y with h | h
  · rw [sup_eq_right.mpr h, max_eq_right (NNReal.coe_le_coe.mpr h)]
  · rw [sup_eq_left.mpr h, max_eq_left (NNReal.coe_le_coe.mpr h)]

private theorem continuous_coe_sup {I X : Type*} [DecidableEq I] [TopologicalSpace X]
    (s : Finset I) (f : X → I → ℝ≥0) (hf : ∀ i ∈ s, Continuous (fun x => (f x i:ℝ))) :
    Continuous (fun x => ((s.sup (f x) : ℝ≥0):ℝ)) := by
  induction s using Finset.induction_on with
  | empty =>
    change Continuous (fun _ : X => (0:ℝ))
    exact continuous_const
  | insert i s hi ih =>
    simpa only [Finset.sup_insert, coe_sup_nnreal] using
      (hf i (mem_insert_self _ _)).max (ih fun j hj => hf j (mem_insert_of_mem hj))

theorem continuous_thirdOccupation {X : Type*} [TopologicalSpace X]
    (s : Finset E) (a : X → E → ℝ) (ha : ∀ e ∈ s, Continuous (fun x => a x e)) :
    Continuous (fun x => thirdOccupation s (a x)) := by
  apply continuous_coe_sup
  intro p hp
  obtain ⟨hi,hj,hk,_,_,_⟩ := mem_distinctTriples_iff.mp hp
  simp only [tripleValue, Real.coe_toNNReal']
  exact ((ha _ hi).min ((ha _ hj).min (ha _ hk))).max continuous_const

private theorem abs_coe_sup_sub_le {I : Type*} [DecidableEq I]
    (s : Finset I) (a b : I → ℝ≥0) {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ i ∈ s, |(a i:ℝ) - (b i:ℝ)| ≤ ε) :
    |((s.sup a : ℝ≥0):ℝ) - ((s.sup b : ℝ≥0):ℝ)| ≤ ε := by
  induction s using Finset.induction_on with
  | empty => simpa
  | insert i s hi ih =>
    simp only [sup_insert,coe_sup_nnreal]
    exact (abs_max_sub_max_le_max _ _ _ _).trans
      (max_le (h _ (mem_insert_self _ _)) (ih fun j hj => h j (mem_insert_of_mem hj)))

theorem abs_thirdOccupation_sub_le {s : Finset E} {a b : E → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ i ∈ s, |a i - b i| ≤ ε) :
    |thirdOccupation s a - thirdOccupation s b| ≤ ε := by
  apply abs_coe_sup_sub_le _ _ _ hε
  intro p hp
  obtain ⟨hi,hj,hk,_,_,_⟩ := mem_distinctTriples_iff.mp hp
  simp only [tripleValue, Real.coe_toNNReal']
  exact (abs_max_sub_max_le_abs _ _ _).trans
    ((abs_min_sub_min_le_max _ _ _ _).trans (max_le (h _ hi)
      ((abs_min_sub_min_le_max _ _ _ _).trans (max_le (h _ hj) (h _ hk)))))

omit [DecidableEq E] in
/-- The squared-occupation statistic is invariant under injective relabelling. -/
theorem squareRowTest_image {J : Type*} [DecidableEq J] (s : Finset E)
    (f : E → J) (hf : Function.Injective f) (a : J → ℝ) :
    squareRowTest (s.image f) a = squareRowTest s (a ∘ f) := by
  unfold squareRowTest
  rw [Finset.sum_image (fun _ _ _ _ h => hf h)]
  rfl

/-- The third largest occupation is invariant under injective relabelling. -/
theorem thirdOccupation_image {J : Type*} [DecidableEq J] (s : Finset E)
    (f : E → J) (hf : Function.Injective f) (a : J → ℝ) :
    thirdOccupation (s.image f) a = thirdOccupation s (a ∘ f) := by
  let mapTriple (p : E × E × E) : J × J × J := (f p.1,f p.2.1,f p.2.2)
  have heq : distinctTriples (s.image f) = (distinctTriples s).image mapTriple := by
    ext p
    constructor
    · intro hp
      obtain ⟨hi,hj,hk,hij,hik,hjk⟩ := mem_distinctTriples_iff.mp hp
      obtain ⟨i, hi, ei⟩ := mem_image.mp hi
      obtain ⟨j, hj, ej⟩ := mem_image.mp hj
      obtain ⟨k, hk, ek⟩ := mem_image.mp hk
      have neq₁ : i ≠ j := fun h => hij (ei.symm.trans ((congrArg f h).trans ej))
      have neq₂ : i ≠ k := fun h => hik (ei.symm.trans ((congrArg f h).trans ek))
      have neq₃ : j ≠ k := fun h => hjk (ej.symm.trans ((congrArg f h).trans ek))
      exact mem_image.mpr ⟨(i,j,k),mem_distinctTriples_iff.mpr ⟨hi,hj,hk,neq₁,neq₂,neq₃⟩,
        Prod.ext ei (Prod.ext ej ek)⟩
    · rintro hp
      obtain ⟨⟨i,j,k⟩,hq,rfl⟩ := mem_image.mp hp
      obtain ⟨hi,hj,hk,hij,hik,hjk⟩ := mem_distinctTriples_iff.mp hq
      exact mem_distinctTriples_iff.mpr
        ⟨mem_image_of_mem _ hi,mem_image_of_mem _ hj,mem_image_of_mem _ hk,
          fun h => hij (hf h),fun h => hik (hf h),fun h => hjk (hf h)⟩
  unfold thirdOccupation
  rw [heq, Finset.sup_image]
  rfl

/-- A continuous majorant of the event that the third occupation is
below eta. It vanishes at and above twice eta. -/
noncomputable def smallOccupationTest (η x : ℝ) : ℝ :=
  max 0 (min 1 (2 - x/η))

theorem smallOccupationTest_mem (η x : ℝ) : smallOccupationTest η x ∈ Icc (0:ℝ) 1 :=
  ⟨le_max_left _ _,max_le zero_le_one (min_le_left _ _)⟩

theorem smallOccupationTest_eq_one {η x : ℝ} (hη : 0 < η) (hx : x ≤ η) :
    smallOccupationTest η x = 1 := by
  have h := (div_le_one hη).mpr hx
  simp [smallOccupationTest, min_eq_left (show 1 ≤ 2-x/η by linarith)]

theorem smallOccupationTest_eq_zero {η x : ℝ} (hη : 0 < η) (hx : 2*η ≤ x) :
    smallOccupationTest η x = 0 := by
  have h := (le_div_iff₀ hη).mpr hx
  simp [smallOccupationTest, max_eq_left ((min_le_right (1:ℝ) (2-x/η)).trans
    (show 2-x/η ≤ 0 by linarith))]

theorem continuous_smallOccupationTest (η : ℝ) : Continuous (smallOccupationTest η) :=
  continuous_const.max (continuous_const.min (continuous_const.sub (continuous_id.div_const η)))

theorem abs_smallOccupationTest_sub_le {η a b ε : ℝ} (hη : 0 < η)
    (h : |a-b| ≤ ε) :
    |smallOccupationTest η a - smallOccupationTest η b| ≤ ε/η := by
  unfold smallOccupationTest
  have hm : |(2-a/η) - (2-b/η)| = |a-b|/η := by
    rw [show (2-a/η)-(2-b/η) = -((a-b)/η) by ring, abs_neg, abs_div, abs_of_pos hη]
  refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le ?_ ?_)
  · simpa using div_nonneg ((abs_nonneg _).trans h) hη.le
  · refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le ?_ ?_)
    · simpa using div_nonneg ((abs_nonneg _).trans h) hη.le
    · rw [hm]
      exact div_le_div_of_nonneg_right h hη.le

end Certificate.Overlap

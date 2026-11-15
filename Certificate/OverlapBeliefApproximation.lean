import Certificate.OverlapBeliefLocal
import Certificate.OverlapBeliefPressure

/-! A deterministic finite-size Bethe pressure error bound uniform in the
weights. The bound depends only on total incident weight and the number of
roots with compatible depth-k neighborhoods. -/

open Finset Filter Set
open scoped BigOperators Topology

namespace Certificate.OverlapBelief

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
variable (G : WeightedGraph V E)
variable {A : ℝ} (hA : 0 ≤ A) (hW : IncidentWeightBound G A)

private theorem norm_one_sub_sub_one_sub {a b : ℝ} :
    ‖(1-a)-(1-b)‖ = ‖a-b‖ := by
  have h : (1-a)-(1-b) = -(a-b) := by ring
  rw [h, norm_neg]

theorem norm_deficit_sub_betheDeficit_le (s : ℝ) (k : ℕ)
    (good : Finset V) (hgood : good ⊆ G.vertices) (hcompat : ∀ v ∈ good, goodRoot G k v) :
    ‖G.deficit s - betheDeficit G hA hW s‖ ≤
      ((G.vertices \ good).card : ℝ) +
        (G.vertices.card : ℝ) * ((contractionRate (Real.exp s) A : ℝ)^k * (A/(Real.exp s)^2)) := by
  let a (v : V) := Real.exp s * Tree.deletionRatio G.ends G.vertices G.edges G.weight (Real.exp s) v
  let b (v : V) := Real.exp s * message G (Real.exp_pos s) hA hW (v,none)
  let ε := (contractionRate (Real.exp s) A : ℝ)^k * (A/(Real.exp s)^2)
  have hD : G.deficit s = ∑ v ∈ G.vertices, (1-a v) := by
    simp [WeightedGraph.deficit, WeightedGraph.monomerCount, Finset.sum_sub_distrib, a]
  rw [hD, betheDeficit, ← Finset.sum_sub_distrib]
  change ‖∑ v ∈ G.vertices, ((1-a v)-(1-b v))‖ ≤
    ((G.vertices \ good).card : ℝ) + (G.vertices.card : ℝ)*ε
  have hε : 0 ≤ ε := by dsimp only [ε]; positivity
  have hsmall (v : V) (hv : v ∈ good) : ‖(1-a v)-(1-b v)‖ ≤ ε := by
    rw [norm_one_sub_sub_one_sub]
    exact norm_rootMonomer_sub_exact_le G (Real.exp_pos s) hA hW (hgood hv) (hcompat v hv)
  have hlarge (v : V) (hv : v ∈ G.vertices) : ‖(1-a v)-(1-b v)‖ ≤ 1 := by
    have ha := Tree.deletionRatio_pos_le G.ends G.edges G.weight G.weight_nonneg
      (Real.exp_pos s) G.ends_card hv
    have ha0 : 0 ≤ a v := mul_nonneg (Real.exp_nonneg s) ha.1.le
    have ha1 : a v ≤ 1 :=
      (mul_le_mul_of_nonneg_left ha.2 (Real.exp_nonneg s)).trans_eq
        (mul_inv_cancel₀ (Real.exp_pos s).ne')
    have hb := rootMonomer_mem G (Real.exp_pos s) hA hW v
    rw [norm_one_sub_sub_one_sub, Real.norm_eq_abs, abs_le]
    exact ⟨by linarith only [ha0,hb.2], by linarith only [ha1,hb.1]⟩
  calc
    _ ≤ ∑ v ∈ G.vertices, ‖(1-a v)-(1-b v)‖ := norm_sum_le _ _
    _ = (∑ v ∈ G.vertices \ good, ‖(1-a v)-(1-b v)‖) +
        ∑ v ∈ good, ‖(1-a v)-(1-b v)‖ := (Finset.sum_sdiff hgood).symm
    _ ≤ (∑ _v ∈ G.vertices \ good, (1 : ℝ)) + ∑ _v ∈ good, ε :=
      add_le_add (Finset.sum_le_sum fun v hv => hlarge v (Finset.mem_sdiff.mp hv).1)
        (Finset.sum_le_sum hsmall)
    _ ≤ _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card hgood)) hε)

include hW in
omit [DecidableEq E] [Fintype V] [Fintype E] in
private theorem totalWeight_le_card_mul :
    (∑ e ∈ G.edges, G.weight e) ≤ (G.vertices.card : ℝ) * A := by
  have hEq : (∑ v ∈ G.vertices, ∑ e ∈ Overlap.incidentEdges G v, G.weight e) =
      2 * ∑ e ∈ G.edges, G.weight e := by
    rw [Overlap.sum_incident_vertices, Finset.mul_sum]
    exact Finset.sum_congr rfl fun e he => by simp [G.ends_card e he, nsmul_eq_mul]
  have hSum : (∑ v ∈ G.vertices, ∑ e ∈ Overlap.incidentEdges G v, G.weight e) ≤
      (G.vertices.card : ℝ) * A := by
    calc
      _ ≤ ∑ _v ∈ G.vertices, A := by
        apply Finset.sum_le_sum
        intro v _
        change (∑ e ∈ Tree.incident G.ends G.vertices G.edges v, G.weight e) ≤ A
        rw [← incidentEdges_eq_incident]
        exact hW v
      _ = _ := by simp [nsmul_eq_mul]
  rw [hEq] at hSum
  linarith only [hSum, Finset.sum_nonneg (s := G.edges) (fun e _ => G.weight_nonneg e)]

include hA in
private theorem contractionError_mono {t s : ℝ} (hts : t ≤ s) (k : ℕ) :
    (contractionRate (Real.exp s) A : ℝ)^k * (A/(Real.exp s)^2) ≤
      (contractionRate (Real.exp t) A : ℝ)^k * (A/(Real.exp t)^2) := by
  have hsq : Real.exp t ^ 2 ≤ Real.exp s ^ 2 :=
    pow_le_pow_left₀ (Real.exp_nonneg t) (Real.exp_le_exp.mpr hts) 2
  have hrate : (contractionRate (Real.exp s) A : ℝ) ≤ (contractionRate (Real.exp t) A : ℝ) := by
    rw [coe_contractionRate (Real.exp_pos s) hA, coe_contractionRate (Real.exp_pos t) hA]
    exact div_le_div_of_nonneg_left hA (by positivity) (add_le_add hsq le_rfl)
  exact mul_le_mul (pow_le_pow_left₀ (by positivity) hrate _)
    (div_le_div_of_nonneg_left hA (by positivity) hsq) (by positivity) (by positivity)

/-- The error has a contribution from incompatible roots, a geometrically
decaying contribution from the other roots, and a high-fugacity cutoff tail. -/
theorem norm_logPartition_sub_betheLog_le
    (hw : ∀ e ∈ G.edges, 0 < G.weight e) {t T : ℝ} (htT : t ≤ T) (k : ℕ)
    (good : Finset V) (hgood : good ⊆ G.vertices) (hcompat : ∀ v ∈ good, goodRoot G k v) :
    ‖Real.log (G.Z t) - betheLog G hA hW t‖ ≤
      (T-t) * (((G.vertices \ good).card : ℝ) +
        (G.vertices.card : ℝ) * ((contractionRate (Real.exp t) A : ℝ)^k * (A/(Real.exp t)^2))) +
        2 * (G.vertices.card : ℝ) * (A/(Real.exp T)^2) := by
  let f (s : ℝ) := G.logCorrected s - betheCorrected G hA hW s
  let C := ((G.vertices \ good).card : ℝ) +
    (G.vertices.card : ℝ) * ((contractionRate (Real.exp t) A : ℝ)^k * (A/(Real.exp t)^2))
  have hder (s : ℝ) : HasDerivAt f (betheDeficit G hA hW s - G.deficit s) s := by
    exact ((G.hasDerivAt_logCorrected s).fun_sub
      (hasDerivAt_betheCorrected G hA hW hw s)).congr_deriv (by ring)
  have hclose : ‖f t - f T‖ ≤ C * (T-t) := by
    have h := (convex_Icc t T).norm_image_sub_le_of_norm_deriv_le
      (fun s _ => (hder s).differentiableAt) (C := C) (fun s hs => by
        rw [(hder s).deriv, norm_sub_rev]
        refine (norm_deficit_sub_betheDeficit_le G hA hW s k good hgood hcompat).trans ?_
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (contractionError_mono hA hs.1 k)
          (Nat.cast_nonneg _))) ⟨htT,le_rfl⟩ ⟨le_rfl,htT⟩
    simpa only [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr htT), neg_sub] using h
  have hFin := G.logCorrected_bound T
  have hB0 := betheCorrected_nonneg G hA hW hw T
  have hB := betheCorrected_le G hA hW hw T
  have he : Real.exp (-2*T) = ((Real.exp T)^2)⁻¹ := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_neg]
    congr 1
    ring
  have hFin' : G.logCorrected T ≤ (G.vertices.card : ℝ) * (A/(Real.exp T)^2) := by
    rw [he] at hFin
    calc
      _ ≤ ((G.vertices.card : ℝ)*A) * ((Real.exp T)^2)⁻¹ :=
        hFin.2.trans (mul_le_mul_of_nonneg_right (totalWeight_le_card_mul G hW) (by positivity))
      _ = _ := by rw [div_eq_mul_inv, mul_assoc]
  have hInf : ‖f T‖ ≤ 2 * (G.vertices.card : ℝ) * (A/(Real.exp T)^2) := by
    dsimp only [f]
    rw [Real.norm_eq_abs, abs_le]
    have hC : 0 ≤ (G.vertices.card : ℝ) * (A/(Real.exp T)^2) := by positivity
    exact ⟨by linarith only [hFin.1,hB,hC], by linarith only [hFin',hB0,hC]⟩
  have heq : Real.log (G.Z t) - betheLog G hA hW t = (f t-f T)+f T := by
    unfold f WeightedGraph.logCorrected betheCorrected
    ring
  rw [heq]
  calc
    _ ≤ ‖f t-f T‖ + ‖f T‖ := norm_add_le _ _
    _ ≤ _ := by simpa only [C, mul_comm (T-t)] using add_le_add hclose hInf

end Certificate.OverlapBelief

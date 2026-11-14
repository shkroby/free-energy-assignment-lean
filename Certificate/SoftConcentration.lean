import Certificate.SoftPressure
import Certificate.TreeBipartite

/-!
# One-row oscillation of the square monomer pressure

Vertex deletion removes precisely the changed inputs. Inserting that vertex
back changes the matching polynomial by a factor between one and one plus
the total activity of its incident edges.
-/

open Finset Set MeasureTheory Filter
open scoped BigOperators Topology

namespace Certificate

/-- The complete square graph with a prescribed nonnegative weight matrix. -/
def squareWeightedGraph {n : ℕ} (w : Fin n → Fin n → ℝ) (hw : ∀ i j, 0 ≤ w i j) :
    WeightedGraph (Fin n ⊕ Fin n) (Fin n × Fin n) where
  vertices := univ
  edges := univ
  ends := Tree.Bipartite.ends
  weight := fun ij => w ij.1 ij.2
  weight_nonneg := fun ij => hw ij.1 ij.2
  ends_card := fun e _ => Tree.Bipartite.ends_card e
  ends_subset := fun _ _ => Finset.subset_univ _

/-- The finite monomer pressure per row for a square weight matrix. -/
noncomputable def squareMonomerPressure {n : ℕ} (w : Fin n → Fin n → ℝ) (t : ℝ) : ℝ :=
  Real.log (Tree.monomerPartition Tree.Bipartite.ends univ univ
    (fun ij => w ij.1 ij.2) (Real.exp t)) / n

private theorem row_incident_card {n : ℕ} (i : Fin n) :
    (Tree.incident (E := Fin n × Fin n) Tree.Bipartite.ends univ univ (Sum.inl i)).card = n := by
  have h :
      Tree.incident (E := Fin n × Fin n) Tree.Bipartite.ends univ univ (Sum.inl i) =
        (univ : Finset (Fin n)).image (fun j => (i,j)) := by
    ext ⟨j,k⟩
    simp [Tree.incident, Tree.Bipartite.ends, eq_comm]
  rw [h, Finset.card_image_of_injective _ (fun j k h => congrArg Prod.snd h)]
  simp

private theorem row_deleted_partition_eq {n : ℕ} {w w' : Fin n → Fin n → ℝ}
    (i : Fin n) (hsame : ∀ j ≠ i, w j = w' j) (t : ℝ) :
    Tree.partition Tree.Bipartite.ends (univ.erase (Sum.inl i)) univ
      (fun ij : Fin n × Fin n => w ij.1 ij.2 * Real.exp (-2*t)) =
    Tree.partition Tree.Bipartite.ends (univ.erase (Sum.inl i)) univ
      (fun ij : Fin n × Fin n => w' ij.1 ij.2 * Real.exp (-2*t)) := by
  unfold Tree.partition
  refine Finset.sum_congr rfl fun M hM => Finset.prod_congr rfl fun ij hij => ?_
  have hi : ij.1 ≠ i := by
    intro h
    have hmem : Sum.inl i ∈ Tree.Bipartite.ends ij := by simp [Tree.Bipartite.ends, h]
    have hcontained := (Tree.mem_matchings.mp hM).2.1 ij hij hmem
    exact (mem_erase.mp hcontained).1 rfl
  change w ij.1 ij.2 * Real.exp (-2 * t) = w' ij.1 ij.2 * Real.exp (-2 * t)
  rw [hsame ij.1 hi]

private theorem row_delete_log_interval {n : ℕ} {w : Fin n → Fin n → ℝ}
    (hw₀ : ∀ j k, 0 ≤ w j k) (hw₁ : ∀ j k, w j k ≤ 1) (i : Fin n) (t : ℝ) :
    let a : Fin n × Fin n → ℝ := fun ij => w ij.1 ij.2 * Real.exp (-2*t)
    let P := Tree.partition Tree.Bipartite.ends univ univ a
    let Q := Tree.partition Tree.Bipartite.ends (univ.erase (Sum.inl i)) univ a
    0 ≤ Real.log P - Real.log Q ∧
      Real.log P - Real.log Q ≤ Real.log (1 + (n : ℝ) * Real.exp (-2 * t)) := by
  let E := Fin n × Fin n
  let V := Fin n ⊕ Fin n
  let a : E → ℝ := fun ij => w ij.1 ij.2 * Real.exp (-2*t)
  let P := Tree.partition Tree.Bipartite.ends (univ : Finset V) univ a
  let Q := Tree.partition Tree.Bipartite.ends (univ.erase (Sum.inl i)) univ a
  change 0 ≤ Real.log P - Real.log Q ∧
    Real.log P - Real.log Q ≤ Real.log (1 + (n : ℝ) * Real.exp (-2 * t))
  have ha (e : E) : 0 ≤ a e := mul_nonneg (hw₀ e.1 e.2) (Real.exp_nonneg _)
  have hP : 0 < P := zero_lt_one.trans_le (Tree.one_le_partition _ _ _ _ ha)
  have hQ : 0 < Q := zero_lt_one.trans_le (Tree.one_le_partition _ _ _ _ ha)
  have hlow : Q ≤ P := Tree.partition_mono_vertices _ (Finset.subset_univ _) _ _ ha
  have hup : P ≤ (1 + (n : ℝ) * Real.exp (-2 * t)) * Q := by
    have hup' := Tree.partition_vertex_deletion Tree.Bipartite.ends (univ : Finset V)
      (univ : Finset E) a (Sum.inl i)
    change P = Q + _ at hup'
    rw [hup', add_mul, one_mul]
    refine add_le_add le_rfl ?_
    let I := Tree.incident Tree.Bipartite.ends (univ : Finset V) (univ : Finset E) (Sum.inl i)
    calc
      _ ≤ ∑ _e ∈ I, Real.exp (-2 * t) * Q := by
        refine Finset.sum_le_sum fun e he => ?_
        have hv := (mem_filter.mp he).2.1
        have hsub : (univ : Finset V) \ Tree.Bipartite.ends e ⊆ univ.erase (Sum.inl i) := by
          intro v hv'
          refine mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
          intro h
          exact (mem_sdiff.mp hv').2 (h.symm ▸ hv)
        exact (mul_le_mul_of_nonneg_left (Tree.partition_mono_vertices _ hsub _ _ ha) (ha e)).trans
          (mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (Real.exp_nonneg _) (hw₁ e.1 e.2)) hQ.le)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, show I.card = n from row_incident_card i, mul_assoc]
  rw [← Real.log_div hP.ne' hQ.ne']
  exact ⟨Real.log_nonneg ((one_le_div hQ).mpr hlow),
    Real.log_le_log (div_pos hP hQ) ((div_le_iff₀ hQ).mpr hup)⟩

/-- Changing one row changes the pressure by at most
`log(1 + n / z^2) / n`, with `z = exp t`. -/
theorem squareMonomerPressure_row_oscillation {n : ℕ} (hn : 0 < n) {w w' : Fin n → Fin n → ℝ}
    (h₀ : ∀ i j, 0 ≤ w i j) (h₁ : ∀ i j, w i j ≤ 1)
    (h₀' : ∀ i j, 0 ≤ w' i j) (h₁' : ∀ i j, w' i j ≤ 1)
    (i : Fin n) (hsame : ∀ j ≠ i, w j = w' j) (t : ℝ) :
    |squareMonomerPressure w t - squareMonomerPressure w' t| ≤
      Real.log (1 + (n : ℝ) * Real.exp (-2 * t)) / n := by
  let G := squareWeightedGraph w h₀
  let G' := squareWeightedGraph w' h₀'
  have hGw : squareMonomerPressure w t = Real.log (G.Z t) / n := rfl
  have hGw' : squareMonomerPressure w' t = Real.log (G'.Z t) / n := rfl
  rw [hGw, hGw', ← sub_div, abs_div, abs_of_nonneg (show 0 ≤ (n : ℝ) from Nat.cast_nonneg n)]
  apply (div_le_div_iff_of_pos_right (Nat.cast_pos.mpr hn)).mpr
  have hcorr : Real.log (G.Z t) - Real.log (G'.Z t) = G.logCorrected t - G'.logCorrected t := by
    simp only [WeightedGraph.logCorrected, G, G', squareWeightedGraph]
    ring
  rw [hcorr, G.logCorrected_eq, G'.logCorrected_eq]
  have h := row_delete_log_interval h₀ h₁ i t
  have h' := row_delete_log_interval h₀' h₁' i t
  dsimp only at h h'
  rw [← row_deleted_partition_eq i hsame t] at h'
  change |Real.log (Tree.partition Tree.Bipartite.ends univ univ
       (fun ij : Fin n × Fin n => w ij.1 ij.2 * Real.exp (-2*t))) -
     Real.log (Tree.partition Tree.Bipartite.ends univ univ
       (fun ij : Fin n × Fin n => w' ij.1 ij.2 * Real.exp (-2*t)))| ≤ _
  exact abs_le.mpr ⟨by linarith only [h.1, h'.2], by linarith only [h.2, h'.1]⟩

end Certificate

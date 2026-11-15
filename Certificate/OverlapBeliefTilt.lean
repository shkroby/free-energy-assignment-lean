import Certificate.OverlapBeliefApproximation
import Certificate.OverlapBeliefSubgraph
import Certificate.OverlapSimplexTilt

/-! Uniform finite pressure bound against every bounded tilt of edge weights. -/

open Finset
open scoped BigOperators

namespace Certificate.OverlapBelief

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
variable (G : WeightedGraph V E)

/-- Finite soft tilt bound. The same compatible-root set works for every
tilt because the tilted weights leave the graph structure fixed. -/
theorem logPartition_tilt_le {A η t T τ : ℝ} {f : E → ℝ} (hA : 0 ≤ A)
    (hW : IncidentWeightBound G A) (hWt : IncidentWeightBound (tilt G τ f) A)
    (hw : ∀ e ∈ G.edges, 0 < G.weight e) (htT : t ≤ T)
    (hη : 0 < η) (hf : ∀ e ∈ G.edges, |f e| ≤ 1)
    (rows : Finset V) (hRowsV : rows ⊆ G.vertices)
    (hRows : ∀ e ∈ G.edges, (rows ∩ G.ends e).card = 1)
    (k : ℕ) (good : Finset V) (hGv : good ⊆ G.vertices)
    (hCompat : ∀ v ∈ good, goodRoot G k v) :
    let γ := occupation G (Real.exp_pos t) hA hW
    Real.log ((tilt G τ f).Z t) ≤
      Real.log (G.Z t) + τ * (∑ e ∈ G.edges, f e * γ e) +
        (rows.card : ℝ) * (16 * τ^2 / η) +
        ((rows \ Overlap.goodRows G rows γ η).card : ℝ) * (2 * |τ|) +
        2 * ((T-t) * (((G.vertices \ good).card : ℝ) +
          (G.vertices.card : ℝ) * ((contractionRate (Real.exp t) A : ℝ)^k * (A/(Real.exp t)^2))) +
          2 * (G.vertices.card : ℝ) * (A/(Real.exp T)^2)) := by
  let H := tilt G τ f
  let γ := occupation G (Real.exp_pos t) hA hW
  let p := occupation H (Real.exp_pos t) hA hWt
  let E₀ := (T-t) * (((G.vertices \ good).card : ℝ) +
    (G.vertices.card : ℝ) * ((contractionRate (Real.exp t) A : ℝ)^k * (A/(Real.exp t)^2))) +
    2 * (G.vertices.card : ℝ) * (A/(Real.exp T)^2)
  have hwH (e : E) (he : e ∈ H.edges) : 0 < H.weight e :=
    mul_pos (hw e he) (Real.exp_pos _)
  have hpH := occupation_feasible H (Real.exp_pos t) hA hWt hwH
  have hp : Overlap.Feasible G p := hpH
  have hγ := occupation_feasible G (Real.exp_pos t) hA hW hw
  have hstat := occupation_stationary G (Real.exp_pos t) hA hW hw
  have hB := Overlap.finiteBethe_perturbed_bound G (t := τ) rows hRowsV hRows hγ hp
    (fun e he => occupation_mem_Ioo G (Real.exp_pos t) hA hW he (hw e he))
    (fun v _ => occupation_vertexSlack_pos G (Real.exp_pos t) hA hW v) hstat hη hf
  have hObj := Overlap.finiteBethe_eq_of_tilt G H (Real.exp t) τ p f rfl rfl rfl hw (fun _ _ => rfl)
  rw [← hObj] at hB
  have hF₀ : ‖Real.log (G.Z t) - betheLog G hA hW t‖ ≤ E₀ :=
    norm_logPartition_sub_betheLog_le G hA hW hw htT k good hGv hCompat
  have hF₁ : ‖Real.log (H.Z t) - betheLog H hA hWt t‖ ≤ E₀ :=
    norm_logPartition_sub_betheLog_le H hA hWt hwH htT k good hGv
      (fun v hv => goodRoot_tilt G (hCompat v hv))
  rw [Real.norm_eq_abs, abs_le] at hF₀ hF₁
  change betheLog H hA hWt t - betheLog G hA hW t ≤ τ * (∑ e ∈ G.edges, f e * γ e) +
      (rows.card : ℝ) * (16*τ^2/η) + ((rows \ Overlap.goodRows G rows γ η).card : ℝ)*(2*|τ|) at hB
  change Real.log (H.Z t) ≤ Real.log (G.Z t) + τ * (∑ e ∈ G.edges, f e * γ e) +
    (rows.card : ℝ) * (16 * τ^2 / η) + ((rows \ Overlap.goodRows G rows γ η).card : ℝ)*(2*|τ|) + 2*E₀
  linarith only [hB,hF₀.1,hF₁.2]

end Certificate.OverlapBelief

import Certificate.OverlapCanonicalTrim
import Certificate.OverlapRowTests
import Certificate.Endpoints

/-! Finite-depth edge occupations on the degree-trimmed canonical tree. -/

namespace Certificate.CanonicalTree

/-- The directed message from a vertex towards its parent, initialized with
the cavity value for the empty neighborhood. -/
noncomputable def trimmedDownwardIterate (β d R z : ℝ) (D k : ℕ)
    (ω : Environment) (v : Vertex) : ℝ :=
  TreeBoundary.fromBoundary z child (trimmedWeight β d R D ω) (fun _ => z⁻¹) k v

/-- The root's directed message towards its indicated child. -/
noncomputable def trimmedRootCavityIterate (β d R z : ℝ) (D : ℕ) (ω : Environment) :
    ℕ → ℕ → ℝ
  | 0, _ => z⁻¹
  | k+1, i => TreeBoundary.update z
      (fun j => if j = i then 0 else trimmedWeight β d R D ω [] j)
      (fun j => trimmedDownwardIterate β d R z D k ω (child [] j))

/-- The occupation computed using k updates in both directions. -/
noncomputable def trimmedRootOccupationIterate (β d R z : ℝ) (D k : ℕ)
    (ω : Environment) (i : ℕ) : ℝ :=
  edgeOccupation (trimmedWeight β d R D ω [] i)
    (trimmedRootCavityIterate β d R z D ω k i)
    (trimmedDownwardIterate β d R z D k ω (child [] i))

/-- The bounded squared occupation sum of the finite-depth computation. -/
noncomputable def trimmedSquareTest (β d R z : ℝ) (D k : ℕ) (ω : Environment) : ℝ :=
  Overlap.squareRowTest (Finset.range (cutoffOffspringNat d R (ω [])))
    (trimmedRootOccupationIterate β d R z D k ω)

/-- The bounded test for a small third occupation in the finite-depth computation. -/
noncomputable def trimmedSmallThirdTest (β d R z η : ℝ) (D k : ℕ) (ω : Environment) : ℝ :=
  Overlap.smallOccupationTest η
    (Overlap.thirdOccupation (Finset.range (cutoffOffspringNat d R (ω [])))
      (trimmedRootOccupationIterate β d R z D k ω))

end Certificate.CanonicalTree

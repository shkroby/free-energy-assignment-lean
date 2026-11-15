import Certificate.OverlapUnorderedTree
import Certificate.LocalPlaneBrackets

/-! Encode a marked plane neighborhood as the corresponding unordered tree. -/

open MeasureTheory Set

namespace Certificate.LocalExploration.PlaneShape

open UnorderedTree

variable (shape : PlaneShape)

noncomputable def childLength (marks : shape.NonRootSlot → ℝ) (v : List ℕ) (i : ℕ) : ℝ := by
  classical
  exact if hs : v++[i] ∈ shape.slots then marks ⟨⟨v++[i],hs⟩,by simp⟩ else 0

noncomputable def encodeUnordered (marks : shape.NonRootSlot → ℝ) : Depth shape.depth :=
  ofChildren shape.childCount (shape.childLength marks) shape.depth []

theorem measurable_encodeUnordered : Measurable shape.encodeUnordered := by
  apply measurable_ofChildren
  · exact fun v => measurable_const
  · intro v i
    classical
    by_cases hs : v++[i] ∈ shape.slots
    · simpa only [childLength, dif_pos hs] using
        (measurable_pi_apply (⟨⟨v++[i],hs⟩,by simp⟩ : shape.NonRootSlot))
    · simp only [childLength, dif_neg hs]
      exact measurable_const

noncomputable def encodeUnorderedAt {k : ℕ} (hk : shape.depth = k)
    (marks : shape.NonRootSlot → ℝ) : Depth k :=
  hk ▸ shape.encodeUnordered marks

theorem measurable_encodeUnorderedAt {k : ℕ} (hk : shape.depth = k) :
    Measurable (shape.encodeUnorderedAt hk) := by
  subst k
  exact shape.measurable_encodeUnordered

private theorem node_congr_nat {k n m : ℕ} (h : n = m) (x y : ℕ → ℝ × Depth k)
    (hxy : ∀ i < m, x i = y i) :
    node n (fun i => x i) = node m (fun i => y i) := by
  subst n
  exact congrArg (node m) (funext fun i => hxy i i.isLt)

/-- Reading a rooted tree's child counts and edge lengths agrees with
encoding the resulting plane neighborhood. -/
theorem encodeUnordered_ofChildren {count : List ℕ → ℕ} {length : List ℕ → ℕ → ℝ}
    {marks : shape.NonRootSlot → ℝ}
    (hc : ∀ v ∈ shape.slots, v.length < shape.depth → count v = shape.childCount v)
    (hw : ∀ v ∈ shape.slots, ∀ i, v++[i] ∈ shape.slots → length v i = shape.childLength marks v i) :
    ofChildren count length shape.depth [] = shape.encodeUnordered marks := by
  have he (k : ℕ) (v : List ℕ) (hv : v ∈ shape.slots) (hdep : k+v.length ≤ shape.depth) :
      ofChildren count length k v = ofChildren shape.childCount (shape.childLength marks) k v := by
    induction k generalizing v with
    | zero => rfl
    | succ k ih =>
      have hd : v.length < shape.depth := by omega
      have hn := hc v hv hd
      simp only [ofChildren]
      refine node_congr_nat (k := k) hn
        (fun i => (length v i, ofChildren count length k (v++[i])))
        (fun i => (shape.childLength marks v i,
          ofChildren shape.childCount (shape.childLength marks) k (v++[i]))) ?_
      intro i hi
      have hmem := (shape.child_mem v i).mpr ⟨hv,hd,hi⟩
      exact Prod.ext (hw v hv i hmem) (ih (v++[i]) hmem (by simp; omega))
  exact he _ _ shape.root_mem (by simp)

theorem encodeUnorderedAt_ofChildren {k : ℕ} (hk : shape.depth = k)
    {count : List ℕ → ℕ} {length : List ℕ → ℕ → ℝ}
    {marks : shape.NonRootSlot → ℝ}
    (hc : ∀ v ∈ shape.slots, v.length < shape.depth → count v = shape.childCount v)
    (hw : ∀ v ∈ shape.slots, ∀ i, v++[i] ∈ shape.slots → length v i = shape.childLength marks v i) :
    ofChildren count length k [] = shape.encodeUnorderedAt hk marks := by
  subst k
  exact shape.encodeUnordered_ofChildren hc hw

end Certificate.LocalExploration.PlaneShape

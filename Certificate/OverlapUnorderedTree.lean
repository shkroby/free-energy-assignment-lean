import Certificate.PoissonFull
import Mathlib.Data.List.FinRange

/-! An unordered marked neighborhood records the multiset of child
lengths and subtrees at each vertex. -/

open MeasureTheory Set

namespace Certificate.UnorderedTree

/-- A rooted marked tree truncated at the indicated depth, with sibling
order forgotten. -/
def Depth : ℕ → Type
  | 0 => PUnit
  | k+1 => Multiset (ℝ × Depth k)

def unorderedBatch {Y : Type*} (x : PoissonBatch Y) : Multiset Y :=
  (List.ofFn x.2 : Multiset Y)

instance measurableSpaceDepth : (k : ℕ) → MeasurableSpace (Depth k)
  | 0 => inferInstanceAs (MeasurableSpace PUnit)
  | k+1 =>
    letI : MeasurableSpace (Depth k) := measurableSpaceDepth k
    MeasurableSpace.map (unorderedBatch (Y := ℝ × Depth k)) inferInstance

def ofBatch (k : ℕ) (x : PoissonBatch (ℝ × Depth k)) : Depth (k+1) := unorderedBatch x

theorem measurable_ofBatch (k : ℕ) : Measurable (ofBatch k) :=
  measurable_iff_le_map.mpr le_rfl

theorem measurable_ofBatch_iff {Y : Type*} [MeasurableSpace Y] {k : ℕ} {f : Depth (k+1) → Y} :
    Measurable f ↔ Measurable (fun b => f (ofBatch k b)) := by
  constructor
  · intro h
    exact h.comp (measurable_ofBatch k)
  · intro h
    rw [measurable_iff_le_map] at h ⊢
    exact h

def node {k : ℕ} (n : ℕ) (xs : Fin n → ℝ × Depth k) : Depth (k+1) := ofBatch k ⟨n,xs⟩

theorem measurable_node (k n : ℕ) : Measurable (node (k := k) n) :=
  (measurable_ofBatch k).comp (measurable_poissonBatch_mk n)

theorem node_perm {k n : ℕ} (xs : Fin n → ℝ × Depth k) (σ : Equiv.Perm (Fin n)) :
    node n (xs ∘ σ) = node n xs := by
  exact Multiset.coe_eq_coe.mpr (σ.ofFn_comp_perm xs)

/-- A batch can be assembled measurably from its count and infinite mark sequence. -/
theorem measurable_batchOfCount {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    {count : Ω → ℕ} {mark : Ω → ℕ → Y}
    (hc : Measurable count) (hm : ∀ i, Measurable (fun ω => mark ω i)) :
    Measurable (fun ω => (⟨count ω, fun i => mark ω i⟩ : PoissonBatch Y)) := by
  intro S hS
  have he : (fun ω => (⟨count ω, fun i => mark ω i⟩ : PoissonBatch Y)) ⁻¹' S =
      ⋃ n : ℕ, {ω | count ω = n} ∩
        (fun ω => (⟨n, fun i => mark ω i⟩ : PoissonBatch Y)) ⁻¹' S := by
    ext ω
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_ofPred_eq]
    constructor
    · intro h
      exact ⟨count ω,rfl,h⟩
    · rintro ⟨n,hn,h⟩
      subst n
      exact h
  rw [he]
  exact MeasurableSet.iUnion fun n => (measurableSet_eq_fun hc measurable_const).inter
    (((measurable_poissonBatch_mk n).comp (measurable_pi_iff.mpr fun i => hm i)) hS)

def ofChildren (count : List ℕ → ℕ) (length : List ℕ → ℕ → ℝ) :
    (k : ℕ) → List ℕ → Depth k
  | 0, _ => PUnit.unit
  | k+1, v => node (count v) (fun i => (length v i, ofChildren count length k (v++[i.val])))

theorem measurable_ofChildren {Ω : Type*} [MeasurableSpace Ω]
    {count : Ω → List ℕ → ℕ} {length : Ω → List ℕ → ℕ → ℝ}
    (hc : ∀ v, Measurable (fun ω => count ω v))
    (hl : ∀ v i, Measurable (fun ω => length ω v i))
    (k : ℕ) (v : List ℕ) :
    Measurable (fun ω => ofChildren (count ω) (length ω) k v) := by
  induction k generalizing v with
  | zero => exact measurable_const
  | succ k ih =>
    exact (measurable_ofBatch k).comp
      (measurable_batchOfCount (hc v) (fun i => (hl v i).prodMk (ih (v++[i]))))

theorem ofChildren_shift (count : List ℕ → ℕ) (length : List ℕ → ℕ → ℝ) (i : ℕ)
    (k : ℕ) (v : List ℕ) :
    ofChildren (fun w => count (i::w)) (fun w => length (i::w)) k v =
      ofChildren count length k (i::v) := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih =>
    simp only [ofChildren]
    congr 1
    funext j
    rw [ih]
    rfl

end Certificate.UnorderedTree

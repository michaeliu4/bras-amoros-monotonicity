import Results.Genus.CapFourMass.SignedReflectionFixedSource
import Results.Genus.CapFourMass.SignedReflectionFreeBlock

/-! A strict two-path split after deleting an interior path vertex and both
of its neighbors. Empty sides are represented by Fin0, not dummy vertices. -/
namespace SubmittedGenus.CapFourMass.SignedReflectionSplit

abbrev Positions (n : ℕ) (k : Fin (n+2)) := Fin (k.val-1) ⊕ Fin (n-k.val)

def index (n : ℕ) (k : Fin (n+2)) : Positions n k → Fin (n+2)
  | .inl i => ⟨i.val,by have:=i.isLt; have:=k.isLt; omega⟩
  | .inr i => ⟨k.val+2+i.val,by have:=i.isLt; have:=k.isLt; omega⟩

/-- Neither side crosses a deleted slot, even if one side is empty. -/
def equiv (n : ℕ) (k : Fin (n+2)) :
    Positions n k ≃ {j : Fin (n+2) // j.val+1<k.val ∨ k.val+1<j.val} where
  toFun i := ⟨index n k i,by
    cases i with
    | inl i => left; have:=i.isLt; dsimp [index]; omega
    | inr i => right; dsimp [index]; omega⟩
  invFun j := if h : j.val.val+1<k.val then .inl ⟨j.val.val,by omega⟩
    else .inr ⟨j.val.val-k.val-2,by have:=j.property; have:=j.val.isLt; omega⟩
  left_inv i := by
    cases i with
    | inl i =>
      have h : (index n k (.inl i)).val+1<k.val := by have:=i.isLt; dsimp [index]; omega
      simp only [dif_pos h]
      rfl
    | inr i =>
      have h : ¬(index n k (.inr i)).val+1<k.val := by dsimp [index]; omega
      simp only [dif_neg h]
      congr 1
      apply Fin.ext
      dsimp [index]
      omega
  right_inv j := by
    apply Subtype.ext
    dsimp only
    split_ifs with h
    · rfl
    · apply Fin.ext
      have:=j.property
      dsimp [index]
      omega

lemma index_injective (n : ℕ) (k : Fin (n+2)) : Function.Injective (index n k) := by
  intro i j he
  exact (equiv n k).injective (Subtype.ext he)

/-- Consecutive within a single side; no cross-gap or closing edge. -/
def Adjacent (n : ℕ) (k : Fin (n+2)) : Positions n k → Positions n k → Prop
  | .inl i,.inl j => i.val+1=j.val ∨ j.val+1=i.val
  | .inr i,.inr j => i.val+1=j.val ∨ j.val+1=i.val
  | _,_ => False

/-- The split relation preserves precisely the full path's genuine edges. -/
theorem index_adjacent_iff (n : ℕ) (k : Fin (n+2)) (i j : Positions n k) :
    ((index n k i).val+1=(index n k j).val ∨ (index n k j).val+1=(index n k i).val) ↔
      Adjacent n k i j := by
  cases i with
  | inl i =>
    cases j with
    | inl j => rfl
    | inr j =>
      have hi:=i.isLt
      have hj:=j.isLt
      have hk:=k.isLt
      change (i.val+1=k.val+2+j.val ∨ k.val+2+j.val+1=i.val) ↔ False
      constructor
      · intro h; rcases h with h | h <;> omega
      · intro h; contradiction
  | inr i =>
    cases j with
    | inl j =>
      have hi:=i.isLt
      have hj:=j.isLt
      have hk:=k.isLt
      change (k.val+2+i.val+1=j.val ∨ j.val+1=k.val+2+i.val) ↔ False
      constructor
      · intro h; rcases h with h | h <;> omega
      · intro h; contradiction
    | inr j => dsimp [index,Adjacent]; omega

/-- Two distinct actual path neighbors exhaust the deleted adjacent slots.
Thus an arbitrary remaining index belongs to exactly the two strict sides. -/
theorem outside_neighbors_iff {n : ℕ} (k u v j : Fin (n+2))
    (hu : k.val+1=u.val ∨ u.val+1=k.val)
    (hv : k.val+1=v.val ∨ v.val+1=k.val) (huv : u≠v) :
    (j.val+1<k.val ∨ k.val+1<j.val) ↔ (j≠k ∧ j≠u ∧ j≠v) := by
  have hne : u.val≠v.val := fun h=>huv (Fin.ext h)
  simp only [Ne,Fin.ext_iff]
  omega

theorem interior_of_neighbors {n : ℕ} (k u v : Fin (n+2))
    (hu : k.val+1=u.val ∨ u.val+1=k.val)
    (hv : k.val+1=v.val ∨ v.val+1=k.val) (huv : u≠v) : 1≤k.val ∧ k.val+1<n+2 := by
  have hne : u.val≠v.val := fun h=>huv (Fin.ext h)
  have:=u.isLt
  have:=v.isLt
  omega

end SubmittedGenus.CapFourMass.SignedReflectionSplit

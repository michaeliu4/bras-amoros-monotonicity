import Results.Genus.RawGraph.PackedAcceptance.ModularReflection

/-! A reusable complete residue order for the two adjacent reflections.
All positions are explicit natural-number formulas, including the zero residue.
Deleting the three distinguished residues will produce the physical layouts. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionZigzag

/-- Residues in the order 0,1,-1,2,-2,... modulo m+1. -/
def forward (m : ℕ) (j : Fin (m+1)) : Fin (m+1) :=
  ⟨if j.val=0 then 0 else if j.val%2=0 then m+1-j.val/2 else (j.val+1)/2,by
    have hj := j.isLt
    split_ifs <;> omega⟩

def backward (m : ℕ) (x : Fin (m+1)) : Fin (m+1) :=
  ⟨if x.val=0 then 0 else if x.val≤(m+1)/2 then 2*x.val-1 else 2*(m+1-x.val),by
    have hx := x.isLt
    split_ifs <;> omega⟩

lemma backward_forward (m : ℕ) (j : Fin (m+1)) : backward m (forward m j)=j := by
  apply Fin.ext
  have hj := j.isLt
  simp only [backward,forward,Fin.val_mk]
  split_ifs <;> omega

lemma forward_backward (m : ℕ) (x : Fin (m+1)) : forward m (backward m x)=x := by
  apply Fin.ext
  have hx := x.isLt
  simp only [backward,forward,Fin.val_mk]
  split_ifs <;> omega

/-- A computable permutation; no graph decomposition or choice is used. -/
def order (m : ℕ) : Fin (m+1) ≃ Fin (m+1) where
  toFun := forward m
  invFun := backward m
  left_inv := backward_forward m
  right_inv := forward_backward m

lemma add_mod_iff {m t : ℕ} (ht : t<m+1) (u v : Fin (m+1)) :
    (u.val+v.val)%(m+1)=t ↔ u.val+v.val=t ∨ u.val+v.val=m+1+t := by
  have hu := u.isLt
  have hv := v.isLt
  constructor
  · intro h
    by_cases hs:u.val+v.val<m+1
    · exact Or.inl ((Nat.mod_eq_of_lt hs).symm.trans h)
    · right
      have hs' : u.val+v.val-(m+1)<m+1 := by omega
      rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt hs'] at h
      omega
  · rintro (h|h)
    · rw [h,Nat.mod_eq_of_lt ht]
    · rw [h,Nat.add_mod_left,Nat.mod_eq_of_lt ht]

/-- Every non-loop edge of the two adjacent modular reflections is a
consecutive pair in the explicit order. -/
lemma adjacent_of_pair (m : ℕ) (i j : Fin (m+1)) (hne : i≠j)
    (h : (forward m i).val+(forward m j).val=0 ∨
      (forward m i).val+(forward m j).val=m+1 ∨
      (forward m i).val+(forward m j).val=1 ∨
      (forward m i).val+(forward m j).val=m+2) :
    i.val+1=j.val ∨ j.val+1=i.val := by
  have hi := i.isLt
  have hj := j.isLt
  have hne' : i.val≠j.val := fun he=>hne (Fin.ext he)
  simp only [forward,Fin.val_mk] at h
  split_ifs at h <;> omega

lemma adjacent_of_mod_pair (m : ℕ) (hm : 0<m) (i j : Fin (m+1)) (hne : i≠j)
    (h : ((forward m i).val+(forward m j).val)%(m+1)=0 ∨
      ((forward m i).val+(forward m j).val)%(m+1)=1) :
    i.val+1=j.val ∨ j.val+1=i.val := by
  apply adjacent_of_pair m i j hne
  rcases h with h|h
  · rcases (add_mod_iff (by omega) _ _).mp h with h|h
    · exact Or.inl h
    · exact Or.inr (Or.inl (by simpa using h))
  · rcases (add_mod_iff (by omega) _ _).mp h with h|h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (by simpa [Nat.add_assoc] using h)))

#print axioms backward_forward
#print axioms forward_backward
#print axioms adjacent_of_pair
#print axioms adjacent_of_mod_pair
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionZigzag

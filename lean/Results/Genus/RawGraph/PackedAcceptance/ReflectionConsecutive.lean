import Results.Genus.RawGraph.PackedAcceptance.ReflectionZigzag
import Mathlib.Tactic.LinearCombination

namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionConsecutive

abbrev asResidue (m : ℕ) (x : Fin (m+1)) : ZMod (m+1) := ZMod.finEquiv (m+1) x

/-- Centering and, for odd r, reversing the universal two-reflection order. -/
def affine (m r : ℕ) : ZMod (m+1) ≃ ZMod (m+1) where
  toFun := fun x=>if r%2=0 then ((r/2:ℕ):ZMod (m+1))+x else (((r+1)/2:ℕ):ZMod (m+1))-x
  invFun := fun x=>if r%2=0 then x-((r/2:ℕ):ZMod (m+1)) else (((r+1)/2:ℕ):ZMod (m+1))-x
  left_inv := by intro x; split_ifs <;> simp_all
  right_inv := by intro x; split_ifs <;> simp_all

/-- The full residue path, before removing 0 and the two pivots. -/
abbrev order (m r : ℕ) : Fin (m+1) ≃ Fin (m+1) :=
  (ReflectionZigzag.order m).trans (affine m r)

lemma zigzag_cast (m : ℕ) (j : Fin (m+1)) :
    (asResidue m (ReflectionZigzag.forward m j))=
      if j.val%2=0 then -((j.val/2:ℕ):ZMod (m+1)) else (((j.val+1)/2:ℕ):ZMod (m+1)) := by
  have hj := j.isLt
  have he := ZMod.natCast_zmod_val (n:=m+1) (asResidue m (ReflectionZigzag.forward m j))
  change (((ReflectionZigzag.forward m j).val:ℕ):ZMod (m+1))=_ at he
  rw [←he]
  simp only [ReflectionZigzag.forward,Fin.val_mk]
  by_cases hz:j.val=0
  · simp [hz]
  · simp only [hz,ite_false]
    by_cases hp:j.val%2=0
    · simp only [hp,ite_true]
      have hle : j.val/2≤m+1 := by omega
      rw [Nat.cast_sub hle]
      simp
    · simp [hp]

lemma order_cast (m r : ℕ) (j : Fin (m+1)) :
    (asResidue m (order m r j))=
      if r%2=0 then ((r/2:ℕ):ZMod (m+1))+(asResidue m (ReflectionZigzag.forward m j))
      else (((r+1)/2:ℕ):ZMod (m+1))-(asResidue m (ReflectionZigzag.forward m j)) := rfl

/-- Distinct residues related by either original reflection have adjacent
positions, uniformly in multiplicity and the consecutive pivot location. -/
lemma adjacent_of_pair (m r : ℕ) (hm : 0<m) (i j : Fin (m+1)) (hne : i≠j)
    (h : (asResidue m (order m r i))+(asResidue m (order m r j))=(r:ZMod (m+1)) ∨
      (asResidue m (order m r i))+(asResidue m (order m r j))=((r+1:ℕ):ZMod (m+1))) :
    i.val+1=j.val ∨ j.val+1=i.val := by
  have hs : (asResidue m (ReflectionZigzag.forward m i))+
      (asResidue m (ReflectionZigzag.forward m j))=0 ∨
      (asResidue m (ReflectionZigzag.forward m i))+
      (asResidue m (ReflectionZigzag.forward m j))=1 := by
    simp only [order_cast] at h
    by_cases hp:r%2=0
    · simp only [hp,ite_true] at h
      have hc : ((r/2:ℕ):ZMod (m+1))+((r/2:ℕ):ZMod (m+1))=(r:ZMod (m+1)) := by
        rw [←Nat.cast_add]
        congr 1
        omega
      rcases h with h|h
      · left; linear_combination h-hc
      · right; push_cast at h; linear_combination h-hc
    · simp only [hp,ite_false] at h
      have hc : (((r+1)/2:ℕ):ZMod (m+1))+(((r+1)/2:ℕ):ZMod (m+1))=((r+1:ℕ):ZMod (m+1)) := by
        rw [←Nat.cast_add]
        congr 1
        omega
      rcases h with h|h
      · right; push_cast at hc; linear_combination hc-h
      · left; linear_combination hc-h
  apply ReflectionZigzag.adjacent_of_mod_pair m hm i j hne
  rcases hs with hs|hs
  · left
    have hv := congrArg ZMod.val hs
    rw [ZMod.val_add,ZMod.val_zero] at hv
    exact hv
  · right
    have hv := congrArg ZMod.val hs
    rw [ZMod.val_add,ZMod.val_one_eq_one_mod,Nat.mod_eq_of_lt (show 1<m+1 by omega)] at hv
    exact hv

/-- The deleted zero residue has exactly the pivot-index position r. -/
lemma order_zero (m : ℕ) (r : Fin (m+1)) : order m r.val r=0 := by
  apply (ZMod.finEquiv (m+1)).injective
  change asResidue m (order m r.val r)=0
  rw [order_cast,zigzag_cast]
  split_ifs <;> simp_all

#print axioms order_zero
#print axioms zigzag_cast
#print axioms adjacent_of_pair
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionConsecutive

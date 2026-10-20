import Results.Genus.RawGraph.PackedAcceptance.ReflectionFixedOrbit
import Results.Genus.RawGraph.PackedAcceptance.ReflectionOrbitDelete

namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionFixedOrbit
open ReflectionCoset ReflectionOrbitDelete ReflectionDelete

lemma normalizedTarget_lt (n : ℕ) (t : ZMod (n+2)) (u : (ZMod (n+2))ˣ)
    (hnext : t+(u:ZMod (n+2))≠0) : (normalizedTarget n t u).val<n+1 := by
  have hv := (normalizedTarget n t u).isLt
  by_contra h
  have he : (normalizedTarget n t u).val=n+1 := by omega
  have hn := normalizedTarget_next n t u
  have hz : ((((normalizedTarget n t u).val+1:ℕ):ZMod (n+2)))=0 := by
    rw [he]
    change ((n+2:ℕ):ZMod (n+2))=0
    exact ZMod.natCast_self _
  rw [hz,mul_zero] at hn
  exact hnext hn.symm

variable {g : ℕ} [NeZero g]

lemma zero_affine (n : ℕ) : affineValue (0:Fin g) (0:ZMod (n+2))=0 := by
  simp [affineValue]

lemma zero_target_value (n : ℕ) (r : ZMod (g*(n+2)))
    (hfix : (r-affineValue (0:Fin g) (0:ZMod (n+2))).val%g=0) :
    affineValue (0:Fin g) (target n 0 r hfix)=r := by
  simpa only [zero_affine,sub_zero] using target_value n (0:Fin g) r hfix

lemma zero_next_ne (n : ℕ) (r p : ZMod (g*(n+2)))
    (hfix : (r-affineValue (0:Fin g) (0:ZMod (n+2))).val%g=0) (u : (ZMod (n+2))ˣ)
    (hgap : scaleHom g (n+2) (u:ZMod (n+2))=p-r) (hp : p≠0) :
    target n (0:Fin g) r hfix+(u:ZMod (n+2))≠0 := by
  have he : affineValue (0:Fin g) (target n 0 r hfix+(u:ZMod (n+2)))=p := by
    rw [affineValue_add,zero_target_value,hgap]
    ring
  intro h
  rw [h,zero_affine] at he
  exact hp he.symm

/-- The zero position is not the final slot because the second original
reflection target p is nonzero. -/
def zeroCut (n : ℕ) (r p : ZMod (g*(n+2)))
    (hfix : (r-affineValue (0:Fin g) (0:ZMod (n+2))).val%g=0) (u : (ZMod (n+2))ˣ)
    (hgap : scaleHom g (n+2) (u:ZMod (n+2))=p-r) (hp : p≠0) : Fin (n+1) :=
  ⟨(normalizedTarget n (target n 0 r hfix) u).val,
    normalizedTarget_lt n _ u (zero_next_ne n r p hfix u hgap hp)⟩

lemma zeroCut_castSucc (n : ℕ) (r p : ZMod (g*(n+2)))
    (hfix : (r-affineValue (0:Fin g) (0:ZMod (n+2))).val%g=0) (u : (ZMod (n+2))ˣ)
    (hgap : scaleHom g (n+2) (u:ZMod (n+2))=p-r) (hp : p≠0) :
    (zeroCut n r p hfix u hgap hp).castSucc=normalizedTarget n (target n 0 r hfix) u := Fin.ext rfl

lemma order_zero_at (n : ℕ) (r p : ZMod (g*(n+2)))
    (hfix : (r-affineValue (0:Fin g) (0:ZMod (n+2))).val%g=0) (u : (ZMod (n+2))ˣ)
    (hgap : scaleHom g (n+2) (u:ZMod (n+2))=p-r) (hp : p≠0) :
    (order n (0:Fin g) r hfix u (zeroCut n r p hfix u hgap hp).castSucc).val=0 := by
  rw [order_val,zeroCut_castSucc,phaseOrder_zero,zero_affine]

abbrev NonzeroCoset (g L : ℕ) (a : Fin g) := {x : Coset g L a // x.val≠0}

/-- Complete physical order for the fixed coset containing zero, after
removing precisely that nonphysical residue. -/
def deletedOrder (n : ℕ) (r p : ZMod (g*(n+2)))
    (hfix : (r-affineValue (0:Fin g) (0:ZMod (n+2))).val%g=0) (u : (ZMod (n+2))ˣ)
    (hgap : scaleHom g (n+2) (u:ZMod (n+2))=p-r) (hp : p≠0) :
    Fin (n+1) ≃ NonzeroCoset g (n+2) 0 :=
  deleteSubtypeZero (order n (0:Fin g) r hfix u) (zeroCut n r p hfix u hgap hp)
    (order_zero_at n r p hfix u hgap hp)

lemma deletedOrder_val (n : ℕ) (r p : ZMod (g*(n+2)))
    (hfix : (r-affineValue (0:Fin g) (0:ZMod (n+2))).val%g=0) (u : (ZMod (n+2))ˣ)
    (hgap : scaleHom g (n+2) (u:ZMod (n+2))=p-r) (hp : p≠0) (j : Fin (n+1)) :
    (deletedOrder n r p hfix u hgap hp j).val.val=
      (order n (0:Fin g) r hfix u ((zeroCut n r p hfix u hgap hp).castSucc.succAbove j)).val := rfl

lemma deletedOrder_adjacent (n : ℕ) (r p : ZMod (g*(n+2)))
    (hfix : (r-affineValue (0:Fin g) (0:ZMod (n+2))).val%g=0) (u : (ZMod (n+2))ˣ)
    (hgap : scaleHom g (n+2) (u:ZMod (n+2))=p-r) (hp : p≠0)
    (i j : Fin (n+1)) (hne : i≠j)
    (h : (deletedOrder n r p hfix u hgap hp i).val.val+(deletedOrder n r p hfix u hgap hp j).val.val=r ∨
      (deletedOrder n r p hfix u hgap hp i).val.val+(deletedOrder n r p hfix u hgap hp j).val.val=p) :
    i.val+1=j.val ∨ j.val+1=i.val := by
  apply adjacent_after_delete (zeroCut n r p hfix u hgap hp) i j
  apply adjacent_of_pair n (0:Fin g) r p hfix u hgap
  · intro he
    have hh := congrArg (zeroCut n r p hfix u hgap hp).predAbove he
    simp only [Fin.predAbove_succAbove] at hh
    exact hne hh
  · exact h

#print axioms zeroCut
#print axioms order_zero_at
#print axioms deletedOrder
#print axioms deletedOrder_adjacent
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionFixedOrbit

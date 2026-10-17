import Results.Genus.CapFourMass.SignedReflectionPairedClosure

/-! Reverse edge semantics for the fixed nonzero reflection paths. A genuine
consecutive factor is proved arithmetically, not inferred from scalar Covers. -/
namespace SubmittedGenus.CapFourMass.SignedReflectionFixed
open RawGraph RawGraph.PackedAcceptance
open ReflectionCoset ReflectionConsecutive

lemma zigzag_pair_of_consecutive (m : ℕ) (i j : Fin (m+1)) (hij : i.val+1=j.val) :
    asResidue m (ReflectionZigzag.forward m i)+asResidue m (ReflectionZigzag.forward m j)=0 ∨
    asResidue m (ReflectionZigzag.forward m i)+asResidue m (ReflectionZigzag.forward m j)=1 := by
  rw [zigzag_cast,zigzag_cast]
  by_cases hi : i.val%2=0
  · have hj : j.val%2≠0 := by omega
    have hd : (j.val+1)/2=i.val/2+1 := by omega
    simp only [hi,ite_true,hj,ite_false,hd,Nat.cast_add,Nat.cast_one]
    right
    ring
  · have hj : j.val%2=0 := by omega
    have hd : (i.val+1)/2=j.val/2 := by omega
    simp only [hi,ite_false,hj,ite_true,hd]
    left
    ring

lemma consecutive_pair (m r : ℕ) (i j : Fin (m+1)) (hij : i.val+1=j.val) :
    asResidue m (ReflectionConsecutive.order m r i)+asResidue m (ReflectionConsecutive.order m r j)=
      (r:ZMod (m+1)) ∨
    asResidue m (ReflectionConsecutive.order m r i)+asResidue m (ReflectionConsecutive.order m r j)=
      ((r+1:ℕ):ZMod (m+1)) := by
  have hs:=zigzag_pair_of_consecutive m i j hij
  simp only [order_cast]
  by_cases hp:r%2=0
  · simp only [hp,ite_true]
    have hc : ((r/2:ℕ):ZMod (m+1))+((r/2:ℕ):ZMod (m+1))=(r:ZMod (m+1)) := by
      rw [←Nat.cast_add]
      congr 1
      omega
    rcases hs with hs|hs
    · left; linear_combination hs+hc
    · right; push_cast; linear_combination hs+hc
  · simp only [hp,ite_false]
    have hc : (((r+1)/2:ℕ):ZMod (m+1))+(((r+1)/2:ℕ):ZMod (m+1))=((r+1:ℕ):ZMod (m+1)) := by
      rw [←Nat.cast_add]
      congr 1
      omega
    rcases hs with hs|hs
    · right; linear_combination hc-hs
    · left; push_cast at hc; linear_combination hc-hs

lemma phase_pair_of_consecutive (n : ℕ) (t : ZMod (n+2)) (u : (ZMod (n+2))ˣ)
    (i j : Fin (n+2)) (hij : i.val+1=j.val) :
    ReflectionFixedOrbit.phaseOrder n t u i+ReflectionFixedOrbit.phaseOrder n t u j=t ∨
    ReflectionFixedOrbit.phaseOrder n t u i+ReflectionFixedOrbit.phaseOrder n t u j=t+(u:ZMod (n+2)) := by
  have hs:=consecutive_pair (n+1) (ReflectionFixedOrbit.normalizedTarget n t u).val i j hij
  simp only [ReflectionFixedOrbit.phaseOrder_apply]
  rw [←mul_add]
  rcases hs with hs|hs
  · left
    rw [hs,ReflectionFixedOrbit.normalizedTarget_value]
  · right
    rw [hs,ReflectionFixedOrbit.normalizedTarget_next]

variable {g : ℕ} [NeZero g]

/-- Every displayed fixed-path factor is one of the two original targets. -/
theorem pair_of_consecutive (n : ℕ) (a : Fin g) (r p : ZMod (g*(n+2)))
    (hfix : (r-affineValue a (0:ZMod (n+2))).val%g=a.val) (u : (ZMod (n+2))ˣ)
    (hgap : scaleHom g (n+2) (u:ZMod (n+2))=p-r)
    (i j : Fin (n+2)) (hij : i.val+1=j.val) :
    (ReflectionFixedOrbit.order n a r hfix u i).val+(ReflectionFixedOrbit.order n a r hfix u j).val=r ∨
    (ReflectionFixedOrbit.order n a r hfix u i).val+(ReflectionFixedOrbit.order n a r hfix u j).val=p := by
  rw [ReflectionFixedOrbit.order_val,ReflectionFixedOrbit.order_val]
  have hs:=phase_pair_of_consecutive n (ReflectionFixedOrbit.target n a r hfix) u i j hij
  have ht:=ReflectionFixedOrbit.target_value n a r hfix
  have hp : affineValue a (ReflectionFixedOrbit.target n a r hfix+(u:ZMod (n+2)))=
      p-affineValue a (0:ZMod (n+2)) := by
    rw [affineValue_add,ht,hgap]
    ring
  exact hs.imp ((affineValue_pair_iff a r _ _ _ ht).mpr)
    ((affineValue_pair_iff a p _ _ _ hp).mpr)

/-- Exact fixed-path incidence, including self-pair exclusion. -/
theorem adjacent_iff_pair (n : ℕ) (a : Fin g) (r p : ZMod (g*(n+2)))
    (hfix : (r-affineValue a (0:ZMod (n+2))).val%g=a.val) (u : (ZMod (n+2))ˣ)
    (hgap : scaleHom g (n+2) (u:ZMod (n+2))=p-r)
    (i j : Fin (n+2)) :
    (i.val+1=j.val ∨ j.val+1=i.val) ↔ i≠j ∧
      ((ReflectionFixedOrbit.order n a r hfix u i).val+(ReflectionFixedOrbit.order n a r hfix u j).val=r ∨
       (ReflectionFixedOrbit.order n a r hfix u i).val+(ReflectionFixedOrbit.order n a r hfix u j).val=p) := by
  constructor
  · intro h
    refine ⟨by intro he; subst j; omega,?_⟩
    rcases h with h|h
    · exact pair_of_consecutive n a r p hfix u hgap i j h
    · simpa only [add_comm] using pair_of_consecutive n a r p hfix u hgap j i h
  · rintro ⟨hne,h⟩
    exact ReflectionFixedOrbit.adjacent_of_pair n a r p hfix u hgap i j hne h

end SubmittedGenus.CapFourMass.SignedReflectionFixed

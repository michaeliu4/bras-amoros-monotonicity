import Results.Genus.RawGraph.PackedAcceptance.ReflectionComponentOrders

/-! Phase-aligned arithmetic coordinates of the original fixed-coset path.
The alignment is an index in the full source order: it does not reverse a path,
discard an endpoint, or identify endpoint unary masks with interior masks. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionFixedPhase
open ReflectionCoset ReflectionConsecutive ReflectionFixedOrbit

/-- The first r-pair starts after one head vertex exactly for even target. -/
def alignment (h : ℕ) : ℕ := 1-h%2

lemma alignment_le_one (h : ℕ) : alignment h≤1 := by unfold alignment;omega

lemma consecutive_sum (m h : ℕ) (i j : Fin (m+1)) (hij : i.val+1=j.val) :
    asResidue m (ReflectionConsecutive.order m h i)+
      asResidue m (ReflectionConsecutive.order m h j)=
      if i.val%2=h%2 then ((h+1:ℕ):ZMod (m+1)) else (h:ZMod (m+1)) := by
  have hs : asResidue m (ReflectionZigzag.forward m i)+
      asResidue m (ReflectionZigzag.forward m j)=
      if i.val%2=0 then 1 else 0 := by
    rw [zigzag_cast,zigzag_cast]
    by_cases hi : i.val%2=0
    · have hj : j.val%2≠0 := by omega
      have hd : (j.val+1)/2=i.val/2+1 := by omega
      simp only [hi,ite_true,hj,ite_false,hd,Nat.cast_add,Nat.cast_one]
      ring
    · have hj : j.val%2=0 := by omega
      have hd : (i.val+1)/2=j.val/2 := by omega
      simp only [hi,ite_false,hj,ite_true,hd]
      ring
  rw [order_cast,order_cast]
  by_cases hh : h%2=0
  · have hc : ((h/2:ℕ):ZMod (m+1))+((h/2:ℕ):ZMod (m+1))=(h:ZMod (m+1)) := by
      rw [←Nat.cast_add];congr 1;omega
    simp only [hh,ite_true] at *
    split_ifs at hs ⊢ <;> push_cast <;> linear_combination hs+hc
  · have hh1 : h%2=1 := by omega
    have hc : (((h+1)/2:ℕ):ZMod (m+1))+(((h+1)/2:ℕ):ZMod (m+1))=((h+1:ℕ):ZMod (m+1)) := by
      rw [←Nat.cast_add];congr 1;omega
    simp only [hh,ite_false]
    by_cases hi : i.val%2=0
    · have hi1 : i.val%2≠h%2 := by omega
      simp only [hi,ite_true] at hs
      simp only [hi1,ite_false]
      push_cast at hc
      linear_combination hc-hs
    · have hi1 : i.val%2=h%2 := by omega
      simp only [hi,ite_false] at hs
      simp only [hi1,ite_true]
      linear_combination hc-hs

/-- The first member of each aligned r-pair is a positive modular progression. -/
lemma order_aligned_even (m h k : ℕ) (i : Fin (m+1))
    (hi : i.val=alignment h+2*k) :
    asResidue m (ReflectionConsecutive.order m h i)=((h/2+1+k:ℕ):ZMod (m+1)) := by
  rw [order_cast,zigzag_cast]
  by_cases hh : h%2=0
  · have hp : i.val%2≠0 := by simp only [alignment,hh] at hi;omega
    have hd : (i.val+1)/2=k+1 := by simp only [alignment,hh] at hi;omega
    simp only [hh,ite_true,hp,ite_false,hd]
    push_cast;ring
  · have hp : i.val%2=0 := by have hm:=Nat.mod_lt h (by omega : 0<2);unfold alignment at hi;omega
    have hd : i.val/2=k := by unfold alignment at hi;omega
    have he : (h+1)/2=h/2+1 := by omega
    simp only [hh,ite_false,hp,ite_true,hd,he]
    push_cast;ring

/-- The second member is the reflection in the normalized target. -/
lemma order_aligned_odd (m h k : ℕ) (i : Fin (m+1))
    (hi : i.val=alignment h+2*k+1) :
    asResidue m (ReflectionConsecutive.order m h i)=
      (h:ZMod (m+1))-((h/2+1+k:ℕ):ZMod (m+1)) := by
  rw [order_cast,zigzag_cast]
  by_cases hh : h%2=0
  · have hp : i.val%2=0 := by unfold alignment at hi;omega
    have hd : i.val/2=k+1 := by unfold alignment at hi;omega
    have hc : ((h/2:ℕ):ZMod (m+1))+((h/2:ℕ):ZMod (m+1))=(h:ZMod (m+1)) := by
      rw [←Nat.cast_add];congr 1;omega
    simp only [hh,ite_true,hp,hd]
    push_cast
    linear_combination hc
  · have hp : i.val%2≠0 := by unfold alignment at hi;omega
    have hd : (i.val+1)/2=k+1 := by unfold alignment at hi;omega
    have he : (h+1)/2=h/2+1 := by omega
    have hc : ((h/2:ℕ):ZMod (m+1))+((h/2:ℕ):ZMod (m+1))+1=(h:ZMod (m+1)) := by
      have heNat : h/2+h/2+1=h := by omega
      simpa only [Nat.cast_add,Nat.cast_one] using congrArg (fun x:ℕ=>(x:ZMod (m+1))) heNat
    simp only [hh,ite_false,hp,hd,he]
    push_cast
    linear_combination hc

lemma phase_aligned_even (n : ℕ) (t : ZMod (n+2)) (u : (ZMod (n+2))ˣ)
    (k : ℕ) (i : Fin (n+2)) (hi : i.val=alignment (normalizedTarget n t u).val+2*k) :
    phaseOrder n t u i=(u:ZMod (n+2))*(((normalizedTarget n t u).val/2+1+k:ℕ):ZMod (n+2)) := by
  rw [phaseOrder_apply,order_aligned_even (n+1) _ k i hi]

lemma phase_aligned_odd (n : ℕ) (t : ZMod (n+2)) (u : (ZMod (n+2))ˣ)
    (k : ℕ) (i : Fin (n+2)) (hi : i.val=alignment (normalizedTarget n t u).val+2*k+1) :
    phaseOrder n t u i=t-(u:ZMod (n+2))*(((normalizedTarget n t u).val/2+1+k:ℕ):ZMod (n+2)) := by
  rw [phaseOrder_apply,order_aligned_odd (n+1) _ k i hi,mul_sub,normalizedTarget_value]

variable {g : ℕ} [NeZero g]

abbrev targetIndex (n r δ : ℕ) (a : Fin g) (hfix : a=ReflectionPairedOrbit.mate r a)
    (hc : Nat.Coprime δ (n+2)) : ℕ :=
  (normalizedTarget n (target n a r (ReflectionComponentOrders.fixed_origin n r a hfix))
    (ReflectionComponentOrders.gapUnit n δ hc)).val

/-- The shift is taken modulo the true translation-orbit length. -/
def startPhase (n δ h : ℕ) : ℕ := (δ*(h/2+1))%(n+2)

lemma aligned_coordinate (n δ h k : ℕ) :
    ((δ:ZMod (n+2))*((h/2+1+k:ℕ):ZMod (n+2))).val=
      (startPhase n δ h+δ*k)%(n+2) := by
  rw [←Nat.cast_mul,ZMod.val_natCast,Nat.mul_add]
  simp only [startPhase,Nat.add_mod,Nat.mod_mod]

/-- Exact original residue formula for aligned even source positions. -/
theorem source_even (n r δ : ℕ) (a : Fin g) (hfix : a=ReflectionPairedOrbit.mate r a)
    (hc : Nat.Coprime δ (n+2)) (k : ℕ) (i : Fin (n+2))
    (hi : i.val=alignment (targetIndex n r δ a hfix hc)+2*k) :
    ((order n a r (ReflectionComponentOrders.fixed_origin n r a hfix)
      (ReflectionComponentOrders.gapUnit n δ hc) i).val).val=
      a.val+g*((startPhase n δ (targetIndex n r δ a hfix hc)+δ*k)%(n+2)) := by
  rw [order_val,phase_aligned_even n _ _ k i hi,ZMod.coe_unitOfCoprime]
  have hv (x : ZMod (n+2)) : (affineValue a x).val=a.val+g*x.val := by
    rw [←affineEquiv_val]
    change (ReflectionCoset.embed a ((ZMod.finEquiv (n+2)).symm x)).val=_
    rw [ReflectionCoset.embed_val,finEquiv_symm_val]
  rw [hv,aligned_coordinate]

/-- Exact original reflected residue, retaining the full modulus and phase. -/
theorem source_odd (n r δ : ℕ) (a : Fin g) (hfix : a=ReflectionPairedOrbit.mate r a)
    (hc : Nat.Coprime δ (n+2)) (k : ℕ) (i : Fin (n+2))
    (hi : i.val=alignment (targetIndex n r δ a hfix hc)+2*k+1) :
    (order n a r (ReflectionComponentOrders.fixed_origin n r a hfix)
      (ReflectionComponentOrders.gapUnit n δ hc) i).val=
      (r:ZMod (g*(n+2)))-
        ((a.val+g*((startPhase n δ (targetIndex n r δ a hfix hc)+δ*k)%(n+2)):ℕ):ZMod (g*(n+2))) := by
  rw [order_val,phase_aligned_odd n _ _ k i hi]
  rw [affineValue_reflection a r _ _ (target_value n a r _)]
  congr 1
  rw [ZMod.coe_unitOfCoprime]
  conv_lhs => rw [←ZMod.natCast_zmod_val ((δ:ZMod (n+2))*_)]
  rw [affineValue_natCast,aligned_coordinate]

#print axioms source_even
#print axioms source_odd
#print axioms consecutive_sum
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionFixedPhase

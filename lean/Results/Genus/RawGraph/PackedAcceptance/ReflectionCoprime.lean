import Results.Genus.RawGraph.PackedAcceptance.ReflectionPath

/-! Complete computable physical layouts whenever the original pivot gap is
coprime to the multiplicity. The order is a unit-scaled adjacent-reflection
path, and the deletion adapter removes precisely the zero residue. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionCoprime
open LayoutCompiler SourceModel ReflectionConsecutive

/-- Multiplication by a unit is an explicit residue permutation. -/
def scale {m : ℕ} (u : (ZMod (m+1))ˣ) : ZMod (m+1) ≃ ZMod (m+1) where
  toFun := fun x=>(u:ZMod (m+1))*x
  invFun := fun x=>((u⁻¹:(ZMod (m+1))ˣ):ZMod (m+1))*x
  left_inv := by intro x; simp [←mul_assoc]
  right_inv := by intro x; simp [←mul_assoc]

abbrev order (n : ℕ) (k : Fin (n+1)) (u : (ZMod (n+2))ˣ) : Fin (n+2)≃Fin (n+2) :=
  (ReflectionConsecutive.order (n+1) k.val).trans (scale u)

lemma order_cast (n : ℕ) (k : Fin (n+1)) (u : (ZMod (n+2))ˣ) (j : Fin (n+2)) :
    asResidue (n+1) (order n k u j)=
      (u:ZMod (n+2))*asResidue (n+1) (ReflectionConsecutive.order (n+1) k.val j) := rfl

lemma order_zero (n : ℕ) (k : Fin (n+1)) (u : (ZMod (n+2))ˣ) :
    order n k u k.castSucc=0 := by
  apply (ZMod.finEquiv (n+2)).injective
  change asResidue (n+1) (order n k u k.castSucc)=0
  rw [order_cast]
  exact (congrArg (fun z : Fin (n+2)=>(u:ZMod (n+2))*asResidue (n+1) z)
    (ReflectionConsecutive.order_zero (n+1) k.castSucc)).trans (mul_zero _)

abbrev layout (n : ℕ) (k : Fin (n+1)) (u : (ZMod (n+2))ˣ) : Layout (n+2) :=
  ReflectionPath.layout (order n k u) k (order_zero n k u)

lemma covers (n r p a : ℕ) (k : Fin (n+1)) (u : (ZMod (n+2))ˣ)
    (hr : r<n+2) (hp : p<n+2)
    (hk : (u:ZMod (n+2))*(k.val:ZMod (n+2))=(r:ZMod (n+2)))
    (hk' : (u:ZMod (n+2))*((k.val+1:ℕ):ZMod (n+2))=(p:ZMod (n+2))) :
    Covers (layout n k u) r p a := by
  apply ReflectionPath.covers (order n k u) k (order_zero n k u) hr hp
  intro i j hne h
  apply ReflectionConsecutive.adjacent_of_pair (n+1) k.val (by omega) i j hne
  simp only [order_cast] at h
  rcases h with h|h
  · left
    apply u.isUnit.mul_left_cancel
    rw [mul_add,hk]
    exact h
  · right
    apply u.isUnit.mul_left_cancel
    rw [mul_add,hk']
    exact h

/-- Location of the zero residue in normalized adjacent-reflection coordinates. -/
def normalizedPivot (n r : ℕ) (u : (ZMod (n+2))ˣ) : ℕ :=
  (((u⁻¹:(ZMod (n+2))ˣ):ZMod (n+2))*(r:ZMod (n+2))).val

lemma normalizedPivot_value (n r : ℕ) (u : (ZMod (n+2))ˣ) :
    (u:ZMod (n+2))*(normalizedPivot n r u:ZMod (n+2))=(r:ZMod (n+2)) := by
  rw [normalizedPivot,ZMod.natCast_zmod_val]
  simp [←mul_assoc]

lemma normalizedPivot_next (n r : ℕ) (u : (ZMod (n+2))ˣ) :
    (u:ZMod (n+2))*((normalizedPivot n r u+1:ℕ):ZMod (n+2))=
      (r:ZMod (n+2))+(u:ZMod (n+2)) := by
  rw [Nat.cast_add,Nat.cast_one,mul_add,mul_one,normalizedPivot_value]

lemma normalizedPivot_lt (n r p : ℕ) (u : (ZMod (n+2))ˣ)
    (hgap : (u:ZMod (n+2))=((p-r:ℕ):ZMod (n+2)))
    (hrp : r≤p) (hppos : 0<p) (hp : p<n+2) : normalizedPivot n r u<n+1 := by
  have hv : normalizedPivot n r u<n+2 := ZMod.val_lt _
  have hn : (u:ZMod (n+2))*((normalizedPivot n r u+1:ℕ):ZMod (n+2))=(p:ZMod (n+2)) := by
    rw [normalizedPivot_next,hgap,Nat.cast_sub hrp]
    ring
  by_contra h
  have he : normalizedPivot n r u=n+1 := by omega
  have hz : (p:ZMod (n+2))=0 := by
    rw [he] at hn
    have hh : (((n+1)+1:ℕ):ZMod (n+2))=0 := by
      change ((n+2:ℕ):ZMod (n+2))=0
      exact ZMod.natCast_self _
    rw [hh,mul_zero] at hn
    exact hn.symm
  have hzv := congrArg ZMod.val hz
  rw [ZMod.val_natCast,Nat.mod_eq_of_lt hp,ZMod.val_zero] at hzv
  omega

abbrev gapUnit (n r p : ℕ) (hcop : Nat.Coprime (p-r) (n+2)) : (ZMod (n+2))ˣ :=
  ZMod.unitOfCoprime (p-r) hcop

def cut (n r p : ℕ) (hcop : Nat.Coprime (p-r) (n+2))
    (hrp : r≤p) (hppos : 0<p) (hp : p<n+2) : Fin (n+1) :=
  ⟨normalizedPivot n r (gapUnit n r p hcop),
    normalizedPivot_lt n r p (gapUnit n r p hcop) rfl hrp hppos hp⟩

/-- Uniform source-correct family for all coprime original pivot gaps. -/
abbrev coprimeLayout (n r p : ℕ) (hcop : Nat.Coprime (p-r) (n+2))
    (hrp : r≤p) (hppos : 0<p) (hp : p<n+2) : Layout (n+2) :=
  layout n (cut n r p hcop hrp hppos hp) (gapUnit n r p hcop)

theorem coprime_covers (n r p a : ℕ) (hcop : Nat.Coprime (p-r) (n+2))
    (hrp : r≤p) (hppos : 0<p) (hp : p<n+2) :
    Covers (coprimeLayout n r p hcop hrp hppos hp) r p a := by
  apply covers n r p a (cut n r p hcop hrp hppos hp) (gapUnit n r p hcop)
    (by omega) hp
  · exact normalizedPivot_value n r (gapUnit n r p hcop)
  · change (gapUnit n r p hcop:ZMod (n+2))*
      ((normalizedPivot n r (gapUnit n r p hcop)+1:ℕ):ZMod (n+2))=(p:ZMod (n+2))
    rw [normalizedPivot_next,ZMod.coe_unitOfCoprime,Nat.cast_sub hrp]
    ring

#print axioms order_zero
#print axioms covers
#print axioms normalizedPivot_lt
#print axioms coprime_covers
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionCoprime

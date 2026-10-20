import Results.Genus.RawGraph.PackedAcceptance.ModularReflection

/-! Executable quotient/remainder coordinates on one translation coset.
This does not choose or enumerate components; it supplies their exact finite
physical residue coordinates for the full two-reflection construction. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionCoset

variable {g L : ℕ} [NeZero g] [NeZero L]

abbrev Coset (g L : ℕ) (a : Fin g) := {x : ZMod (g*L) // x.val%g=a.val}

lemma coordinate_lt (a : Fin g) (k : Fin L) : a.val+g*k.val<g*L := by
  have ha := a.isLt
  have hg := NeZero.pos g
  have hk := Nat.mul_le_mul_left g (Nat.succ_le_of_lt k.isLt)
  rw [Nat.mul_succ] at hk
  omega

/-- Natural coordinates before coercion to the original residue ring. -/
def embed (a : Fin g) (k : Fin L) : ZMod (g*L) := ((a.val+g*k.val:ℕ):ZMod (g*L))

lemma embed_val (a : Fin g) (k : Fin L) : (embed a k).val=a.val+g*k.val := by
  rw [embed,ZMod.val_natCast,Nat.mod_eq_of_lt (coordinate_lt a k)]

lemma embed_mod (a : Fin g) (k : Fin L) : (embed a k).val%g=a.val := by
  rw [embed_val,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt a.isLt]

lemma embed_injective (a : Fin g) : Function.Injective (embed (L:=L) a) := by
  intro i j h
  have hh := congrArg ZMod.val h
  rw [embed_val,embed_val] at hh
  apply Fin.ext
  exact Nat.eq_of_mul_eq_mul_left (NeZero.pos g) (Nat.add_left_cancel hh)

/-- Complete executable residue-class bijection, inverse given by quotient. -/
def equiv (a : Fin g) : Fin L ≃ Coset g L a where
  toFun := fun k=>⟨embed a k,embed_mod a k⟩
  invFun := fun x=>⟨x.val.val/g,by
    rw [Nat.div_lt_iff_lt_mul (NeZero.pos g)]
    simpa [Nat.mul_comm] using ZMod.val_lt x.val⟩
  left_inv := by
    intro k
    apply Fin.ext
    change (embed a k).val/g=k.val
    rw [embed_val,Nat.add_mul_div_left _ _ (NeZero.pos g),Nat.div_eq_of_lt a.isLt,zero_add]
  right_inv := by
    intro x
    apply Subtype.ext
    change embed a ⟨x.val.val/g,_⟩=x.val
    have hh : a.val+g*(x.val.val/g)=x.val.val := by
      exact (congrArg (fun z=>z+g*(x.val.val/g)) x.property.symm).trans (Nat.mod_add_div _ _)
    dsimp only [embed]
    rw [hh]
    exact ZMod.natCast_zmod_val x.val

lemma equiv_apply_val (a : Fin g) (k : Fin L) : ((equiv a k).val).val=a.val+g*k.val :=
  embed_val a k

lemma equiv_symm_val (a : Fin g) (x : Coset g L a) : ((equiv a).symm x).val = x.val.val/g := rfl

#print axioms embed_val
#print axioms embed_mod
#print axioms embed_injective
#print axioms equiv
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionCoset

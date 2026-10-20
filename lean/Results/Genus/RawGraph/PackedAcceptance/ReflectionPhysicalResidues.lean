import Results.Genus.RawGraph.PackedAcceptance.ModularReflection

namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionPhysicalResidues
open SourceModel

variable {M : ℕ} [NeZero M]

lemma physical_lt (v : Fin (M-1)) : physical v<M := by
  have hv := v.isLt
  dsimp [physical]
  omega

lemma physical_pos (v : Fin (M-1)) : 0<physical v := by
  dsimp [physical]
  omega

lemma nonzero_val_pos (x : ZMod M) (hx : x≠0) : 0<x.val := by
  by_contra h
  have hz : x.val=0 := by omega
  have he := ZMod.natCast_zmod_val x
  rw [hz,Nat.cast_zero] at he
  exact hx he.symm

/-- The actual one-based physical residue, with precisely zero excluded. -/
def equiv (M : ℕ) [NeZero M] : Fin (M-1) ≃ {x : ZMod M // x≠0} where
  toFun v := ⟨(physical v:ZMod M),by
    intro h
    have hh := congrArg ZMod.val h
    rw [ZMod.val_natCast,Nat.mod_eq_of_lt (physical_lt v),ZMod.val_zero] at hh
    exact (Nat.ne_of_gt (physical_pos v)) hh⟩
  invFun x := ⟨x.val.val-1,by
    have hl := ZMod.val_lt x.val
    have hp := nonzero_val_pos x.val x.property
    omega⟩
  left_inv v := by
    apply Fin.ext
    change ((physical v:ZMod M)).val-1=v.val
    rw [ZMod.val_natCast,Nat.mod_eq_of_lt (physical_lt v)]
    rfl
  right_inv x := by
    apply Subtype.ext
    have hp := nonzero_val_pos x.val x.property
    change (((x.val.val-1)+1:ℕ):ZMod M)=x.val
    rw [Nat.sub_add_cancel hp]
    exact ZMod.natCast_zmod_val x.val

lemma equiv_value (v : Fin (M-1)) : (equiv M v).val=(physical v:ZMod M) := rfl
lemma equiv_val (v : Fin (M-1)) : (equiv M v).val.val=physical v := by
  rw [equiv_value,ZMod.val_natCast,Nat.mod_eq_of_lt (physical_lt v)]

lemma equiv_symm_physical (x : {z : ZMod M // z≠0}) : physical ((equiv M).symm x)=x.val.val := by
  change (x.val.val-1)+1=x.val.val
  exact Nat.sub_add_cancel (nonzero_val_pos x.val x.property)

lemma equiv_symm_cast (x : {z : ZMod M // z≠0}) : (physical ((equiv M).symm x):ZMod M)=x.val := by
  rw [equiv_symm_physical,ZMod.natCast_zmod_val]

#print axioms equiv
#print axioms equiv_symm_cast
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionPhysicalResidues

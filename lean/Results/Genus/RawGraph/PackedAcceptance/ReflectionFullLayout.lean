import Results.Genus.RawGraph.PackedAcceptance.ReflectionComponentOrders
import Results.Genus.RawGraph.PackedAcceptance.ReflectionPhysicalResidues
import Results.Genus.RawGraph.PackedAcceptance.ReflectionComponentCompiler
import Results.Genus.RawGraph.PackedAcceptance.InvolutionPartition.Index

/-! Complete executable reflection layouts in factored multiplicity coordinates.
Component representatives are computed by filtered finite enumeration, while
every component's actual residue labels come from the four proved orbit orders. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionFullLayout
open LayoutCompiler SourceModel
open ReflectionPairedOrbit (mate)

variable {g : ℕ} [NeZero g]

abbrev involution (r : ℕ) : Fin g→Fin g := mate r
lemma involutive (r : ℕ) : Function.Involutive (involution (g:=g) r) :=
  ReflectionPairedOrbit.partner_involutive g r (NeZero.pos g)
abbrev count (r : ℕ) : ℕ := InvolutionPartition.count (involution (g:=g) r)
abbrev representative (r : ℕ) (c : Fin (count (g:=g) r)) : Fin g := InvolutionPartition.representative (involution r) c
lemma representative_le (r : ℕ) (c : Fin (count (g:=g) r)) :
    representative r c≤mate r (representative r c) := InvolutionPartition.representative_le_mate (involution r) c

def residueClass (n : ℕ) (v : Fin (g*(n+2)-1)) : Fin g :=
  ⟨physical v%g,Nat.mod_lt _ (NeZero.pos g)⟩

def owner (n r : ℕ) (v : Fin (g*(n+2)-1)) : Fin (count (g:=g) r) :=
  InvolutionPartition.repIndex (involution r) (involutive r) (residueClass n v)

lemma owner_eq_iff (n r : ℕ) (v : Fin (g*(n+2)-1)) (c : Fin (count (g:=g) r)) :
    owner n r v=c ↔ physical v%g=(representative r c).val ∨
      physical v%g=(mate r (representative r c)).val := by
  rw [owner,InvolutionPartition.repIndex_eq_iff]
  constructor
  · rintro (h|h)
    · exact Or.inl (congrArg Fin.val h)
    · exact Or.inr (congrArg Fin.val h)
  · rintro (h|h)
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)

/-- Exact conversion from a nonzero residue component to its physical owner
fiber; no ordering or label is chosen in this adapter. -/
def blockEquiv (n r : ℕ) (c : Fin (count (g:=g) r)) :
    ReflectionComponentOrders.Block n r (representative r c) ≃ {v : Fin (g*(n+2)-1) // owner n r v=c} where
  toFun x := ⟨(ReflectionPhysicalResidues.equiv (g*(n+2))).symm ⟨x.val,x.property.2⟩,by
    apply (owner_eq_iff n r _ c).mpr
    rw [ReflectionPhysicalResidues.equiv_symm_physical]
    exact x.property.1⟩
  invFun v := ⟨(ReflectionPhysicalResidues.equiv (g*(n+2)) v.val).val,⟨by
    rw [ReflectionPhysicalResidues.equiv_val]
    exact (owner_eq_iff n r v.val c).mp v.property,
    (ReflectionPhysicalResidues.equiv (g*(n+2)) v.val).property⟩⟩
  left_inv x := by
    apply Subtype.ext
    exact congrArg (fun z : {x : ZMod (g*(n+2)) // x≠0} => z.val)
      ((ReflectionPhysicalResidues.equiv (g*(n+2))).apply_symm_apply ⟨x.val,x.property.2⟩)
  right_inv v := by
    apply Subtype.ext
    exact (ReflectionPhysicalResidues.equiv (g*(n+2))).symm_apply_apply v.val

lemma blockEquiv_cast (n r : ℕ) (c : Fin (count (g:=g) r)) (x : ReflectionComponentOrders.Block n r (representative r c)) :
    (physical (blockEquiv n r c x).val:ZMod (g*(n+2)))=x.val :=
  ReflectionPhysicalResidues.equiv_symm_cast ⟨x.val,x.property.2⟩

abbrev componentData (n r p δ : ℕ) (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ)
    (hp0 : 0<p) (hpm : p<g*(n+2)) (c : Fin (count (g:=g) r)) :=
  ReflectionComponentOrders.component n r p δ hc hp hp0 hpm (representative r c) (representative_le r c)

def fiberEquiv (n r p δ : ℕ) (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ)
    (hp0 : 0<p) (hpm : p<g*(n+2)) (c : Fin (count (g:=g) r)) :
    Fin (componentData n r p δ hc hp hp0 hpm c).size ≃
      {v : Fin (g*(n+2)-1) // owner n r v=c} :=
  (componentData n r p δ hc hp hp0 hpm c).equiv.trans (blockEquiv n r c)

lemma fiberEquiv_cast (n r p δ : ℕ) (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ)
    (hp0 : 0<p) (hpm : p<g*(n+2)) (c : Fin (count (g:=g) r))
    (i : Fin (componentData n r p δ hc hp hp0 hpm c).size) :
    (physical (fiberEquiv n r p δ hc hp hp0 hpm c i).val:ZMod (g*(n+2)))=
      ((componentData n r p δ hc hp hp0 hpm c).equiv i).val :=
  blockEquiv_cast n r c _

abbrev layout (n r p δ : ℕ) (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ)
    (hp0 : 0<p) (hpm : p<g*(n+2)) : Layout (g*(n+2)) :=
  ReflectionComponentCompiler.layout (owner n r) (fun c=>(componentData n r p δ hc hp hp0 hpm c).size)
    (fun c=>(componentData n r p δ hc hp hp0 hpm c).size_pos)
    (fiberEquiv n r p δ hc hp hp0 hpm) (fun c=>(componentData n r p δ hc hp hp0 hpm c).cycle)

lemma positive_pair {M r p a : ℕ} (u v : Fin (M-1)) (hb : 0<edgeBound r p a u v) :
    TargetPair r u v ∨ TargetPair p u v := by
  unfold edgeBound at hb
  split_ifs at hb with h0 hs hc
  · omega
  · rcases hs with hs|hs
    · exact Or.inl (Or.inl hs)
    · exact Or.inr (Or.inl hs)
  · rcases hc with hc|hc
    · exact Or.inl (Or.inr hc)
    · exact Or.inr (Or.inr hc)
  · omega

lemma positive_ne {M r p a : ℕ} (u v : Fin (M-1)) (hb : 0<edgeBound r p a u v) : u≠v := by
  intro h
  subst v
  simp [edgeBound] at hb

lemma residueClass_pair (n t : ℕ) (ht : t<g*(n+2)) (u v : Fin (g*(n+2)-1))
    (h : TargetPair t u v) : residueClass n v=mate t (residueClass n u) := by
  have he := (targetPair_iff_modularReflect ht u v).mp h
  change (physical v:ZMod (g*(n+2)))=(t:ZMod (g*(n+2)))-(physical u:ZMod (g*(n+2))) at he
  have hu : ((physical u:ZMod (g*(n+2)))).val%g=(residueClass n u).val := by
    rw [ZMod.val_natCast,Nat.mod_eq_of_lt (ReflectionPhysicalResidues.physical_lt u)]
    rfl
  have hh := ReflectionPairedOrbit.reflect_coset g (n+2) t (NeZero.pos g) (by omega)
    (residueClass n u) (physical u:ZMod (g*(n+2))) hu
  rw [←he,ZMod.val_natCast,Nat.mod_eq_of_lt (ReflectionPhysicalResidues.physical_lt v)] at hh
  exact Fin.ext hh

lemma mate_gap (r p δ : ℕ) (hp : p=r+g*δ) (a : Fin g) : mate p a=mate r a := by
  apply Fin.ext
  change ((p:ZMod g)-(a.val:ZMod g)).val=((r:ZMod g)-(a.val:ZMod g)).val
  rw [hp,Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,zero_mul,add_zero]

lemma same_owner (n r p δ a : ℕ) (hp : p=r+g*δ) (hpm : p<g*(n+2))
    (u v : Fin (g*(n+2)-1)) (hb : 0<edgeBound r p a u v) : owner n r u=owner n r v := by
  have hr : r<g*(n+2) := by omega
  have hclass : residueClass n v=mate r (residueClass n u) := by
    rcases positive_pair u v hb with h|h
    · exact residueClass_pair n r hr u v h
    · exact (residueClass_pair n p hpm u v h).trans (mate_gap r p δ hp _)
  unfold owner
  rw [hclass,InvolutionPartition.repIndex_mate]

/-- The complete original positive-edge graph is covered, for every source
cap, by the computed finite family. No final coverage predicate is assumed. -/
theorem covers (n r p δ a : ℕ) (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ)
    (hp0 : 0<p) (hpm : p<g*(n+2)) : Covers (layout n r p δ hc hp hp0 hpm) r p a := by
  apply ReflectionComponentCompiler.covers (owner n r) (fun c=>(componentData n r p δ hc hp hp0 hpm c).size)
    (fun c=>(componentData n r p δ hc hp hp0 hpm c).size_pos)
    (fiberEquiv n r p δ hc hp hp0 hpm) (fun c=>(componentData n r p δ hc hp hp0 hpm c).cycle)
    r p a (same_owner n r p δ a hp hpm)
  intro c u v hb
  let e := fiberEquiv n r p δ hc hp hp0 hpm c
  let i := e.symm u
  let j := e.symm v
  have hi : (e i).val=u.val := congrArg Subtype.val (e.apply_symm_apply u)
  have hj : (e j).val=v.val := congrArg Subtype.val (e.apply_symm_apply v)
  have hcastu : ((componentData n r p δ hc hp hp0 hpm c).equiv i).val=(physical u.val:ZMod (g*(n+2))) :=
    (fiberEquiv_cast n r p δ hc hp hp0 hpm c i).symm.trans
      (congrArg (fun x=>(physical x:ZMod (g*(n+2)))) hi)
  have hcastv : ((componentData n r p δ hc hp hp0 hpm c).equiv j).val=(physical v.val:ZMod (g*(n+2))) :=
    (fiberEquiv_cast n r p δ hc hp hp0 hpm c j).symm.trans
      (congrArg (fun x=>(physical x:ZMod (g*(n+2)))) hj)
  apply (componentData n r p δ hc hp hp0 hpm c).adjacent i j
  · intro he
    exact positive_ne u.val v.val hb (congrArg Subtype.val (e.symm.injective he))
  · rcases positive_pair u.val v.val hb with h|h
    · left
      exact (congrArg₂ (·+·) hcastu hcastv).trans
        ((targetPair_iff_zmod (by omega : r<g*(n+2)) u.val v.val).mp h)
    · right
      exact (congrArg₂ (·+·) hcastu hcastv).trans
        ((targetPair_iff_zmod hpm u.val v.val).mp h)

#print axioms blockEquiv
#print axioms same_owner
#print axioms covers
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionFullLayout

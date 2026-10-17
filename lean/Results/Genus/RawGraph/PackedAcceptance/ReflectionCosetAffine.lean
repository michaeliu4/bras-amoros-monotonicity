import Results.Genus.RawGraph.PackedAcceptance.ReflectionCoset
import Results.Genus.RawGraph.PackedAcceptance.ReflectionConsecutive

namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionCoset

variable {g L : ℕ} [NeZero g] [NeZero L]

/-- The additive inclusion of the length-L translation group into residues
modulo g*L, implemented using the canonical natural representative. -/
def scaleValue (g L : ℕ) (x : ZMod L) : ZMod (g*L) := ((g*x.val:ℕ):ZMod (g*L))

lemma scaleValue_natCast (k : ℕ) : scaleValue g L (k:ZMod L)=((g*k:ℕ):ZMod (g*L)) := by
  unfold scaleValue
  rw [ZMod.val_natCast]
  have he := congrArg (fun t:ℕ=>((g*t:ℕ):ZMod (g*L))) (Nat.mod_add_div k L)
  have hz : (g:ZMod (g*L))*(L:ZMod (g*L))=0 := by
    rw [←Nat.cast_mul,ZMod.natCast_self]
  push_cast at he ⊢
  rw [mul_add,←mul_assoc,hz,zero_mul,add_zero] at he
  exact he

lemma scaleValue_add (x y : ZMod L) : scaleValue g L (x+y)=scaleValue g L x+scaleValue g L y := by
  conv_lhs => rw [←ZMod.natCast_zmod_val x,←ZMod.natCast_zmod_val y,←Nat.cast_add]
  rw [scaleValue_natCast]
  dsimp only [scaleValue]
  push_cast
  ring

def scaleHom (g L : ℕ) [NeZero g] [NeZero L] : ZMod L →+ ZMod (g*L) where
  toFun := scaleValue g L
  map_zero' := by simp [scaleValue]
  map_add' := scaleValue_add

lemma scaleHom_natCast (k : ℕ) : scaleHom g L (k:ZMod L)=((g*k:ℕ):ZMod (g*L)) :=
  scaleValue_natCast k

lemma scaleHom_val (x : ZMod L) : (scaleHom g L x).val=g*x.val := by
  change (((g*x.val:ℕ):ZMod (g*L))).val=g*x.val
  rw [ZMod.val_natCast,Nat.mod_eq_of_lt]
  exact Nat.mul_lt_mul_of_pos_left (ZMod.val_lt x) (NeZero.pos g)

lemma scaleHom_injective : Function.Injective (scaleHom g L) := by
  intro x y h
  have hv := congrArg ZMod.val h
  rw [scaleHom_val,scaleHom_val] at hv
  have hv' := Nat.eq_of_mul_eq_mul_left (NeZero.pos g) hv
  exact (ZMod.natCast_zmod_val x).symm.trans
    ((congrArg (fun t:ℕ=>(t:ZMod L)) hv').trans (ZMod.natCast_zmod_val y))

/-- Affine coordinates on an arbitrary translation coset. -/
def affineValue (a : Fin g) (x : ZMod L) : ZMod (g*L) := (a.val:ZMod (g*L))+scaleHom g L x

lemma affineValue_natCast (a : Fin g) (k : ℕ) :
    affineValue a (k:ZMod L)=((a.val+g*k:ℕ):ZMod (g*L)) := by
  rw [affineValue,scaleHom_natCast,Nat.cast_add]

lemma affineValue_add (a : Fin g) (x y : ZMod L) :
    affineValue a (x+y)=affineValue a x+scaleHom g L y := by
  simp [affineValue,map_add,add_assoc]

lemma affineValue_sub (a : Fin g) (x y : ZMod L) :
    affineValue a (x-y)=affineValue a x-scaleHom g L y := by
  simp [affineValue,map_sub,add_sub_assoc]

lemma affineValue_injective (a : Fin g) : Function.Injective (affineValue (L:=L) a) := by
  intro x y h
  exact scaleHom_injective (add_left_cancel h)

/-- A reflected coset is internally another affine reflection. Its target
is determined exactly by the image of its origin. -/
lemma affineValue_reflection (a : Fin g) (r : ZMod (g*L)) (t x : ZMod L)
    (ht : affineValue a t=r-affineValue a 0) :
    affineValue a (t-x)=r-affineValue a x := by
  rw [affineValue_sub,ht]
  simp [affineValue,map_zero]
  ring

lemma finEquiv_symm_val (x : ZMod L) : ((ZMod.finEquiv L).symm x).val=x.val := by
  cases L with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rfl

/-- The same coset bijection with its source written as the residue group. -/
def affineEquiv (a : Fin g) : ZMod L ≃ Coset g L a :=
  (ZMod.finEquiv L).symm.toEquiv.trans (equiv a)

lemma affineEquiv_val (a : Fin g) (x : ZMod L) : (affineEquiv a x).val=affineValue a x := by
  have he := affineValue_natCast (L:=L) a x.val
  rw [ZMod.natCast_zmod_val] at he
  change embed a ((ZMod.finEquiv L).symm x)=affineValue a x
  unfold embed
  rw [finEquiv_symm_val]
  exact he.symm

lemma affineValue_pair_iff (a : Fin g) (r : ZMod (g*L)) (t x y : ZMod L)
    (ht : affineValue a t=r-affineValue a 0) :
    affineValue a x+affineValue a y=r ↔ x+y=t := by
  constructor
  · intro h
    have he : affineValue a x=r-affineValue a y := eq_sub_iff_add_eq.mpr h
    have hx : x=t-y := affineValue_injective a
      (he.trans (affineValue_reflection a r t y ht).symm)
    exact eq_sub_iff_add_eq.mp hx
  · intro h
    have hx : x=t-y := eq_sub_iff_add_eq.mpr h
    rw [hx,affineValue_reflection a r t y ht,sub_add_cancel]

#print axioms affineEquiv
#print axioms affineEquiv_val
#print axioms affineValue_pair_iff
#print axioms scaleValue_natCast
#print axioms scaleHom_injective
#print axioms affineValue_reflection
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionCoset

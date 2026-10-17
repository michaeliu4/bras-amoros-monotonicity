import Results.Genus.CapFourMass.SignedReflectionPairedClosure

/-! Explicit free physical coordinates for a residue block after zero and
both original pivots are removed. This adapter also applies to the zero block. -/
namespace SubmittedGenus.CapFourMass.SignedReflectionFreeBlock
open RawGraph RawGraph.SourceModel RawGraph.Topology RawGraph.PackedAcceptance
open ReflectionPairedOrbit ReflectionFullLayout SignedReflectionPaired

variable {g : ℕ} [NeZero g]

def Keep (n r p : ℕ) {a : Fin g} (x : PairedCosets (L:=n+2) r a) : Prop :=
  x.val≠0 ∧ x.val≠(r:ZMod (g*(n+2))) ∧ x.val≠(p:ZMod (g*(n+2)))

abbrev FreeResidue (n r p : ℕ) (a : Fin g) := {x : PairedCosets (L:=n+2) r a // Keep n r p x}

lemma val_pos (n r p : ℕ) (a : Fin g) (x : FreeResidue n r p a) : 0<x.val.val.val := by
  apply Nat.pos_of_ne_zero
  intro he
  apply x.property.1
  rw [←ZMod.natCast_zmod_val x.val.val,he,Nat.cast_zero]

def vertex (n r p : ℕ) (a : Fin g) (x : FreeResidue n r p a) : FreeVertex (g*(n+2)) r p := by
  have hpos:=val_pos n r p a x
  have hlt:=ZMod.val_lt x.val.val
  have hxr : x.val.val.val≠r := by
    intro he
    apply x.property.2.1
    rw [←ZMod.natCast_zmod_val x.val.val,he]
  have hxp : x.val.val.val≠p := by
    intro he
    apply x.property.2.2
    rw [←ZMod.natCast_zmod_val x.val.val,he]
  refine ⟨⟨x.val.val.val-1,by omega⟩,?_⟩
  unfold IsFree IsPivot
  dsimp only [physical]
  omega

@[simp] lemma physical_vertex (n r p : ℕ) (a : Fin g) (x : FreeResidue n r p a) :
    physical (vertex n r p a x).val=x.val.val.val := by
  change x.val.val.val-1+1=x.val.val.val
  have :=val_pos n r p a x
  omega

@[simp] lemma cast_physical_vertex (n r p : ℕ) (a : Fin g) (x : FreeResidue n r p a) :
    (physical (vertex n r p a x).val:ZMod (g*(n+2)))=x.val.val := by
  rw [physical_vertex,ZMod.natCast_zmod_val]

theorem vertex_injective (n r p : ℕ) (a : Fin g) : Function.Injective (vertex n r p a) := by
  intro x y he
  have hv:=congrArg (fun v : FreeVertex (g*(n+2)) r p=>
    (physical v.val:ZMod (g*(n+2)))) he
  simp only [cast_physical_vertex] at hv
  exact Subtype.ext (Subtype.ext hv)

lemma vertex_inBlock (n r p : ℕ) (a : Fin g) (x : FreeResidue n r p a) :
    InBlock n r p a (vertex n r p a x) := by
  rcases x.val.property with hx|hx
  · exact Or.inl (Fin.ext (by change physical (vertex n r p a x).val%g=a.val; rwa [physical_vertex]))
  · exact Or.inr (Fin.ext (by change physical (vertex n r p a x).val%g=(mate r a).val; rwa [physical_vertex]))

/-- Exact residue-to-free-vertex bijection after all three forbidden values
are excluded. The original r,p bounds justify the inverse's exclusion tests. -/
def equiv (n r p : ℕ) (hrm : r<g*(n+2)) (hpm : p<g*(n+2)) (a : Fin g) :
    FreeResidue n r p a ≃ {v : FreeVertex (g*(n+2)) r p // InBlock n r p a v} where
  toFun x := ⟨vertex n r p a x,vertex_inBlock n r p a x⟩
  invFun v := by
    have hv : physical v.val.val<g*(n+2) := by have:=v.val.val.isLt; dsimp [physical]; omega
    have hz : 0<physical v.val.val := by dsimp [physical]; omega
    let x : PairedCosets (L:=n+2) r a := ⟨(physical v.val.val:ZMod (g*(n+2))),by
      rw [ZMod.val_natCast,Nat.mod_eq_of_lt hv]
      exact v.property.elim (fun h=>Or.inl (congrArg Fin.val h))
        (fun h=>Or.inr (congrArg Fin.val h))⟩
    refine ⟨x,?_,?_,?_⟩
    · intro he
      have hh:=congrArg ZMod.val he
      change (physical v.val.val:ZMod (g*(n+2))).val=(0:ZMod (g*(n+2))).val at hh
      rw [ZMod.val_natCast,Nat.mod_eq_of_lt hv,ZMod.val_zero] at hh
      omega
    · intro he
      have hh:=congrArg ZMod.val he
      change (physical v.val.val:ZMod (g*(n+2))).val=(r:ZMod (g*(n+2))).val at hh
      rw [ZMod.val_natCast,ZMod.val_natCast,Nat.mod_eq_of_lt hv,Nat.mod_eq_of_lt hrm] at hh
      exact v.val.property (Or.inl hh)
    · intro he
      have hh:=congrArg ZMod.val he
      change (physical v.val.val:ZMod (g*(n+2))).val=(p:ZMod (g*(n+2))).val at hh
      rw [ZMod.val_natCast,ZMod.val_natCast,Nat.mod_eq_of_lt hv,Nat.mod_eq_of_lt hpm] at hh
      exact v.val.property (Or.inr hh)
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact cast_physical_vertex n r p a x
  right_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    apply Fin.ext
    have hv : physical v.val.val<g*(n+2) := by have:=v.val.val.isLt; dsimp [physical]; omega
    change ((physical v.val.val:ZMod (g*(n+2))).val)-1=v.val.val
    rw [ZMod.val_natCast,Nat.mod_eq_of_lt hv]
    rfl

theorem vertex_adjacent_iff (n r p : ℕ) (hrm : r<g*(n+2)) (hpm : p<g*(n+2))
    (a : Fin g) (x y : FreeResidue n r p a) :
    (freeGraph (g*(n+2)) r p).Adj (vertex n r p a x) (vertex n r p a y) ↔
      x≠y ∧ (x.val.val+y.val.val=(r:ZMod (g*(n+2))) ∨ x.val.val+y.val.val=(p:ZMod (g*(n+2)))) := by
  change ((vertex n r p a x).val≠(vertex n r p a y).val ∧
    IsFree r p (vertex n r p a x).val ∧ IsFree r p (vertex n r p a y).val ∧
    (TargetPair r (vertex n r p a x).val (vertex n r p a y).val ∨
     TargetPair p (vertex n r p a x).val (vertex n r p a y).val)) ↔ _
  rw [targetPair_iff_zmod hrm,targetPair_iff_zmod hpm]
  simp only [cast_physical_vertex,(vertex n r p a x).property,(vertex n r p a y).property,true_and]
  have hinj : Function.Injective (fun z=> (vertex n r p a z).val) :=
    Subtype.val_injective.comp (vertex_injective n r p a)
  exact and_congr (not_congr hinj.eq_iff) Iff.rfl

end SubmittedGenus.CapFourMass.SignedReflectionFreeBlock

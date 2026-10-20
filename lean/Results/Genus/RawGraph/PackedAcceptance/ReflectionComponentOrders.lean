import Results.Genus.RawGraph.PackedAcceptance.ReflectionFixedDelete
import Results.Genus.RawGraph.PackedAcceptance.ReflectionPairedOrbit

/-! The four explicit original-residue component orders: fixed path, paired
cycle, and the respective paths obtained by deleting the unique zero residue. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionComponentOrders
open ReflectionCoset
open ReflectionPairedOrbit (mate)

variable {g : ℕ} [NeZero g]

abbrev Block (n r : ℕ) (a : Fin g) :=
  {x : ZMod (g*(n+2)) // (x.val%g=a.val ∨ x.val%g=(mate r a).val) ∧ x≠0}

def size (n r : ℕ) (a : Fin g) : ℕ :=
  if a=mate r a then (if a=0 then n+1 else n+2)
  else if a=0 then 2*(n+2)-1 else 2*(n+2)

def cycle (r : ℕ) (a : Fin g) : Bool :=
  if a=mate r a then false else if a=0 then false else true

lemma size_pos (n r : ℕ) (a : Fin g) : 0<size n r a := by
  unfold size
  split_ifs <;> omega

lemma fixed_origin (n r : ℕ) (a : Fin g) (ha : a=mate r a) :
    ((r:ZMod (g*(n+2)))-affineValue a (0:ZMod (n+2))).val%g=a.val := by
  have he := (affineEquiv (L:=n+2) a 0).property
  rw [affineEquiv_val] at he
  have hh := ReflectionPairedOrbit.reflect_coset g (n+2) r (NeZero.pos g) (by omega)
    a (affineValue a 0) he
  exact hh.trans (congrArg Fin.val ha.symm)

lemma coset_nonzero (n : ℕ) (a : Fin g) (ha : a≠0) (x : Coset g (n+2) a) : x.val≠0 := by
  intro h
  have he := x.property
  rw [h,ZMod.val_zero,Nat.zero_mod] at he
  exact ha (Fin.ext he.symm)

lemma paired_nonzero (n r : ℕ) (a : Fin g) (ha : a≤mate r a) (ha0 : a≠0)
    (x : ReflectionPairedOrbit.PairedCosets (L:=n+2) r a) : x.val≠0 := by
  intro h
  have he := x.property
  rw [h,ZMod.val_zero,Nat.zero_mod] at he
  have ha0' : a.val≠0 := fun h=>ha0 (Fin.ext h)
  have ha' : a.val≤(mate r a).val := ha
  omega

/-- Restrict a proved nonzero source subtype without changing any label. -/
def addNonzero {A : Type*} [Zero A] {P : A→Prop} (h : ∀x:Subtype P,x.val≠0) :
    Subtype P ≃ {x : Subtype P // x.val≠0} where
  toFun x := ⟨x,h x⟩
  invFun x := x.val
  left_inv _ := rfl
  right_inv _ := rfl

def fixedBlockEquiv (n r : ℕ) (a : Fin g) (ha : a=mate r a) :
    ReflectionFixedOrbit.NonzeroCoset g (n+2) a ≃ Block n r a where
  toFun x := ⟨x.val.val,⟨Or.inl x.val.property,x.property⟩⟩
  invFun x := ⟨⟨x.val,by
    rcases x.property.1 with hx|hx
    · exact hx
    · exact hx.trans (congrArg Fin.val ha.symm)⟩,x.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def pairedBlockEquiv (n r : ℕ) (a : Fin g) :
    {x : ReflectionPairedOrbit.PairedCosets (L:=n+2) r a // x.val≠0} ≃ Block n r a where
  toFun x := ⟨x.val.val,⟨x.val.property,x.property⟩⟩
  invFun x := ⟨⟨x.val,x.property.1⟩,x.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

abbrev gapUnit (n δ : ℕ) (hc : Nat.Coprime δ (n+2)) : (ZMod (n+2))ˣ :=
  ZMod.unitOfCoprime δ hc

lemma gap_value (n r p δ : ℕ) (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ) :
    scaleHom g (n+2) (gapUnit n δ hc:ZMod (n+2))=(p:ZMod (g*(n+2)))-(r:ZMod (g*(n+2))) := by
  rw [ZMod.coe_unitOfCoprime,scaleHom_natCast,hp,Nat.cast_add]
  ring

lemma pivot_ne_zero (n p : ℕ) (hp : 0<p) (hpm : p<g*(n+2)) : (p:ZMod (g*(n+2)))≠0 := by
  intro he
  have hh := congrArg ZMod.val he
  rw [ZMod.val_natCast,Nat.mod_eq_of_lt hpm,ZMod.val_zero] at hh
  omega

/-- Consecutive positions, with a closing alternative only for a cycle. -/
def PositionAdjacent (N : ℕ) (closed : Bool) (i j : Fin N) : Prop :=
  i.val+1=j.val ∨ j.val+1=i.val ∨
    (closed=true ∧ ((i.val+1=N ∧ j.val=0) ∨ (j.val+1=N ∧ i.val=0)))

/-- An explicit finite residue component and its proved original-edge coverage. -/
structure Component (n r p : ℕ) (a : Fin g) where
  size : ℕ
  size_pos : 0<size
  cycle : Bool
  equiv : Fin size ≃ Block n r a
  adjacent : ∀i j : Fin size,i≠j →
    ((equiv i).val+(equiv j).val=(r:ZMod (g*(n+2))) ∨
      (equiv i).val+(equiv j).val=(p:ZMod (g*(n+2)))) →
    PositionAdjacent size cycle i j

/-- All four cases are constructed with their correctness proofs together,
so no dependent finite-index casts occur in the local source edge checks. -/
def component (n r p δ : ℕ) (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ)
    (hp0 : 0<p) (hpm : p<g*(n+2)) (a : Fin g) (ha : a≤mate r a) : Component n r p a := by
  by_cases hfix:a=mate r a
  · by_cases hz:a=0
    · subst a
      exact {
        size := n+1
        size_pos := by omega
        cycle := false
        equiv := (ReflectionFixedOrbit.deletedOrder n (r:ZMod (g*(n+2))) p
          (fixed_origin n r 0 hfix) (gapUnit n δ hc) (gap_value n r p δ hc hp)
          (pivot_ne_zero n p hp0 hpm)).trans (fixedBlockEquiv n r 0 hfix)
        adjacent := by
          intro i j hne h
          have hh := ReflectionFixedOrbit.deletedOrder_adjacent n (r:ZMod (g*(n+2))) p
            (fixed_origin n r 0 hfix) (gapUnit n δ hc) (gap_value n r p δ hc hp)
            (pivot_ne_zero n p hp0 hpm) i j hne h
          exact hh.elim Or.inl (fun h=>Or.inr (Or.inl h)) }
    · exact {
        size := n+2
        size_pos := by omega
        cycle := false
        equiv := ((ReflectionFixedOrbit.order n a (r:ZMod (g*(n+2)))
          (fixed_origin n r a hfix) (gapUnit n δ hc)).trans
          (addNonzero (coset_nonzero n a hz))).trans (fixedBlockEquiv n r a hfix)
        adjacent := by
          intro i j hne h
          have hh := ReflectionFixedOrbit.adjacent_of_pair n a (r:ZMod (g*(n+2))) p
            (fixed_origin n r a hfix) (gapUnit n δ hc) (gap_value n r p δ hc hp) i j hne h
          exact hh.elim Or.inl (fun h=>Or.inr (Or.inl h)) }
  · by_cases hz:a=0
    · subst a
      exact {
        size := 2*(n+2)-1
        size_pos := by omega
        cycle := false
        equiv := (ReflectionPairedOrbit.zeroDeletedOrder r hfix δ hc).trans (pairedBlockEquiv n r 0)
        adjacent := by
          intro i j _ h
          change (ReflectionPairedOrbit.zeroDeletedOrder r hfix δ hc i).val.val+
              (ReflectionPairedOrbit.zeroDeletedOrder r hfix δ hc j).val.val=(r:ZMod (g*(n+2))) ∨
            (ReflectionPairedOrbit.zeroDeletedOrder r hfix δ hc i).val.val+
              (ReflectionPairedOrbit.zeroDeletedOrder r hfix δ hc j).val.val=(p:ZMod (g*(n+2))) at h
          have hh := ReflectionPairedOrbit.zeroDeletedOrder_adjacent r hfix δ hc i j
            (h.imp id (fun he=>he.trans (congrArg (fun x:ℕ=>(x:ZMod (g*(n+2)))) hp)))
          exact hh.elim Or.inl (fun h=>Or.inr (Or.inl h)) }
    · exact {
        size := 2*(n+2)
        size_pos := by omega
        cycle := true
        equiv := ((ReflectionPairedOrbit.canonicalOrder r a hfix δ hc).trans
          (addNonzero (paired_nonzero n r a ha hz))).trans (pairedBlockEquiv n r a)
        adjacent := by
          intro i j _ h
          change (ReflectionPairedOrbit.canonicalOrder r a hfix δ hc i).val+
              (ReflectionPairedOrbit.canonicalOrder r a hfix δ hc j).val=(r:ZMod (g*(n+2))) ∨
            (ReflectionPairedOrbit.canonicalOrder r a hfix δ hc i).val+
              (ReflectionPairedOrbit.canonicalOrder r a hfix δ hc j).val=(p:ZMod (g*(n+2))) at h
          have hh := ReflectionPairedOrbit.canonicalOrder_adjacent r a hfix δ hc i j
            (h.imp id (fun he=>he.trans (congrArg (fun x:ℕ=>(x:ZMod (g*(n+2)))) hp)))
          dsimp only [ReflectionPairedOrbit.CycleAdjacent] at hh
          change i.val+1=j.val ∨ j.val+1=i.val ∨
            (true=true ∧ ((i.val+1=2*(n+2) ∧ j.val=0) ∨ (j.val+1=2*(n+2) ∧ i.val=0)))
          rcases hh with hh|hh|hh|hh
          · exact Or.inl hh
          · exact Or.inr (Or.inl hh)
          · exact Or.inr (Or.inr ⟨rfl,Or.inr ⟨hh.2,hh.1⟩⟩)
          · exact Or.inr (Or.inr ⟨rfl,Or.inl ⟨hh.2,hh.1⟩⟩) }

lemma component_size (n r p δ : ℕ) (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ)
    (hp0 : 0<p) (hpm : p<g*(n+2)) (a : Fin g) (ha : a≤mate r a) :
    (component n r p δ hc hp hp0 hpm a ha).size=size n r a := by
  unfold component size
  split_ifs <;> (try subst a) <;> rfl

lemma component_cycle (n r p δ : ℕ) (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ)
    (hp0 : 0<p) (hpm : p<g*(n+2)) (a : Fin g) (ha : a≤mate r a) :
    (component n r p δ hc hp hp0 hpm a ha).cycle=cycle r a := by
  unfold component cycle
  split_ifs <;> (try subst a) <;> rfl

#print axioms fixed_origin
#print axioms component
#print axioms component_size
#print axioms component_cycle
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionComponentOrders

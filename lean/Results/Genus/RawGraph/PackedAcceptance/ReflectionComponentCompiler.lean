import Results.Genus.RawGraph.PackedAcceptance.LayoutCheck

/-! Executable assembly of complete physical layouts from explicit owner-fiber
orders. No component or label is selected by Classical.choice. -/
open scoped BigOperators
namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionComponentCompiler
open LayoutCompiler SourceModel

section Fibers
variable {V C : Type*} (owner : V→C)

/-- Explicit inverse: a physical vertex carries its computed owner. -/
def fiberUnion : (Σc:C,{v : V // owner v=c})≃V where
  toFun x := x.2.val
  invFun v := ⟨owner v,⟨v,rfl⟩⟩
  left_inv := by
    rintro ⟨c,⟨v,hv⟩⟩
    cases hv
    rfl
  right_inv _ := rfl

@[simp] lemma fiberUnion_apply (c : C) (v : {v : V // owner v=c}) :
    fiberUnion owner ⟨c,v⟩=v.val := rfl
@[simp] lemma fiberUnion_symm (v : V) :
    (fiberUnion owner).symm v=⟨owner v,⟨v,rfl⟩⟩ := rfl

end Fibers
section Compiler
variable {m count : ℕ} (owner : Fin (m-1)→Fin count)
variable (size : Fin count→ℕ) (hsize : ∀c,0<size c)
variable (e : ∀c,Fin (size c)≃{v : Fin (m-1) // owner v=c})

/-- Value-preserving passage from a positive vertex size to edge count plus one. -/
def sizeIndex (c : Fin count) : Fin (size c-1+1)≃Fin (size c) :=
  finCongr (by have:=hsize c; omega)

@[simp] lemma sizeIndex_val (c : Fin count) (i : Fin (size c-1+1)) :
    (sizeIndex size hsize c i).val=i.val := rfl
@[simp] lemma sizeIndex_symm_val (c : Fin count) (i : Fin (size c)) :
    ((sizeIndex size hsize c).symm i).val=i.val := rfl

/-- The complete label bijection is assembled only from the supplied finite
fiber equivalences and the computed owner function. -/
def componentLabel : (Σc:Fin count,Fin (size c-1+1))≃Fin (m-1) :=
  (Equiv.sigmaCongrRight (fun c => (sizeIndex size hsize c).trans (e c))).trans (fiberUnion owner)

@[simp] lemma componentLabel_apply (c : Fin count) (i : Fin (size c-1+1)) :
    componentLabel owner size hsize e ⟨c,i⟩=(e c (sizeIndex size hsize c i)).val := rfl

lemma componentLabel_owner (c : Fin count) (i : Fin (size c-1+1)) :
    owner (componentLabel owner size hsize e ⟨c,i⟩)=c :=
  (e c (sizeIndex size hsize c i)).property

@[simp] lemma componentLabel_symm_owner (v : Fin (m-1)) :
    ((componentLabel owner size hsize e).symm v).1=owner v := rfl

@[simp] lemma componentLabel_symm_position (v : Fin (m-1)) :
    ((componentLabel owner size hsize e).symm v).2.val=
      ((e (owner v)).symm ⟨v,rfl⟩).val := rfl

/-- Positive component sizes exclude empty phantom components. Pivot singleton
components and actual cycles are supported without any special case. -/
def layout (cycle : Fin count→Bool) : Layout m where
  count := count
  edges := fun c => size c-1
  cycle := cycle
  label := componentLabel owner size hsize e

@[simp] lemma layout_count (cycle : Fin count→Bool) :
    (layout owner size hsize e cycle).count=count := rfl
@[simp] lemma layout_edges (cycle : Fin count→Bool) (c : Fin count) :
    (layout owner size hsize e cycle).edges c=size c-1 := rfl
@[simp] lemma layout_cycle (cycle : Fin count→Bool) (c : Fin count) :
    (layout owner size hsize e cycle).cycle c=cycle c := rfl
@[simp] lemma layout_label (cycle : Fin count→Bool) (c : Fin count) (i : Fin (size c-1+1)) :
    (layout owner size hsize e cycle).label ⟨c,i⟩=(e c (sizeIndex size hsize c i)).val := rfl

/-- Consecutive positions or the flagged last/first closing pair. -/
def OrderedPair (n : ℕ) (cycle : Bool) (i j : Fin n) : Prop :=
  i.val+1=j.val ∨ j.val+1=i.val ∨
    (cycle=true ∧ ((i.val+1=n ∧ j.val=0) ∨ (j.val+1=n ∧ i.val=0)))

instance (n : ℕ) (cycle : Bool) (i j : Fin n) : Decidable (OrderedPair n cycle i j) := by
  unfold OrderedPair
  infer_instance

/-- An explicit owner fiber's positional proof yields actual layout adjacency. -/
lemma adjacent_of_fiber_positions (cycle : Fin count→Bool) (c : Fin count)
    (u v : {v : Fin (m-1) // owner v=c})
    (h : OrderedPair (size c) (cycle c) ((e c).symm u) ((e c).symm v)) :
    Adjacent (layout owner size hsize e cycle) u.val v.val := by
  let i := (sizeIndex size hsize c).symm ((e c).symm u)
  let j := (sizeIndex size hsize c).symm ((e c).symm v)
  have hi : (layout owner size hsize e cycle).label ⟨c,i⟩=u.val := by
    change (e c (sizeIndex size hsize c ((sizeIndex size hsize c).symm ((e c).symm u)))).val=u.val
    rw [Equiv.apply_symm_apply,Equiv.apply_symm_apply]
  have hj : (layout owner size hsize e cycle).label ⟨c,j⟩=v.val := by
    change (e c (sizeIndex size hsize c ((sizeIndex size hsize c).symm ((e c).symm v)))).val=v.val
    rw [Equiv.apply_symm_apply,Equiv.apply_symm_apply]
  rw [←hi,←hj]
  apply adjacent_of_positions
  change i.val+1=j.val ∨ j.val+1=i.val ∨
    (cycle c=true ∧ ((i.val=size c-1 ∧ j.val=0) ∨ (j.val=size c-1 ∧ i.val=0)))
  have hi' : i.val=((e c).symm u).val := rfl
  have hj' : j.val=((e c).symm v).val := rfl
  have hn:=hsize c
  unfold OrderedPair at h
  rw [hi',hj']
  rcases h with h | h | ⟨hc,h | h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨hc,Or.inl ⟨by omega,h.2⟩⟩)
  · exact Or.inr (Or.inr ⟨hc,Or.inr ⟨by omega,h.2⟩⟩)

/-- Exact original-source coverage from two independently proved family facts:
positive source edges stay within owner fibers, and their positions are legal. -/
theorem covers (cycle : Fin count→Bool) (r p a : ℕ)
    (howner : ∀u v : Fin (m-1),0<edgeBound r p a u v → owner u=owner v)
    (hpositions : ∀c (u v : {v : Fin (m-1) // owner v=c}),
      0<edgeBound r p a u.val v.val →
        OrderedPair (size c) (cycle c) ((e c).symm u) ((e c).symm v)) :
    Covers (layout owner size hsize e cycle) r p a := by
  intro u v he
  let c:=owner u
  let u' : {v : Fin (m-1) // owner v=c}:=⟨u,rfl⟩
  let v' : {v : Fin (m-1) // owner v=c}:=⟨v,(howner u v he).symm⟩
  exact adjacent_of_fiber_positions owner size hsize e cycle c u' v' (hpositions c u' v' he)


/-- The assembled computable layout evaluates the exact original source
polynomial once its two local geometric facts have been supplied. -/
theorem source_polynomial (cycle : Fin count→Bool) {r p a : ℕ} (hp : Parameters m r p a)
    (howner : ∀u v : Fin (m-1),0<edgeBound r p a u v → owner u=owner v)
    (hpositions : ∀c (u v : {v : Fin (m-1) // owner v=c}),
      0<edgeBound r p a u.val v.val →
        OrderedPair (size c) (cycle c) ((e c).symm u) ((e c).symm v)) :
    rawPolynomial m r p a=∏c,componentRun (layout owner size hsize e cycle) r p a c :=
  rawPolynomial_eq_components (layout owner size hsize e cycle) hp
    (covers owner size hsize e cycle r p a howner hpositions)

end Compiler
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionComponentCompiler

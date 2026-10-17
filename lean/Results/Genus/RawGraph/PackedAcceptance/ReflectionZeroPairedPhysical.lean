import Results.Genus.RawGraph.PackedAcceptance.ReflectionZeroPairedEndpoints
import Results.Genus.RawGraph.PackedAcceptance.ReflectionFullLayout

namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionZeroPaired
open SourceModel LayoutCompiler ReflectionPairedOrbit ReflectionFullLayout
variable {g : ℕ} [NeZero g]

lemma component_zero_order (n r p δ : ℕ) (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ)
    (hp0 : 0<p) (hpm : p<g*(n+2)) (a : Fin g) (ha : a≤mate r a) (hz : a=0)
    (hpair : (0:Fin g)≠mate r 0) :
    (⟨(ReflectionComponentOrders.component n r p δ hc hp hp0 hpm a ha).size,
      fun j=>((ReflectionComponentOrders.component n r p δ hc hp hp0 hpm a ha).equiv j).val⟩ :
      ΣN,Fin N→ZMod (g*(n+2)))=
    ⟨2*(n+2)-1,fun j=>(zeroDeletedOrder r hpair δ hc j).val.val⟩ := by
  subst a
  let f : ReflectionComponentOrders.Component n r p (0:Fin g) → (ΣN,Fin N→ZMod (g*(n+2))) :=
    fun D=>⟨D.size,fun j=>(D.equiv j).val⟩
  change f (ReflectionComponentOrders.component n r p δ hc hp hp0 hpm 0 ha)=_
  unfold ReflectionComponentOrders.component
  rw [dif_neg hpair,dif_pos (rfl:(0:Fin g)=0)]
  rfl

lemma component_zero_value (n r p δ : ℕ) (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ)
    (hp0 : 0<p) (hpm : p<g*(n+2)) (a : Fin g) (ha : a≤mate r a) (hz : a=0)
    (hpair : (0:Fin g)≠mate r 0) (j : Fin (2*(n+2)-1))
    (i : Fin (ReflectionComponentOrders.component n r p δ hc hp hp0 hpm a ha).size)
    (hij : i.val=j.val) :
    ((ReflectionComponentOrders.component n r p δ hc hp hp0 hpm a ha).equiv i).val=
      (zeroDeletedOrder r hpair δ hc j).val.val := by
  have aux : ∀(D : ΣN,Fin N→ZMod (g*(n+2))),
      D=⟨2*(n+2)-1,fun j=>(zeroDeletedOrder r hpair δ hc j).val.val⟩ →
      ∀i:Fin D.1,i.val=j.val → D.2 i=(zeroDeletedOrder r hpair δ hc j).val.val := by
    intro D hD
    subst D
    intro i hij
    have hi : i=j := Fin.ext hij
    subst i
    rfl
  exact aux _ (component_zero_order n r p δ hc hp hp0 hpm a ha hz hpair) i hij

lemma zero_edges (n r p δ : ℕ) (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ)
    (hp0 : 0<p) (hpm : p<g*(n+2)) (c : Fin (count (g:=g) r))
    (hz : representative r c=0) (hpair : (0:Fin g)≠mate r 0) :
    (layout n r p δ hc hp hp0 hpm).edges c=2*n+2 := by
  change (componentData n r p δ hc hp hp0 hpm c).size-1=_
  rw [ReflectionComponentOrders.component_size]
  simp only [ReflectionComponentOrders.size,hz,hpair,↓reduceIte]
  omega

lemma zero_cycle (n r p δ : ℕ) (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ)
    (hp0 : 0<p) (hpm : p<g*(n+2)) (c : Fin (count (g:=g) r))
    (hz : representative r c=0) (hpair : (0:Fin g)≠mate r 0) :
    (layout n r p δ hc hp hp0 hpm).cycle c=false := by
  change (componentData n r p δ hc hp hp0 hpm c).cycle=_
  rw [ReflectionComponentOrders.component_cycle]
  simp only [ReflectionComponentOrders.cycle,hz,hpair,↓reduceIte]

def zeroIndex (n r p δ : ℕ) (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ)
    (hp0 : 0<p) (hpm : p<g*(n+2)) (c : Fin (count (g:=g) r))
    (hz : representative r c=0) (hpair : (0:Fin g)≠mate r 0)
    (j : Fin ((layout n r p δ hc hp hp0 hpm).edges c+1)) : Fin (2*n+3) :=
  ⟨j.val,by have:=j.isLt;have:=zero_edges n r p δ hc hp hp0 hpm c hz hpair;omega⟩

theorem label_eq_zero_point (n r p δ : ℕ) (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ)
    (hp0 : 0<p) (hpm : p<g*(n+2)) (c : Fin (count (g:=g) r))
    (hz : representative r c=0) (hpair : (0:Fin g)≠mate r 0)
    (j : Fin ((layout n r p δ hc hp hp0 hpm).edges c+1)) :
    (layout n r p δ hc hp hp0 hpm).label ⟨c,j⟩=
      point n r δ hc hpair (zeroIndex n r p δ hc hp hp0 hpm c hz hpair j) := by
  apply Fin.ext
  change (((componentData n r p δ hc hp hp0 hpm c).equiv
    (ReflectionComponentCompiler.sizeIndex
      (fun c=>(componentData n r p δ hc hp hp0 hpm c).size)
      (fun c=>(componentData n r p δ hc hp hp0 hpm c).size_pos) c j)).val).val-1=_
  have hj : j.val<2*(n+2)-1 := by have:=j.isLt;have:=zero_edges n r p δ hc hp hp0 hpm c hz hpair;omega
  rw [component_zero_value n r p δ hc hp hp0 hpm (representative r c)
    (representative_le r c) hz hpair ⟨j.val,hj⟩ _ rfl]
  rfl

#print axioms component_zero_order
#print axioms component_zero_value
#print axioms zero_edges
#print axioms zero_cycle
#print axioms label_eq_zero_point
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionZeroPaired

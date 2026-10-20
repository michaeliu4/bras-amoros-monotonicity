import Results.Genus.RawGraph.PackedAcceptance.ReflectionFixedPhysicalLabels

/-! Original fixed-zero raw signatures. Exactly the zero residue is removed;
the two pivot singleton masks and all original endpoint loops are retained. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionFixedZeroPhysical
open LayoutCompiler SourceModel ReflectionPairedOrbit ReflectionFullLayout
open ReflectionCoset ReflectionFixedOrbit ReflectionComponentOrders ReflectionFixedSourceWindow
variable {g : ℕ} [NeZero g]

abbrev zeroOrder (n r p δ : ℕ) (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ)
    (hp0 : 0<p) (hpm : p<g*(n+2)) (hfix : (0:Fin g)=mate r 0) :=
  deletedOrder n (r:ZMod (g*(n+2))) p (fixed_origin n r 0 hfix) (gapUnit n δ hc)
    (gap_value n r p δ hc hp) (pivot_ne_zero n p hp0 hpm)

/-- Source-index map after deleting zero, with global path phase unchanged. -/
def originalIndex (n r p δ : ℕ) (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ)
    (hp0 : 0<p) (hpm : p<g*(n+2)) (hfix : (0:Fin g)=mate r 0) (j : Fin (n+1)) : Fin (n+2) :=
  (zeroCut n (r:ZMod (g*(n+2))) p (fixed_origin n r 0 hfix) (gapUnit n δ hc)
    (gap_value n r p δ hc hp) (pivot_ne_zero n p hp0 hpm)).castSucc.succAbove j

lemma zeroOrder_value (n r p δ : ℕ) (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ)
    (hp0 : 0<p) (hpm : p<g*(n+2)) (hfix : (0:Fin g)=mate r 0) (j : Fin (n+1)) :
    (zeroOrder n r p δ hc hp hp0 hpm hfix j).val.val=
      residue n r δ 0 hfix hc (originalIndex n r p δ hc hp hp0 hpm hfix j) := rfl

abbrev zeroPoint (n r p δ : ℕ) (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ)
    (hp0 : 0<p) (hpm : p<g*(n+2)) (hfix : (0:Fin g)=mate r 0) (j : Fin (n+1)) :=
  point n r δ 0 hfix hc (originalIndex n r p δ hc hp hp0 hpm hfix j)
    (zeroOrder n r p δ hc hp hp0 hpm hfix j).property

lemma zero_edges (n r p δ : ℕ) (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ)
    (hp0 : 0<p) (hpm : p<g*(n+2)) (c : Fin (count (g:=g) r))
    (hfix : representative r c=mate r (representative r c)) (ha0 : representative r c=0) :
    (layout n r p δ hc hp hp0 hpm).edges c=n := by
  change (componentData n r p δ hc hp hp0 hpm c).size-1=_
  rw [component_size]
  unfold ReflectionComponentOrders.size
  rw [if_pos hfix,if_pos ha0]
  omega

lemma component_order (n r p δ : ℕ) (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ)
    (hp0 : 0<p) (hpm : p<g*(n+2)) (ha : (0:Fin g)≤mate r 0) (hfix : (0:Fin g)=mate r 0) :
    (⟨(component n r p δ hc hp hp0 hpm 0 ha).size,(component n r p δ hc hp hp0 hpm 0 ha).equiv⟩ :
      ΣN,Fin N≃Block n r (0:Fin g))=
    ⟨n+1,(zeroOrder n r p δ hc hp hp0 hpm hfix).trans (fixedBlockEquiv n r 0 hfix)⟩ := by
  let f : Component n r p (0:Fin g)→(ΣN,Fin N≃Block n r (0:Fin g)) := fun D=>⟨D.size,D.equiv⟩
  change f (component n r p δ hc hp hp0 hpm 0 ha)=_
  unfold component
  rw [dif_pos hfix,dif_pos rfl]

lemma component_value (n r p δ : ℕ) (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ)
    (hp0 : 0<p) (hpm : p<g*(n+2)) (a : Fin g) (ha : a≤mate r a)
    (hfix : a=mate r a) (ha0 : a=0) (j : Fin (n+1))
    (i : Fin (component n r p δ hc hp hp0 hpm a ha).size) (hij : i.val=j.val) :
    ((component n r p δ hc hp hp0 hpm a ha).equiv i).val=
      (zeroOrder n r p δ hc hp hp0 hpm (by simpa only [ha0] using hfix) j).val.val := by
  subst a
  have aux : ∀(D : ΣN,Fin N≃Block n r (0:Fin g)),
      D=⟨n+1,(zeroOrder n r p δ hc hp hp0 hpm hfix).trans (fixedBlockEquiv n r 0 hfix)⟩ →
      ∀i:Fin D.1,i.val=j.val→(D.2 i).val=(zeroOrder n r p δ hc hp hp0 hpm hfix j).val.val := by
    intro D hD
    subst D
    intro i hij
    have hi : i=j := Fin.ext hij
    subst i
    rfl
  exact aux _ (component_order n r p δ hc hp hp0 hpm ha hfix) i hij

def index (n r p δ : ℕ) (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ)
    (hp0 : 0<p) (hpm : p<g*(n+2)) (c : Fin (count (g:=g) r))
    (hfix : representative r c=mate r (representative r c)) (ha0 : representative r c=0)
    (j : Fin ((layout n r p δ hc hp hp0 hpm).edges c+1)) : Fin (n+1) :=
  ⟨j.val,by have:=j.isLt;have:=zero_edges n r p δ hc hp hp0 hpm c hfix ha0;omega⟩

theorem label_eq_point (n r p δ : ℕ) (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ)
    (hp0 : 0<p) (hpm : p<g*(n+2)) (c : Fin (count (g:=g) r))
    (hfix : representative r c=mate r (representative r c)) (ha0 : representative r c=0)
    (j : Fin ((layout n r p δ hc hp hp0 hpm).edges c+1)) :
    (layout n r p δ hc hp hp0 hpm).label ⟨c,j⟩=
      zeroPoint n r p δ hc hp hp0 hpm (by simpa only [ha0] using hfix)
        (index n r p δ hc hp hp0 hpm c hfix ha0 j) := by
  apply Fin.ext
  change (((componentData n r p δ hc hp hp0 hpm c).equiv
    (ReflectionComponentCompiler.sizeIndex
      (fun c=>(componentData n r p δ hc hp hp0 hpm c).size)
      (fun c=>(componentData n r p δ hc hp hp0 hpm c).size_pos) c j)).val).val-1=_
  rw [component_value n r p δ hc hp hp0 hpm (representative r c)
    (representative_le r c) hfix ha0 (index n r p δ hc hp hp0 hpm c hfix ha0 j) _ rfl]
  rfl

def signature (n r p δ cap : ℕ) (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ)
    (hp0 : 0<p) (hpm : p<g*(n+2)) (hfix : (0:Fin g)=mate r 0) : ComponentSignature cap where
  edges := n
  mask j v := ReflectionFixedSourceWindow.mask (g*(n+2)) r p cap
    (residue n r δ 0 hfix hc (originalIndex n r p δ hc hp hp0 hpm hfix j)).val
    (decide (endpoint n (originalIndex n r p δ hc hp hp0 hpm hfix j))) v
  bound j := edgeBound r p cap (zeroPoint n r p δ hc hp hp0 hpm hfix j.castSucc)
    (zeroPoint n r p δ hc hp hp0 hpm hfix j.succ)
  cycle := false
  close := edgeBound r p cap (zeroPoint n r p δ hc hp hp0 hpm hfix (Fin.last n))
    (zeroPoint n r p δ hc hp hp0 hpm hfix 0)

theorem physicalSignature_eq (n r p δ cap : ℕ) (hc : Nat.Coprime δ (n+2))
    (hp : p=r+g*δ) (hp0 : 0<p) (hpm : p<g*(n+2)) (c : Fin (count (g:=g) r))
    (hfix : representative r c=mate r (representative r c)) (ha0 : representative r c=0) :
    physicalSignature (layout n r p δ hc hp hp0 hpm) r p cap c=
      signature n r p δ cap hc hp hp0 hpm (by simpa only [ha0] using hfix) := by
  have he:=zero_edges n r p δ hc hp hp0 hpm c hfix ha0
  apply sameSignature_sound
  refine ⟨he,ReflectionFixedPhysicalLabels.fixed_cycle n r p δ hc hp hp0 hpm c hfix,?_,?_,?_⟩
  · change edgeBound r p cap _ _=edgeBound r p cap _ _
    rw [label_eq_point n r p δ hc hp hp0 hpm c hfix ha0,
      label_eq_point n r p δ hc hp hp0 hpm c hfix ha0]
    have hl : index n r p δ hc hp hp0 hpm c hfix ha0
        (Fin.last ((layout n r p δ hc hp hp0 hpm).edges c))=Fin.last n := Fin.ext he
    rw [hl]
    rfl
  · intro j v
    have hj : j.val<n+1 := by have:=j.isLt;change j.val<(layout n r p δ hc hp hp0 hpm).edges c+1 at this;omega
    simp only [physicalSignature,signature,dif_pos hj]
    rw [label_eq_point n r p δ hc hp hp0 hpm c hfix ha0]
    exact domain_mask n r p δ cap hp hpm 0 _ hc _ _ v
  · intro j
    have hj : j.val<n := by have:=j.isLt;change j.val<(layout n r p δ hc hp hp0 hpm).edges c at this;omega
    simp only [physicalSignature,signature,dif_pos hj]
    rw [label_eq_point n r p δ hc hp hp0 hpm c hfix ha0,
      label_eq_point n r p δ hc hp hp0 hpm c hfix ha0]
    rfl

#print axioms originalIndex
#print axioms label_eq_point
#print axioms physicalSignature_eq
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionFixedZeroPhysical

import Results.Genus.RawGraph.PackedAcceptance.ReflectionFullLayout
import Results.Genus.RawGraph.PackedAcceptance.ReflectionFixedSourceWindow
import Results.Genus.RawGraph.SignatureCheck

/-! The raw complete layout retains its exact fixed-coset ordering, with the
original unary fields at every position and all terminal fields present. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionFixedPhysicalLabels
open LayoutCompiler SourceModel ReflectionPairedOrbit ReflectionFullLayout
open ReflectionFixedSourceWindow
variable {g : ℕ} [NeZero g]

lemma fixed_edges (n r p δ : ℕ) (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ)
    (hp0 : 0<p) (hpm : p<g*(n+2)) (c : Fin (count (g:=g) r))
    (hfix : representative r c=mate r (representative r c)) (ha0 : representative r c≠0) :
    (layout n r p δ hc hp hp0 hpm).edges c=n+1 := by
  change (componentData n r p δ hc hp hp0 hpm c).size-1=_
  rw [ReflectionComponentOrders.component_size]
  unfold ReflectionComponentOrders.size
  rw [if_pos hfix,if_neg ha0]
  omega

lemma fixed_cycle (n r p δ : ℕ) (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ)
    (hp0 : 0<p) (hpm : p<g*(n+2)) (c : Fin (count (g:=g) r))
    (hfix : representative r c=mate r (representative r c)) :
    (layout n r p δ hc hp hp0 hpm).cycle c=false := by
  change (componentData n r p δ hc hp hp0 hpm c).cycle=_
  rw [ReflectionComponentOrders.component_cycle]
  unfold ReflectionComponentOrders.cycle
  rw [if_pos hfix]

lemma component_order (n r p δ : ℕ) (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ)
    (hp0 : 0<p) (hpm : p<g*(n+2)) (a : Fin g) (ha : a≤mate r a)
    (hfix : a=mate r a) (ha0 : a≠0) :
    (⟨(ReflectionComponentOrders.component n r p δ hc hp hp0 hpm a ha).size,
      (ReflectionComponentOrders.component n r p δ hc hp hp0 hpm a ha).equiv⟩ :
      ΣN,Fin N≃ReflectionComponentOrders.Block n r a)=
    ⟨n+2,((ReflectionFixedOrbit.order n a r (ReflectionComponentOrders.fixed_origin n r a hfix)
      (ReflectionComponentOrders.gapUnit n δ hc)).trans
      (ReflectionComponentOrders.addNonzero (ReflectionComponentOrders.coset_nonzero n a ha0))).trans
      (ReflectionComponentOrders.fixedBlockEquiv n r a hfix)⟩ := by
  let f : ReflectionComponentOrders.Component n r p a→(ΣN,Fin N≃ReflectionComponentOrders.Block n r a) :=
    fun D=>⟨D.size,D.equiv⟩
  change f (ReflectionComponentOrders.component n r p δ hc hp hp0 hpm a ha)=_
  unfold ReflectionComponentOrders.component
  rw [dif_pos hfix,dif_neg ha0]

lemma component_value (n r p δ : ℕ) (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ)
    (hp0 : 0<p) (hpm : p<g*(n+2)) (a : Fin g) (ha : a≤mate r a)
    (hfix : a=mate r a) (ha0 : a≠0) (j : Fin (n+2))
    (i : Fin (ReflectionComponentOrders.component n r p δ hc hp hp0 hpm a ha).size)
    (hij : i.val=j.val) :
    ((ReflectionComponentOrders.component n r p δ hc hp hp0 hpm a ha).equiv i).val=
      residue n r δ a hfix hc j := by
  have aux : ∀(D : ΣN,Fin N≃ReflectionComponentOrders.Block n r a),
      D=⟨n+2,((ReflectionFixedOrbit.order n a r (ReflectionComponentOrders.fixed_origin n r a hfix)
      (ReflectionComponentOrders.gapUnit n δ hc)).trans
      (ReflectionComponentOrders.addNonzero (ReflectionComponentOrders.coset_nonzero n a ha0))).trans
      (ReflectionComponentOrders.fixedBlockEquiv n r a hfix)⟩ →
      ∀i:Fin D.1,i.val=j.val→(D.2 i).val=residue n r δ a hfix hc j := by
    intro D hD
    subst D
    intro i hij
    have hi : i=j := Fin.ext hij
    subst i
    rfl
  exact aux _ (component_order n r p δ hc hp hp0 hpm a ha hfix ha0) i hij

abbrev fullPoint (n r δ : ℕ) (a : Fin g) (hfix : a=mate r a)
    (hc : Nat.Coprime δ (n+2)) (ha0 : a≠0) (i : Fin (n+2)) :=
  point n r δ a hfix hc i (ReflectionComponentOrders.coset_nonzero n a ha0 _)

def fixedIndex (n r p δ : ℕ) (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ)
    (hp0 : 0<p) (hpm : p<g*(n+2)) (c : Fin (count (g:=g) r))
    (hfix : representative r c=mate r (representative r c)) (ha0 : representative r c≠0)
    (j : Fin ((layout n r p δ hc hp hp0 hpm).edges c+1)) : Fin (n+2) :=
  ⟨j.val,by have:=j.isLt;have:=fixed_edges n r p δ hc hp hp0 hpm c hfix ha0;omega⟩

theorem label_eq_point (n r p δ : ℕ) (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ)
    (hp0 : 0<p) (hpm : p<g*(n+2)) (c : Fin (count (g:=g) r))
    (hfix : representative r c=mate r (representative r c)) (ha0 : representative r c≠0)
    (j : Fin ((layout n r p δ hc hp hp0 hpm).edges c+1)) :
    (layout n r p δ hc hp hp0 hpm).label ⟨c,j⟩=
      fullPoint n r δ (representative r c) hfix hc ha0
        (fixedIndex n r p δ hc hp hp0 hpm c hfix ha0 j) := by
  apply Fin.ext
  change (((componentData n r p δ hc hp hp0 hpm c).equiv
    (ReflectionComponentCompiler.sizeIndex
      (fun c=>(componentData n r p δ hc hp hp0 hpm c).size)
      (fun c=>(componentData n r p δ hc hp hp0 hpm c).size_pos) c j)).val).val-1=_
  rw [component_value n r p δ hc hp hp0 hpm (representative r c)
    (representative_le r c) hfix ha0
    (fixedIndex n r p δ hc hp hp0 hpm c hfix ha0 j) _ rfl]
  rfl

/-- Original masks are kept at all indices, even a head or terminal vertex
outside a complete aligned pair. The actual last/first field is also retained. -/
def signature (n r p δ cap : ℕ) (a : Fin g) (hfix : a=mate r a)
    (hc : Nat.Coprime δ (n+2)) (ha0 : a≠0) : ComponentSignature cap where
  edges := n+1
  mask i v := ReflectionFixedSourceWindow.mask (g*(n+2)) r p cap
    (residue n r δ a hfix hc i).val (decide (endpoint n i)) v
  bound i := edgeBound r p cap (fullPoint n r δ a hfix hc ha0 i.castSucc)
    (fullPoint n r δ a hfix hc ha0 i.succ)
  cycle := false
  close := edgeBound r p cap (fullPoint n r δ a hfix hc ha0 (Fin.last (n+1)))
    (fullPoint n r δ a hfix hc ha0 0)

theorem physicalSignature_eq (n r p δ cap : ℕ) (hc : Nat.Coprime δ (n+2))
    (hp : p=r+g*δ) (hp0 : 0<p) (hpm : p<g*(n+2)) (c : Fin (count (g:=g) r))
    (hfix : representative r c=mate r (representative r c)) (ha0 : representative r c≠0) :
    physicalSignature (layout n r p δ hc hp hp0 hpm) r p cap c=
      signature n r p δ cap (representative r c) hfix hc ha0 := by
  have he:=fixed_edges n r p δ hc hp hp0 hpm c hfix ha0
  apply sameSignature_sound
  refine ⟨he,fixed_cycle n r p δ hc hp hp0 hpm c hfix,?_,?_,?_⟩
  · change edgeBound r p cap _ _=edgeBound r p cap _ _
    rw [label_eq_point n r p δ hc hp hp0 hpm c hfix ha0,
      label_eq_point n r p δ hc hp hp0 hpm c hfix ha0]
    have hl : fixedIndex n r p δ hc hp hp0 hpm c hfix ha0
        (Fin.last ((layout n r p δ hc hp hp0 hpm).edges c))=Fin.last (n+1) := Fin.ext he
    rw [hl]
    rfl
  · intro j v
    have hj : j.val<n+1+1 := by have:=j.isLt;change j.val<(layout n r p δ hc hp hp0 hpm).edges c+1 at this;omega
    simp only [physicalSignature,signature,dif_pos hj]
    rw [label_eq_point n r p δ hc hp hp0 hpm c hfix ha0]
    exact domain_mask n r p δ cap hp hpm (representative r c) hfix hc _ _ v
  · intro j
    have hj : j.val<n+1 := by have:=j.isLt;change j.val<(layout n r p δ hc hp hp0 hpm).edges c at this;omega
    simp only [physicalSignature,signature,dif_pos hj]
    rw [label_eq_point n r p δ hc hp hp0 hpm c hfix ha0,
      label_eq_point n r p δ hc hp hp0 hpm c hfix ha0]
    rfl

#print axioms label_eq_point
#print axioms physicalSignature_eq
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionFixedPhysicalLabels

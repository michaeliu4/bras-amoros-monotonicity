import Results.Genus.RawGraph.PackedAcceptance.ReflectionFullLayout
import Results.Genus.RawGraph.PackedAcceptance.ReflectionPairedLetters

/-! Exact label identity between the original complete executable layout and
its nonzero paired arithmetic word. No per-position finite check is assumed. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionPairedPhysicalLabels
open LayoutCompiler SourceModel ReflectionPairedOrbit
open ReflectionFullLayout

variable {g : ℕ} [NeZero g]

lemma paired_edges (n r p δ : ℕ) (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ)
    (hp0 : 0<p) (hpm : p<g*(n+2)) (c : Fin (count (g:=g) r))
    (hpair : representative r c≠mate r (representative r c))
    (ha0 : representative r c≠0) :
    (layout n r p δ hc hp hp0 hpm).edges c=2*(n+2)-1 := by
  change (componentData n r p δ hc hp hp0 hpm c).size-1=_
  rw [ReflectionComponentOrders.component_size]
  simp only [ReflectionComponentOrders.size,hpair,ha0,↓reduceIte]

lemma paired_cycle (n r p δ : ℕ) (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ)
    (hp0 : 0<p) (hpm : p<g*(n+2)) (c : Fin (count (g:=g) r))
    (hpair : representative r c≠mate r (representative r c))
    (ha0 : representative r c≠0) :
    (layout n r p δ hc hp hp0 hpm).cycle c=true := by
  change (componentData n r p δ hc hp hp0 hpm c).cycle=_
  rw [ReflectionComponentOrders.component_cycle]
  simp only [ReflectionComponentOrders.cycle,hpair,ha0,↓reduceIte]

def pairedIndex (n r p δ : ℕ) (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ)
    (hp0 : 0<p) (hpm : p<g*(n+2)) (c : Fin (count (g:=g) r))
    (hpair : representative r c≠mate r (representative r c))
    (ha0 : representative r c≠0)
    (j : Fin ((layout n r p δ hc hp hp0 hpm).edges c+1)) : Fin (2*(n+2)) :=
  ⟨j.val,by have hj:=j.isLt; have he:=paired_edges n r p δ hc hp hp0 hpm c hpair ha0;omega⟩

lemma component_order (n r p δ : ℕ) (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ)
    (hp0 : 0<p) (hpm : p<g*(n+2)) (a : Fin g) (ha : a≤mate r a)
    (hpair : a≠mate r a) (ha0 : a≠0) :
    (⟨(ReflectionComponentOrders.component n r p δ hc hp hp0 hpm a ha).size,
      (ReflectionComponentOrders.component n r p δ hc hp hp0 hpm a ha).equiv⟩ :
      ΣN,Fin N≃ReflectionComponentOrders.Block n r a)=
    ⟨2*(n+2),((canonicalOrder r a hpair δ hc).trans
      (ReflectionComponentOrders.addNonzero (ReflectionComponentOrders.paired_nonzero n r a ha ha0))).trans
      (ReflectionComponentOrders.pairedBlockEquiv n r a)⟩ := by
  let f : ReflectionComponentOrders.Component n r p a → (ΣN,Fin N≃ReflectionComponentOrders.Block n r a) :=
    fun D=>⟨D.size,D.equiv⟩
  change f (ReflectionComponentOrders.component n r p δ hc hp hp0 hpm a ha)=_
  unfold ReflectionComponentOrders.component
  rw [dif_neg hpair,dif_neg ha0]

lemma component_equiv_value (n r p δ : ℕ) (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ)
    (hp0 : 0<p) (hpm : p<g*(n+2)) (a : Fin g) (ha : a≤mate r a)
    (hpair : a≠mate r a) (ha0 : a≠0)
    (j : Fin (2*(n+2)))
    (i : Fin (ReflectionComponentOrders.component n r p δ hc hp hp0 hpm a ha).size)
    (hij : i.val=j.val) :
    ((ReflectionComponentOrders.component n r p δ hc hp hp0 hpm a ha).equiv i).val=
      (canonicalOrder r a hpair δ hc j).val := by
  have aux : ∀(D : ΣN,Fin N≃ReflectionComponentOrders.Block n r a),
      D=⟨2*(n+2),((canonicalOrder r a hpair δ hc).trans
        (ReflectionComponentOrders.addNonzero (ReflectionComponentOrders.paired_nonzero n r a ha ha0))).trans
        (ReflectionComponentOrders.pairedBlockEquiv n r a)⟩ →
      ∀i:Fin D.1,i.val=j.val → (D.2 i).val=(canonicalOrder r a hpair δ hc j).val := by
    intro D hD
    subst D
    intro i hij
    have hi : i=j := Fin.ext hij
    subst i
    rfl
  exact aux _ (component_order n r p δ hc hp hp0 hpm a ha hpair ha0) i hij

theorem label_eq_point (n r p δ : ℕ) (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ)
    (hp0 : 0<p) (hpm : p<g*(n+2)) (c : Fin (count (g:=g) r))
    (hpair : representative r c≠mate r (representative r c))
    (ha0 : representative r c≠0)
    (j : Fin ((layout n r p δ hc hp hp0 hpm).edges c+1)) :
    (layout n r p δ hc hp hp0 hpm).label ⟨c,j⟩=
      (ReflectionThresholdWord.point n r p δ hp hc (representative r c)
        (representative_le r c) ha0 hpair
        (pairedIndex n r p δ hc hp hp0 hpm c hpair ha0 j)).val := by
  apply Fin.ext
  change (((componentData n r p δ hc hp hp0 hpm c).equiv
    (ReflectionComponentCompiler.sizeIndex
      (fun c=>(componentData n r p δ hc hp hp0 hpm c).size)
      (fun c=>(componentData n r p δ hc hp hp0 hpm c).size_pos) c j)).val).val-1=_
  rw [component_equiv_value n r p δ hc hp hp0 hpm (representative r c)
    (representative_le r c) hpair ha0
    (pairedIndex n r p δ hc hp hp0 hpm c hpair ha0 j) _ rfl]
  rfl

#print axioms paired_edges
#print axioms paired_cycle
#print axioms label_eq_point
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionPairedPhysicalLabels

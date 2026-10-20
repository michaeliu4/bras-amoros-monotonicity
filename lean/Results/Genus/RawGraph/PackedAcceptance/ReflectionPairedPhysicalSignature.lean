import Results.Genus.RawGraph.PackedAcceptance.ReflectionPairedPhysicalLabels
import Results.Genus.RawGraph.PackedAcceptance.ReflectionDeltaOneSignature
import Results.Genus.RawGraph.SignatureCheck

/-! All five signature fields are transported from the original executable
layout. Ordinary-word equality alone is deliberately insufficient. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionPairedPhysicalLabels
open LayoutCompiler SourceModel ReflectionPairedOrbit ReflectionFullLayout
open ReflectionThresholdWord
variable {g : ℕ} [NeZero g]

theorem physicalSignature_eq_canonical (n r p δ cap : ℕ)
    (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ)
    (hp0 : 0<p) (hpm : p<g*(n+2)) (c : Fin (count (g:=g) r))
    (hpair : representative r c≠mate r (representative r c))
    (ha0 : representative r c≠0) :
    physicalSignature (layout n r p δ hc hp hp0 hpm) r p cap c=
      canonicalSignature n r p δ cap hp hc (representative r c)
        (representative_le r c) ha0 hpair := by
  have he:=paired_edges n r p δ hc hp hp0 hpm c hpair ha0
  apply sameSignature_sound
  refine ⟨he,paired_cycle n r p δ hc hp hp0 hpm c hpair ha0,?_,?_,?_⟩
  · change edgeBound r p cap _ _=edgeBound r p cap _ _
    rw [label_eq_point n r p δ hc hp hp0 hpm c hpair ha0,
      label_eq_point n r p δ hc hp hp0 hpm c hpair ha0]
    have hl : pairedIndex n r p δ hc hp hp0 hpm c hpair ha0
        (Fin.last ((layout n r p δ hc hp hp0 hpm).edges c))=
        (⟨2*(n+2)-1,by omega⟩:Fin (2*(n+2))) := Fin.ext he
    rw [hl]
    rfl
  · intro j v
    have hj : j.val<2*(n+2)-1+1 := by have:=j.isLt;change j.val<(layout n r p δ hc hp hp0 hpm).edges c+1 at this;omega
    simp only [physicalSignature,canonicalSignature,dif_pos hj]
    rw [label_eq_point n r p δ hc hp hp0 hpm c hpair ha0]
    rfl
  · intro j
    have hj : j.val<2*(n+2)-1 := by have:=j.isLt;change j.val<(layout n r p δ hc hp hp0 hpm).edges c at this;omega
    simp only [physicalSignature,canonicalSignature,dif_pos hj]
    rw [label_eq_point n r p δ hc hp hp0 hpm c hpair ha0,
      label_eq_point n r p δ hc hp hp0 hpm c hpair ha0]
    rfl

theorem physicalSignature_delta_one (n r p cap : ℕ) (hr : 0<r)
    (hc : Nat.Coprime 1 (n+2)) (hp : p=r+g*1)
    (hp0 : 0<p) (hpm : p<g*(n+2)) (c : Fin (count (g:=g) r))
    (hpair : representative r c≠mate r (representative r c))
    (ha0 : representative r c≠0) :
    physicalSignature (layout n r p 1 hc hp hp0 hpm) r p cap c=
      deltaOneSignature n cap (cut g (representative r c).val r) := by
  rw [physicalSignature_eq_canonical n r p 1 cap hc hp hp0 hpm c hpair ha0]
  exact canonicalSignature_delta_one n r p cap hr hp hpm hc
    (representative r c) (representative_le r c) ha0 hpair

#print axioms physicalSignature_eq_canonical
#print axioms physicalSignature_delta_one
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionPairedPhysicalLabels

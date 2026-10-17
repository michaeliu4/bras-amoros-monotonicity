import Results.Genus.RawGraph.PackedAcceptance.ReflectionZeroPairedPhysical
import Results.Genus.RawGraph.PackedAcceptance.ReflectionZeroPairedWord
import Results.Genus.RawGraph.SignatureCheck

/-! The actual zero-paired raw component retains two pinned pivots. All five
signature fields, including its open flag and unused closing field, are exact. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionZeroPaired
open LayoutCompiler SourceModel ReflectionPairedOrbit ReflectionFullLayout
variable {g : ℕ} [NeZero g]

theorem physicalSignature_eq_raw (n r p δ cap : ℕ)
    (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ)
    (hp0 : 0<p) (hpm : p<g*(n+2)) (c : Fin (count (g:=g) r))
    (hz : representative r c=0) (hpair : (0:Fin g)≠mate r 0) :
    physicalSignature (layout n r p δ hc hp hp0 hpm) r p cap c=
      rawSignature n r p δ cap hc hpair := by
  have he:=zero_edges n r p δ hc hp hp0 hpm c hz hpair
  apply sameSignature_sound
  refine ⟨he,zero_cycle n r p δ hc hp hp0 hpm c hz hpair,?_,?_,?_⟩
  · change edgeBound r p cap _ _=0
    rw [label_eq_zero_point n r p δ hc hp hp0 hpm c hz hpair,
      label_eq_zero_point n r p δ hc hp hp0 hpm c hz hpair]
    have hl : zeroIndex n r p δ hc hp hp0 hpm c hz hpair
        (Fin.last ((layout n r p δ hc hp hp0 hpm).edges c))=
        Fin.last (2*n+2) := Fin.ext he
    rw [hl]
    have hi : IsPivot r p (point n r δ hc hpair (Fin.last (2*n+2))) :=
      Or.inr (last_physical n r p δ hp hc hpair hpm)
    simp only [edgeBound,hi,true_or,↓reduceIte]
  · intro j v
    have hj : j.val<2*n+2+1 := by
      have:=j.isLt
      change j.val<(layout n r p δ hc hp hp0 hpm).edges c+1 at this
      omega
    simp only [physicalSignature,rawSignature,dif_pos hj]
    rw [label_eq_zero_point n r p δ hc hp hp0 hpm c hz hpair]
    rfl
  · intro j
    have hj : j.val<2*n+2 := by
      have:=j.isLt
      change j.val<(layout n r p δ hc hp hp0 hpm).edges c at this
      omega
    simp only [physicalSignature,rawSignature,dif_pos hj]
    rw [label_eq_zero_point n r p δ hc hp hp0 hpm c hz hpair,
      label_eq_zero_point n r p δ hc hp hp0 hpm c hz hpair]
    rfl

theorem scalarComponent_eq_pinned_free {R : Type*} [CommSemiring R]
    (n r p δ cap : ℕ) (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ)
    (hp0 : 0<p) (hpm : p<g*(n+2)) (c : Fin (count (g:=g) r))
    (hz : representative r c=0) (hpair : (0:Fin g)≠mate r 0) (z : R) :
    scalarComponent (layout n r p δ hc hp hp0 hpm) r p cap z c=
      z^(2*cap)*signatureScalar (freeSignature n r p δ cap hp hc hpair) z := by
  rw [scalarComponent_eq_signature,
    physicalSignature_eq_raw n r p δ cap hc hp hp0 hpm c hz hpair]
  exact rawScalar_eq_pinned_free n r p δ cap hp hc hpair (by omega) hpm z

#print axioms physicalSignature_eq_raw
#print axioms scalarComponent_eq_pinned_free
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionZeroPaired

import Results.Genus.RawGraph.PackedAcceptance.ReflectionZeroPairedEndpoints
import Results.Genus.RawGraph.PackedAcceptance.CompressedSignature

namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionZeroPaired
open SourceModel LayoutCompiler ReflectionPairedOrbit CompressedSignature
variable {g : ℕ} [NeZero g]

def rawSignature (n r p δ cap : ℕ) (hc : Nat.Coprime δ (n+2))
    (hpair : (0:Fin g)≠mate r 0) : ComponentSignature cap where
  edges := 2*n+2
  mask j v := decide (Domain r p cap (point n r δ hc hpair j) v.val)
  bound j := edgeBound r p cap (point n r δ hc hpair j.castSucc) (point n r δ hc hpair j.succ)
  cycle := false
  close := 0

def freeSignature (n r p δ cap : ℕ) (hp : p=r+g*δ) (hc : Nat.Coprime δ (n+2))
    (hpair : (0:Fin g)≠mate r 0) : ComponentSignature cap where
  edges := 2*n
  mask j v := decide (Domain r p cap (freePoint n r p δ hp hc hpair j).val v.val)
  bound j := edgeBound r p cap (freePoint n r p δ hp hc hpair j.castSucc).val
    (freePoint n r p δ hp hc hpair j.succ).val
  cycle := false
  close := 0

lemma first_step (n r p δ cap : ℕ) (hc : Nat.Coprime δ (n+2))
    (hpair : (0:Fin g)≠mate r 0) (hrm : r<g*(n+2)) :
    (⟨(rawSignature n r p δ cap hc hpair).mask (0:Fin (2*n+3)),
      (rawSignature n r p δ cap hc hpair).bound (0:Fin (2*n+2))⟩ : Step (cap+1))=
      ⟨(fun v=>decide (v.val=cap)),0⟩ := by
  change Step.mk _ (edgeBound r p cap (point n r δ hc hpair 0) _)=_
  rw [first_edge_zero n r p δ cap hc hpair hrm]
  congr 1
  funext v
  change decide (Domain r p cap (point n r δ hc hpair 0) v.val)=_
  simp only [first_domain n r p δ cap hc hpair hrm v.val]

lemma middle_step (n r p δ cap : ℕ) (hp : p=r+g*δ) (hc : Nat.Coprime δ (n+2))
    (hpair : (0:Fin g)≠mate r 0) (j : Fin (2*n)) :
    (⟨(rawSignature n r p δ cap hc hpair).mask ⟨j.val+1,by change j.val+1<2*n+3;have:=j.isLt;omega⟩,
      (rawSignature n r p δ cap hc hpair).bound ⟨j.val+1,by change j.val+1<2*n+2;have:=j.isLt;omega⟩⟩ : Step (cap+1))=
      ⟨(freeSignature n r p δ cap hp hc hpair).mask j.castSucc,
        (freeSignature n r p δ cap hp hc hpair).bound j⟩ := by
  rfl

lemma last_step (n r p δ cap : ℕ) (hp : p=r+g*δ) (hc : Nat.Coprime δ (n+2))
    (hpair : (0:Fin g)≠mate r 0) (hpm : p<g*(n+2)) :
    (⟨(rawSignature n r p δ cap hc hpair).mask (Fin.last (2*n+1)).castSucc,
      (rawSignature n r p δ cap hc hpair).bound (Fin.last (2*n+1))⟩ : Step (cap+1))=
      ⟨(freeSignature n r p δ cap hp hc hpair).mask (Fin.last (2*n)),0⟩ := by
  change Step.mk _ (edgeBound r p cap _ (point n r δ hc hpair (Fin.last (2*n+2))))=_
  rw [last_edge_zero n r p δ cap hp hc hpair hpm]
  rfl

lemma terminal_pin (n r p δ cap : ℕ) (hp : p=r+g*δ) (hc : Nat.Coprime δ (n+2))
    (hpair : (0:Fin g)≠mate r 0) (hpm : p<g*(n+2)) :
    (rawSignature n r p δ cap hc hpair).mask (Fin.last (2*n+2))=(fun v=>decide (v.val=cap)) := by
  funext v
  change decide (Domain r p cap (point n r δ hc hpair (Fin.last (2*n+2))) v.val)=_
  simp only [last_domain n r p δ cap hp hc hpair hpm v.val]

#print axioms first_step
#print axioms middle_step
#print axioms last_step
#print axioms terminal_pin
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionZeroPaired

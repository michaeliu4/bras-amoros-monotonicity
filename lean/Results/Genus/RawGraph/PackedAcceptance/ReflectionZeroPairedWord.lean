import Results.Genus.RawGraph.PackedAcceptance.ReflectionZeroPairedSignatures
import Results.Genus.RawGraph.PackedAcceptance.PinnedPathEndpoints

namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionZeroPaired
open SourceModel LayoutCompiler ReflectionPairedOrbit CompressedSignature PinnedPathEndpoints

lemma ofFn_borders {A : Type*} (N : ℕ) (f : Fin (N+2)→A) (inside : Fin N→A)
    (left right : A) (hfirst : f 0=left) (hlast : f (Fin.last (N+1))=right)
    (hmiddle : ∀i,f ⟨i.val+1,by have:=i.isLt;omega⟩=inside i) :
    List.ofFn f=[left] ++ List.ofFn inside ++ [right] := by
  rw [List.ofFn_succ,List.ofFn_succ_last,hfirst]
  have hm : (fun i:Fin N=>f i.castSucc.succ)=inside := by
    funext i
    exact hmiddle i
  rw [hm,Fin.succ_last,hlast]
  rfl

variable {g : ℕ} [NeZero g]

theorem sourceSteps_pinned (n r p δ cap : ℕ) (hp : p=r+g*δ) (hc : Nat.Coprime δ (n+2))
    (hpair : (0:Fin g)≠mate r 0) (hrm : r<g*(n+2)) (hpm : p<g*(n+2)) :
    sourceSteps (rawSignature n r p δ cap hc hpair)=
      [pinStep cap] ++ sourceSteps (freeSignature n r p δ cap hp hc hpair) ++
      [openTerminalStep (freeSignature n r p δ cap hp hc hpair)] := by
  apply ofFn_borders (2*n)
  · have h0 : (0:Fin (2*n+2)).castSucc=(0:Fin (2*n+3)) := by apply Fin.ext;simp
    change (⟨(rawSignature n r p δ cap hc hpair).mask (0:Fin (2*n+2)).castSucc,
      (rawSignature n r p δ cap hc hpair).bound (0:Fin (2*n+2))⟩:Step (cap+1))=pinStep cap
    rw [h0]
    simpa only [pinStep,Fin.ext_iff,Fin.val_last] using first_step n r p δ cap hc hpair hrm
  · exact last_step n r p δ cap hp hc hpair hpm
  · intro j
    exact middle_step n r p δ cap hp hc hpair j

theorem rawScalar_eq_pinned_free {R : Type*} [CommSemiring R]
    (n r p δ cap : ℕ) (hp : p=r+g*δ) (hc : Nat.Coprime δ (n+2))
    (hpair : (0:Fin g)≠mate r 0) (hrm : r<g*(n+2)) (hpm : p<g*(n+2)) (z : R) :
    signatureScalar (rawSignature n r p δ cap hc hpair) z=
      z^(2*cap)*signatureScalar (freeSignature n r p δ cap hp hc hpair) z := by
  apply strip_endpoints _ _ rfl rfl (sourceSteps_pinned n r p δ cap hp hc hpair hrm hpm) _ z
  intro v
  have h:=congrFun (terminal_pin n r p δ cap hp hc hpair hpm) v
  simpa only [rawSignature,Fin.ext_iff,Fin.val_last] using h

#print axioms ofFn_borders
#print axioms sourceSteps_pinned
#print axioms rawScalar_eq_pinned_free
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionZeroPaired

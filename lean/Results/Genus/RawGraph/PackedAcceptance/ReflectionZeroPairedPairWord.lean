import Results.Genus.RawGraph.PackedAcceptance.ReflectionZeroPairedLetters
import Results.Genus.RawGraph.PackedAcceptance.ReflectionChunkClosure

namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionZeroPaired
open SourceModel ReflectionPairedOrbit ReflectionThresholdWord CompressedSignature
open CapFourMass SignedReflectionFreeBlock SignedReflectionZeroPaired
variable {g : ℕ} [NeZero g]

def letterSteps (cap : ℕ) (q : Letter) : List (Step (cap+1)) :=
  [⟨mask cap q,evenBound cap q⟩,⟨mask cap q,oddBound cap q⟩]

theorem free_sourceSteps (n r p δ cap : ℕ) (hr : 0<r) (hδ : 0<δ)
    (hp : p=r+g*δ) (hpm : p<g*(n+2)) (hc : Nat.Coprime δ (n+2))
    (hpair : (0:Fin g)≠mate r 0) :
    sourceSteps (freeSignature n r p δ cap hp hc hpair)=
      (List.ofFn (fun j:Fin n=>letterSteps cap
        (letter (g*(n+2)) r (g*δ) (g*((δ*(j.val+1))%(n+2)))))).flatten := by
  unfold sourceSteps
  change List.ofFn (fun j:Fin (2*n)=> _)=_
  rw [List.ofFn_mul']
  congr 1
  apply congrArg List.ofFn
  funext j
  have h:=free_source_letter n r p δ cap hr hδ hp hpm hc hpair j
  dsimp only at h
  simp only [List.ofFn_succ,List.ofFn_zero]
  unfold letterSteps
  congr 1
  · congr 1
    · funext v
      exact (h.1 v).1
    · exact h.2.1
  · congr 1
    congr 1
    · funext v
      exact (h.1 v).2
    · exact h.2.2

/-- The last free vertex is the excluded return-to-zero boundary. Its mask
is retained, but it contributes no outgoing pair or artificial closure. -/
theorem free_terminal_mask (n r p δ cap : ℕ) (hδ : 0<δ)
    (hp : p=r+g*δ) (hpm : p<g*(n+2)) (hc : Nat.Coprime δ (n+2))
    (hpair : (0:Fin g)≠mate r 0) :
    (freeSignature n r p δ cap hp hc hpair).mask (Fin.last (2*n))=mask cap .carryCarry := by
  let T:=residueEquiv n r p δ hp hpair hc (Fin.last (2*n))
  have hi : trimIndex n (Fin.last (2*n))=
      (parityEquiv (n+2)).symm (false,(⟨n+1,by omega⟩:Fin (n+2))) := by
    apply Fin.ext
    change 2*n+2=2*(n+1)
    omega
  have ht : T.val.val=(canonicalOrder r (0:Fin g) hpair δ hc
      ((parityEquiv (n+2)).symm (false,(⟨n+1,by omega⟩:Fin (n+2))))).val := by
    dsimp only [T]
    rw [residueEquiv_value,hi]
  have hdL : δ<n+2 := Nat.lt_of_mul_lt_mul_left (by omega : g*δ<g*(n+2))
  have hv : T.val.val.val=g*((n+2)-δ) := by
    rw [ht,canonicalOrder_even]
    simp only [Fin.val_zero,zero_add]
    rw [show n+1=(n+2)-1 by omega,final_modular_coordinate (n+2) δ hδ hdL]
  have hr : ¬T.val.val.val<r := by
    rw [hv,Nat.mul_sub_left_distrib]
    omega
  funext v
  change decide (Domain r p cap (vertex n r p 0 T).val v.val)=_
  simp only [ReflectionFreeThreshold.vertex_domain n r p δ cap hp 0 hpair T,
    hr,↓reduceIte,mask,reduceCtorEq]

#print axioms free_sourceSteps
#print axioms free_terminal_mask
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionZeroPaired

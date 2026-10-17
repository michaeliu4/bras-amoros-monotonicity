import Results.Genus.RawGraph.PackedAcceptance.ReflectionPairedPhysicalSignature
import Results.Genus.RawGraph.PackedAcceptance.ReflectionChunkWord

/-! A source-exact normalized paired signature for every reduced gap. It
retains alternating edge phases and the actual last-to-first threshold. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord
open SourceModel ReflectionPairedOrbit
open CapFourMass.SignedReflectionPaired
variable {g : ℕ} [NeZero g]

def normalizedSignature (n δ cap q : ℕ) : ComponentSignature cap where
  edges := 2*(n+2)-1
  mask j := mask cap (reducedLetter (n+2) δ q ((δ*(j.val/2))%(n+2)))
  bound j := if j.val%2=0 then evenBound cap (reducedLetter (n+2) δ q ((δ*(j.val/2))%(n+2)))
    else oddBound cap (reducedLetter (n+2) δ q ((δ*(j.val/2))%(n+2)))
  cycle := true
  close := oddBound cap (reducedLetter (n+2) δ q ((δ*(n+1))%(n+2)))

lemma source_mask_normalized (n r p δ cap : ℕ) (hr : 0<r) (hδ : 0<δ)
    (hp : p=r+g*δ) (hpm : p<g*(n+2)) (hc : Nat.Coprime δ (n+2))
    (a : Fin g) (ha : a≤mate r a) (ha0 : a≠0) (hpair : a≠mate r a)
    (j : Fin (2*(n+2))) (i : Fin (cap+1)) :
    decide (Domain r p cap (point n r p δ hp hc a ha ha0 hpair j).val i.val)=
      mask cap (reducedLetter (n+2) δ (cut g a.val r) ((δ*(j.val/2))%(n+2))) i := by
  obtain ⟨⟨b,k⟩,rfl⟩ := (parityEquiv (n+2)).symm.surjective j
  have h:=paired_source_letter n r p δ cap hr hδ hp hpm hc a ha ha0 hpair k
  dsimp only at h
  cases b
  · rw [(h.1 i).1]
    change mask cap _ i=mask cap (reducedLetter (n+2) δ (cut g a.val r) ((δ*((2*k.val)/2))%(n+2))) i
    rw [show (2*k.val)/2=k.val by omega]
    exact congrArg (fun t=>mask cap t i) (affine_letter_reduced g (n+2) r δ a.val _ (NeZero.pos g) a.isLt)
  · rw [(h.1 i).2]
    change mask cap _ i=mask cap (reducedLetter (n+2) δ (cut g a.val r) ((δ*((2*k.val+1)/2))%(n+2))) i
    rw [show (2*k.val+1)/2=k.val by omega]
    exact congrArg (fun t=>mask cap t i) (affine_letter_reduced g (n+2) r δ a.val _ (NeZero.pos g) a.isLt)

lemma source_edge_normalized (n r p δ cap : ℕ) (hr : 0<r) (hδ : 0<δ)
    (hp : p=r+g*δ) (hpm : p<g*(n+2)) (hc : Nat.Coprime δ (n+2))
    (a : Fin g) (ha : a≤mate r a) (ha0 : a≠0) (hpair : a≠mate r a)
    (j : Fin (2*(n+2)-1)) :
    edgeBound r p cap
      (point n r p δ hp hc a ha ha0 hpair ⟨j.val,by have:=j.isLt; omega⟩).val
      (point n r p δ hp hc a ha ha0 hpair ⟨j.val+1,by have:=j.isLt; omega⟩).val=
      if j.val%2=0 then evenBound cap (reducedLetter (n+2) δ (cut g a.val r) ((δ*(j.val/2))%(n+2)))
      else oddBound cap (reducedLetter (n+2) δ (cut g a.val r) ((δ*(j.val/2))%(n+2))) := by
  let k : Fin (n+2) := ⟨j.val/2,by have:=j.isLt; omega⟩
  have h:=paired_source_letter n r p δ cap hr hδ hp hpm hc a ha ha0 hpair k
  dsimp only at h
  have hl:=affine_letter_reduced g (n+2) r δ a.val ((δ*k.val)%(n+2)) (NeZero.pos g) a.isLt
  by_cases he : j.val%2=0
  · have hj : j.val=2*k.val := by dsimp [k]; omega
    have e1 : (⟨j.val,by have:=j.isLt; omega⟩:Fin (2*(n+2)))=(parityEquiv (n+2)).symm (false,k) := Fin.ext hj
    have e2 : (⟨j.val+1,by have:=j.isLt; omega⟩:Fin (2*(n+2)))=(parityEquiv (n+2)).symm (true,k) := Fin.ext (by simpa only [hj,parityEquiv_symm_odd])
    rw [e1,e2,h.2.1,if_pos he,hl]
    rfl
  · have hj : j.val=2*k.val+1 := by dsimp [k]; omega
    have hkl : k.val+1<n+2 := by have:=j.isLt; omega
    have e1 : (⟨j.val,by have:=j.isLt; omega⟩:Fin (2*(n+2)))=(parityEquiv (n+2)).symm (true,k) := Fin.ext hj
    have e2 : (⟨j.val+1,by have:=j.isLt; omega⟩:Fin (2*(n+2)))=(parityEquiv (n+2)).symm (false,next k) := by
      apply Fin.ext
      change j.val+1=2*((k.val+1)%(n+2))
      rw [Nat.mod_eq_of_lt hkl]
      omega
    rw [e1,e2,h.2.2,if_neg he,hl]
    rfl

lemma source_close_normalized (n r p δ cap : ℕ) (hr : 0<r) (hδ : 0<δ)
    (hp : p=r+g*δ) (hpm : p<g*(n+2)) (hc : Nat.Coprime δ (n+2))
    (a : Fin g) (ha : a≤mate r a) (ha0 : a≠0) (hpair : a≠mate r a) :
    edgeBound r p cap
      (point n r p δ hp hc a ha ha0 hpair ⟨2*(n+2)-1,by omega⟩).val
      (point n r p δ hp hc a ha ha0 hpair 0).val=
      oddBound cap (reducedLetter (n+2) δ (cut g a.val r) ((δ*(n+1))%(n+2))) := by
  let k : Fin (n+2) := ⟨n+1,by omega⟩
  have h:=paired_source_letter n r p δ cap hr hδ hp hpm hc a ha ha0 hpair k
  dsimp only at h
  have e1 : (⟨2*(n+2)-1,by omega⟩:Fin (2*(n+2)))=(parityEquiv (n+2)).symm (true,k) := by
    apply Fin.ext
    change 2*(n+2)-1=2*(n+1)+1
    omega
  have e2 : (0:Fin (2*(n+2)))=(parityEquiv (n+2)).symm (false,next k) := by
    apply Fin.ext
    change 0=2*(((n+1)+1)%(n+2))
    simp [Nat.add_assoc]
  rw [e1,e2,h.2.2]
  exact congrArg (oddBound cap) (affine_letter_reduced g (n+2) r δ a.val _ (NeZero.pos g) a.isLt)

theorem canonicalSignature_normalized (n r p δ cap : ℕ) (hr : 0<r) (hδ : 0<δ)
    (hp : p=r+g*δ) (hpm : p<g*(n+2)) (hc : Nat.Coprime δ (n+2))
    (a : Fin g) (ha : a≤mate r a) (ha0 : a≠0) (hpair : a≠mate r a) :
    canonicalSignature n r p δ cap hp hc a ha ha0 hpair=
      normalizedSignature n δ cap (cut g a.val r) := by
  unfold canonicalSignature normalizedSignature
  congr 1
  · funext j i
    exact source_mask_normalized n r p δ cap hr hδ hp hpm hc a ha ha0 hpair _ i
  · funext j
    exact source_edge_normalized n r p δ cap hr hδ hp hpm hc a ha ha0 hpair j
  · exact source_close_normalized n r p δ cap hr hδ hp hpm hc a ha ha0 hpair

#print axioms canonicalSignature_normalized
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord

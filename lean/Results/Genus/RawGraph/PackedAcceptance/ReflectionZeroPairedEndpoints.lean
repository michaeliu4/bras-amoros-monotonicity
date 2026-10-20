import Results.Genus.RawGraph.PackedAcceptance.ReflectionPhysicalResidues
import Results.Genus.RawGraph.PackedAcceptance.Signatures
import Results.Genus.CapFourMass.SignedReflectionZeroPaired

/-! Raw zero-paired paths retain both pinned pivots. The free middle interval
is the independently proved signed/free order, without adding a closing edge. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionZeroPaired
open SourceModel LayoutCompiler ReflectionPairedOrbit
open CapFourMass
variable {g : ℕ} [NeZero g]

def point (n r δ : ℕ) (hc : Nat.Coprime δ (n+2))
    (hpair : (0:Fin g)≠mate r 0) (j : Fin (2*n+3)) : Fin (g*(n+2)-1) :=
  let x:=zeroDeletedOrder r hpair δ hc (⟨j.val,by have:=j.isLt;omega⟩:Fin (2*(n+2)-1))
  (ReflectionPhysicalResidues.equiv (g*(n+2))).symm ⟨x.val.val,x.property⟩

lemma point_physical (n r δ : ℕ) (hc : Nat.Coprime δ (n+2))
    (hpair : (0:Fin g)≠mate r 0) (j : Fin (2*n+3)) :
    physical (point n r δ hc hpair j)=
      (canonicalOrder r 0 hpair δ hc (⟨j.val+1,by have:=j.isLt;omega⟩:Fin (2*(n+2)))).val.val := by
  unfold point
  rw [ReflectionPhysicalResidues.equiv_symm_physical,zeroDeletedOrder_val]

lemma first_physical (n r δ : ℕ) (hc : Nat.Coprime δ (n+2))
    (hpair : (0:Fin g)≠mate r 0) (hrm : r<g*(n+2)) :
    physical (point n r δ hc hpair 0)=r := by
  rw [point_physical]
  change (canonicalOrder r 0 hpair δ hc (SignedReflectionZeroPaired.firstPivotIndex n)).val.val=r
  rw [SignedReflectionZeroPaired.order_first_pivot,ZMod.val_natCast,Nat.mod_eq_of_lt hrm]

lemma last_physical (n r p δ : ℕ) (hp : p=r+g*δ) (hc : Nat.Coprime δ (n+2))
    (hpair : (0:Fin g)≠mate r 0) (hpm : p<g*(n+2)) :
    physical (point n r δ hc hpair (Fin.last (2*n+2)))=p := by
  rw [point_physical]
  have hi : (⟨(Fin.last (2*n+2)).val+1,by omega⟩:Fin (2*(n+2)))=
      SignedReflectionZeroPaired.lastPivotIndex n := Fin.ext (by dsimp [SignedReflectionZeroPaired.lastPivotIndex];omega)
  rw [hi,SignedReflectionZeroPaired.order_last_pivot n r p δ hp hpair hc,
    ZMod.val_natCast,Nat.mod_eq_of_lt hpm]

abbrev freePoint (n r p δ : ℕ) (hp : p=r+g*δ) (hc : Nat.Coprime δ (n+2))
    (hpair : (0:Fin g)≠mate r 0) (i : Fin (2*n+1)) :=
  SignedReflectionFreeBlock.vertex n r p 0
    (SignedReflectionZeroPaired.residueEquiv n r p δ hp hpair hc i)

/-- The literal middle labels agree, without permutation or reversal. -/
theorem middle_eq_free (n r p δ : ℕ) (hp : p=r+g*δ) (hc : Nat.Coprime δ (n+2))
    (hpair : (0:Fin g)≠mate r 0) (i : Fin (2*n+1)) :
    point n r δ hc hpair ⟨i.val+1,by have:=i.isLt;omega⟩=(freePoint n r p δ hp hc hpair i).val := by
  apply Fin.ext
  have h : physical (point n r δ hc hpair ⟨i.val+1,by have:=i.isLt;omega⟩)=
      physical (freePoint n r p δ hp hc hpair i).val := by
    rw [point_physical,SignedReflectionFreeBlock.physical_vertex,SignedReflectionZeroPaired.residueEquiv_value]
    rfl
  change (point n r δ hc hpair _).val+1=(freePoint n r p δ hp hc hpair i).val.val+1 at h
  omega

lemma first_domain (n r p δ cap : ℕ) (hc : Nat.Coprime δ (n+2))
    (hpair : (0:Fin g)≠mate r 0) (hrm : r<g*(n+2)) (v : ℕ) :
    Domain r p cap (point n r δ hc hpair 0) v ↔ v=cap := by
  have hi : IsPivot r p (point n r δ hc hpair 0) := Or.inl (first_physical n r δ hc hpair hrm)
  simp only [Domain,hi,true_implies,IsFree,not_true_eq_false,false_implies,and_true]

lemma last_domain (n r p δ cap : ℕ) (hp : p=r+g*δ) (hc : Nat.Coprime δ (n+2))
    (hpair : (0:Fin g)≠mate r 0) (hpm : p<g*(n+2)) (v : ℕ) :
    Domain r p cap (point n r δ hc hpair (Fin.last (2*n+2))) v ↔ v=cap := by
  have hi : IsPivot r p (point n r δ hc hpair (Fin.last (2*n+2))) := Or.inr (last_physical n r p δ hp hc hpair hpm)
  simp only [Domain,hi,true_implies,IsFree,not_true_eq_false,false_implies,and_true]

lemma first_edge_zero (n r p δ cap : ℕ) (hc : Nat.Coprime δ (n+2))
    (hpair : (0:Fin g)≠mate r 0) (hrm : r<g*(n+2)) (v : Fin (g*(n+2)-1)) :
    edgeBound r p cap (point n r δ hc hpair 0) v=0 := by
  have hi : IsPivot r p (point n r δ hc hpair 0) := Or.inl (first_physical n r δ hc hpair hrm)
  simp only [edgeBound,hi,true_or,↓reduceIte]

lemma last_edge_zero (n r p δ cap : ℕ) (hp : p=r+g*δ) (hc : Nat.Coprime δ (n+2))
    (hpair : (0:Fin g)≠mate r 0) (hpm : p<g*(n+2)) (v : Fin (g*(n+2)-1)) :
    edgeBound r p cap v (point n r δ hc hpair (Fin.last (2*n+2)))=0 := by
  have hi : IsPivot r p (point n r δ hc hpair (Fin.last (2*n+2))) := Or.inr (last_physical n r p δ hp hc hpair hpm)
  simp only [edgeBound,hi,true_or,or_true,↓reduceIte]

#print axioms point_physical
#print axioms first_physical
#print axioms last_physical
#print axioms middle_eq_free
#print axioms first_domain
#print axioms last_domain
#print axioms first_edge_zero
#print axioms last_edge_zero
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionZeroPaired

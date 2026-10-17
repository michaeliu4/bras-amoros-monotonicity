import Results.Genus.RawGraph.PackedAcceptance.ReflectionZeroPairedSignatures
import Results.Genus.RawGraph.PackedAcceptance.ReflectionFreeThreshold

namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionZeroPaired
open SourceModel ReflectionPairedOrbit ReflectionThresholdWord
open CapFourMass SignedReflectionFreeBlock SignedReflectionZeroPaired
variable {g : ℕ} [NeZero g]

def freeEven (n : ℕ) (j : Fin n) : Fin (2*n+1) := ⟨2*j.val,by have:=j.isLt;omega⟩
def freeOdd (n : ℕ) (j : Fin n) : Fin (2*n+1) := ⟨2*j.val+1,by have:=j.isLt;omega⟩
def freeNext (n : ℕ) (j : Fin n) : Fin (2*n+1) := ⟨2*j.val+2,by have:=j.isLt;omega⟩
def pairPosition (n : ℕ) (j : Fin n) : Fin (n+2) := ⟨j.val+1,by have:=j.isLt;omega⟩

lemma trim_free_even (n : ℕ) (j : Fin n) :
    trimIndex n (freeEven n j)=(parityEquiv (n+2)).symm (false,pairPosition n j) := by
  apply Fin.ext
  dsimp [trimIndex,freeEven,pairPosition]
  omega
lemma trim_free_odd (n : ℕ) (j : Fin n) :
    trimIndex n (freeOdd n j)=(parityEquiv (n+2)).symm (true,pairPosition n j) := by
  apply Fin.ext
  dsimp [trimIndex,freeOdd,pairPosition]
  omega
lemma trim_free_next (n : ℕ) (j : Fin n) :
    trimIndex n (freeNext n j)=(parityEquiv (n+2)).symm (false,next (pairPosition n j)) := by
  apply Fin.ext
  change 2*j.val+2+2=2*((j.val+1+1)%(n+2))
  rw [Nat.mod_eq_of_lt (by have:=j.isLt;omega)]
  omega

/-- Every interior pair uses two actual consecutive edges. The excluded
return-to-zero pair is not in Fin n and remains the terminal vertex only. -/
theorem free_source_letter (n r p δ cap : ℕ) (hr : 0<r) (hδ : 0<δ)
    (hp : p=r+g*δ) (hpm : p<g*(n+2)) (hc : Nat.Coprime δ (n+2))
    (hpair : (0:Fin g)≠mate r 0) (j : Fin n) :
    let q:=letter (g*(n+2)) r (g*δ) (g*((δ*(j.val+1))%(n+2)))
    (∀v : Fin (cap+1),decide (Domain r p cap (freePoint n r p δ hp hc hpair (freeEven n j)).val v.val)=mask cap q v ∧
      decide (Domain r p cap (freePoint n r p δ hp hc hpair (freeOdd n j)).val v.val)=mask cap q v) ∧
    edgeBound r p cap (freePoint n r p δ hp hc hpair (freeEven n j)).val
      (freePoint n r p δ hp hc hpair (freeOdd n j)).val=evenBound cap q ∧
    edgeBound r p cap (freePoint n r p δ hp hc hpair (freeOdd n j)).val
      (freePoint n r p δ hp hc hpair (freeNext n j)).val=oddBound cap q := by
  let E := canonicalOrder (L:=n+2) r 0 hpair δ hc
  let U := residueEquiv n r p δ hp hpair hc (freeEven n j)
  let V := residueEquiv n r p δ hp hpair hc (freeOdd n j)
  let W := residueEquiv n r p δ hp hpair hc (freeNext n j)
  have hU : U.val=E ((parityEquiv (n+2)).symm (false,pairPosition n j)) := by
    apply Subtype.ext
    change (residueEquiv n r p δ hp hpair hc (freeEven n j)).val.val=_
    rw [residueEquiv_value,trim_free_even]
  have hV : V.val=E ((parityEquiv (n+2)).symm (true,pairPosition n j)) := by
    apply Subtype.ext
    change (residueEquiv n r p δ hp hpair hc (freeOdd n j)).val.val=_
    rw [residueEquiv_value,trim_free_odd]
  have hW : W.val=E ((parityEquiv (n+2)).symm (false,next (pairPosition n j))) := by
    apply Subtype.ext
    change (residueEquiv n r p δ hp hpair hc (freeNext n j)).val.val=_
    rw [residueEquiv_value,trim_free_next]
  have hu : U.val.val.val=g*((δ*(j.val+1))%(n+2)) := by
    rw [hU]
    simpa only [Fin.val_zero,zero_add,pairPosition] using
      canonicalOrder_even r (0:Fin g) hpair δ hc (pairPosition n j)
  have hxy : U.val.val.val+V.val.val.val=r ∨ U.val.val.val+V.val.val.val=g*(n+2)+r := by
    have hs : U.val.val+V.val.val=(r:ZMod (g*(n+2))) := by
      rw [hU,hV]
      exact canonicalOrder_even_odd_sum r (0:Fin g) hpair δ hc (pairPosition n j)
    have ht := (targetPair_iff_zmod (by omega : r<g*(n+2))
      (vertex n r p 0 U).val (vertex n r p 0 V).val).mpr
      (by simpa only [cast_physical_vertex] using hs)
    simpa only [TargetPair,physical_vertex] using ht
  have hz : W.val.val.val=(U.val.val.val+g*δ)%(g*(n+2)) := by
    have hs : W.val.val=U.val.val+((g*δ:ℕ):ZMod (g*(n+2))) := by
      rw [hW,hU]
      dsimp only [E,canonicalOrder]
      rw [order_even,order_even,orbit_next]
    calc
      W.val.val.val=(U.val.val+((g*δ:ℕ):ZMod (g*(n+2)))).val := congrArg ZMod.val hs
      _=_ := by
        conv_lhs => rw [←ZMod.natCast_zmod_val U.val.val]
        rw [←Nat.cast_add,ZMod.val_natCast]
  have hUV : (vertex n r p 0 U).val≠(vertex n r p 0 V).val := by
    intro he
    have h:=(residueEquiv n r p δ hp hpair hc).injective
      (vertex_injective n r p 0 (Subtype.ext he))
    have hv:=congrArg Fin.val h
    change 2*j.val=2*j.val+1 at hv
    omega
  have hVW : (vertex n r p 0 V).val≠(vertex n r p 0 W).val := by
    intro he
    have h:=(residueEquiv n r p δ hp hpair hc).injective
      (vertex_injective n r p 0 (Subtype.ext he))
    have hv:=congrArg Fin.val h
    change 2*j.val+1=2*j.val+2 at hv
    omega
  have h:=ReflectionFreeThreshold.source_letter n r p δ cap hr hδ hp hpm 0 hpair U V W hxy hz hUV hVW
  rw [hu] at h
  exact h

#print axioms free_source_letter
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionZeroPaired

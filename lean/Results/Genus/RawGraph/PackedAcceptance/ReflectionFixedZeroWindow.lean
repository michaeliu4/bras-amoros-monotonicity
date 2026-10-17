import Results.Genus.RawGraph.PackedAcceptance.ReflectionFixedZeroPhysical
import Results.Genus.RawGraph.PackedAcceptance.ReflectionFixedOrdinaryWord
import Results.Genus.CapFourMass.SignedReflectionZeroFixed

namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionFixedZeroWindow
open LayoutCompiler SourceModel ReflectionPairedOrbit ReflectionFullLayout
open ReflectionFixedOrbit ReflectionComponentOrders ReflectionFixedPhase ReflectionFixedSourceWindow
open ReflectionFixedZeroPhysical ReflectionFixedOrdinaryWord
variable {g : ℕ} [NeZero g]

lemma zeroIndex_value (n r p δ : ℕ) (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ)
    (hp0 : 0<p) (hpm : p<g*(n+2)) (hfix : (0:Fin g)=mate r 0) :
    (CapFourMass.SignedReflectionZeroFixed.zeroIndex n r δ hfix hc).val=
      targetIndex n r δ 0 hfix hc := by
  have he : CapFourMass.SignedReflectionZeroFixed.zeroIndex n r δ hfix hc=
      (zeroCut n (r:ZMod (g*(n+2))) p (fixed_origin n r 0 hfix) (gapUnit n δ hc)
        (gap_value n r p δ hc hp) (pivot_ne_zero n p hp0 hpm)).castSucc := by
    apply (CapFourMass.SignedReflectionZeroFixed.order n r δ hfix hc).injective
    apply Subtype.ext
    exact (CapFourMass.SignedReflectionZeroFixed.zero_value n r δ hfix hc).trans
      (order_zero_at n (r:ZMod (g*(n+2))) p (fixed_origin n r 0 hfix) (gapUnit n δ hc)
        (gap_value n r p δ hc hp) (pivot_ne_zero n p hp0 hpm)).symm
  exact congrArg Fin.val he

lemma target_interior (n r p δ : ℕ) (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ)
    (hr : 0<r) (hδ : 0<δ) (hp0 : 0<p) (hpm : p<g*(n+2))
    (hfix : (0:Fin g)=mate r 0) :
    1≤targetIndex n r δ 0 hfix hc ∧ targetIndex n r δ 0 hfix hc≤n := by
  have hpos:=Nat.mul_pos (NeZero.pos g) hδ
  have hh:=CapFourMass.SignedReflectionZeroFixed.zero_interior n r p δ hp hr (by omega) hpm hfix hc
  rw [zeroIndex_value n r p δ hc hp hp0 hpm hfix] at hh
  omega

lemma originalIndex_before (n r p δ : ℕ) (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ)
    (hp0 : 0<p) (hpm : p<g*(n+2)) (hfix : (0:Fin g)=mate r 0)
    (j : Fin (n+1)) (hj : j.val<targetIndex n r δ 0 hfix hc) :
    originalIndex n r p δ hc hp hp0 hpm hfix j=j.castSucc := by
  exact Fin.succAbove_of_castSucc_lt _ _ hj

lemma originalIndex_after (n r p δ : ℕ) (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ)
    (hp0 : 0<p) (hpm : p<g*(n+2)) (hfix : (0:Fin g)=mate r 0)
    (j : Fin (n+1)) (hj : targetIndex n r δ 0 hfix hc≤j.val) :
    originalIndex n r p δ hc hp hp0 hpm hfix j=j.succ := by
  exact Fin.succAbove_of_le_castSucc _ _ hj

lemma keep_of_outside (n r p δ : ℕ) (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ)
    (hr : 0<r) (hδ : 0<δ) (hp0 : 0<p) (hpm : p<g*(n+2))
    (hfix : (0:Fin g)=mate r 0) (i : Fin (n+2))
    (hi : i.val+1<targetIndex n r δ 0 hfix hc ∨ targetIndex n r δ 0 hfix hc+1 < i.val) :
    CapFourMass.SignedReflectionFreeBlock.Keep n r p
      (CapFourMass.SignedReflectionZeroFixed.order n r δ hfix hc i) := by
  have hpos:=Nat.mul_pos (NeZero.pos g) hδ
  apply (CapFourMass.SignedReflectionZeroFixed.keep_iff n r p δ hp hr (by omega) hpm hfix hc i).mp
  rwa [zeroIndex_value n r p δ hc hp hp0 hpm hfix]

lemma point_free (n r p δ : ℕ) (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ)
    (hr : 0<r) (hδ : 0<δ) (hp0 : 0<p) (hpm : p<g*(n+2))
    (hfix : (0:Fin g)=mate r 0) (i : Fin (n+2))
    (hi : i.val+1<targetIndex n r δ 0 hfix hc ∨ targetIndex n r δ 0 hfix hc+1 < i.val)
    (hi0 : residue n r δ 0 hfix hc i≠0) : IsFree r p (point n r δ 0 hfix hc i hi0) := by
  exact (CapFourMass.SignedReflectionFreeBlock.vertex n r p 0
    ⟨CapFourMass.SignedReflectionZeroFixed.order n r δ hfix hc i,
      keep_of_outside n r p δ hc hp hr hδ hp0 hpm hfix i hi⟩).property

#print axioms target_interior
#print axioms point_free
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionFixedZeroWindow

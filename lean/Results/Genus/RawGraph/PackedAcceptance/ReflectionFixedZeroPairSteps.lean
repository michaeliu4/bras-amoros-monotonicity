import Results.Genus.RawGraph.PackedAcceptance.ReflectionFixedZeroWindow
import Results.Genus.RawGraph.PackedAcceptance.ReflectionFixedZeroPartition

namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionFixedZeroWindow
open LayoutCompiler SourceModel ReflectionPairedOrbit ReflectionFullLayout
open ReflectionFixedOrbit ReflectionComponentOrders ReflectionFixedPhase ReflectionFixedSourceWindow
open ReflectionFixedZeroPhysical ReflectionFixedOrdinaryWord ReflectionFixedZeroPartition ReflectionThresholdWord
variable {g : ℕ} [NeZero g]

/-- A zero-deleted raw pair is a threshold letter only when its three full
source positions are consecutive, outside both pivots, and nonterminal. -/
theorem raw_pair_steps (n r p δ cap : ℕ) (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ)
    (hr : 0<r) (hδ : 0<δ) (hp0 : 0<p) (hpm : p<g*(n+2)) (hfix : (0:Fin g)=mate r 0)
    (j k shift : ℕ) (hj : j+2<n+1)
    (hi0 : (originalIndex n r p δ hc hp hp0 hpm hfix ⟨j,by omega⟩).val=j+shift)
    (hi1 : (originalIndex n r p δ hc hp hp0 hpm hfix ⟨j+1,by omega⟩).val=j+shift+1)
    (hi2 : (originalIndex n r p δ hc hp hp0 hpm hfix ⟨j+2,hj⟩).val=j+shift+2)
    (halign : j+shift=alignment (targetIndex n r δ 0 hfix hc)+2*k)
    (hpos : 0<j+shift)
    (hout : j+shift+3<targetIndex n r δ 0 hfix hc ∨ targetIndex n r δ 0 hfix hc+1<j+shift) :
    [stepAt (signature n r p δ cap hc hp hp0 hpm hfix) j,
      stepAt (signature n r p δ cap hc hp hp0 hpm hfix) (j+1)]=
      pairSteps cap (letter (g*(n+2)) r (g*δ)
        (g*((startPhase n δ (targetIndex n r δ 0 hfix hc)+δ*k)%(n+2)))) := by
  let i:=originalIndex n r p δ hc hp hp0 hpm hfix ⟨j,by omega⟩
  let v:=originalIndex n r p δ hc hp hp0 hpm hfix ⟨j+1,by omega⟩
  let w:=originalIndex n r p δ hc hp hp0 hpm hfix ⟨j+2,hj⟩
  have hi : i.val=j+shift := hi0
  have hv : v.val=j+shift+1 := hi1
  have hw : w.val=j+shift+2 := hi2
  have hwi:=w.isLt
  have hiZ : residue n r δ 0 hfix hc i≠0 := (zeroOrder n r p δ hc hp hp0 hpm hfix ⟨j,by omega⟩).property
  have hvZ : residue n r δ 0 hfix hc v≠0 := (zeroOrder n r p δ hc hp hp0 hpm hfix ⟨j+1,by omega⟩).property
  have hwZ : residue n r δ 0 hfix hc w≠0 := (zeroOrder n r p δ hc hp hp0 hpm hfix ⟨j+2,hj⟩).property
  have hif:=point_free n r p δ hc hp hr hδ hp0 hpm hfix i (by omega) hiZ
  have hvf:=point_free n r p δ hc hp hr hδ hp0 hpm hfix v (by omega) hvZ
  have hwf:=point_free n r p δ hc hp hr hδ hp0 hpm hfix w (by omega) hwZ
  have ht:=aligned_source_letter n r p δ cap hr hδ hp hpm 0 hfix hc k i v w
    (by omega) (by omega) (by omega) hiZ hvZ hwZ hif hvf hwf
  simp only [Fin.val_zero,Nat.zero_add] at ht
  have hei : ¬endpoint n i := by unfold endpoint;omega
  have hev : ¬endpoint n v := by unfold endpoint;omega
  have hmi (a : Fin (cap+1)) := (domain_mask n r p δ cap hp hpm 0 hfix hc i hiZ a).symm.trans
    (ht.2.2 hei hev a).1
  have hmv (a : Fin (cap+1)) := (domain_mask n r p δ cap hp hpm 0 hfix hc v hvZ a).symm.trans
    (ht.2.2 hei hev a).2
  have hj0 : j<n := by omega
  have hj1 : j+1<n := by omega
  simp only [stepAt,signature,dif_pos hj0,dif_pos hj1,pairSteps]
  congr 2
  · exact funext hmi
  · exact ht.1
  · congr 1
    · exact funext hmv
    · exact ht.2.1

lemma left_pair_steps (n r p δ cap : ℕ) (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ)
    (hr : 0<r) (hδ : 0<δ) (hp0 : 0<p) (hpm : p<g*(n+2)) (hfix : (0:Fin g)=mate r 0)
    (k : ℕ) (hk : k<leftPairs (targetIndex n r δ 0 hfix hc)) :
    let h:=targetIndex n r δ 0 hfix hc
    let s:=signature n r p δ cap hc hp hp0 hpm hfix
    [stepAt s (leftHead h+2*k),stepAt s (leftHead h+2*k+1)]=
      pairSteps cap (letter (g*(n+2)) r (g*δ)
        (g*((startPhase n δ h+δ*(leftOffset h+k))%(n+2)))) := by
  dsimp only
  let h:=targetIndex n r δ 0 hfix hc
  have hb:=target_interior n r p δ hc hp hr hδ hp0 hpm hfix
  have hl:=left_positions h k hk
  refine raw_pair_steps n r p δ cap hc hp hr hδ hp0 hpm hfix
    (leftHead h+2*k) (leftOffset h+k) 0 (by omega) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [originalIndex_before n r p δ hc hp hp0 hpm hfix _ (by dsimp;omega)];rfl
  · rw [originalIndex_before n r p δ hc hp hp0 hpm hfix _ (by dsimp;omega)];rfl
  · rw [originalIndex_before n r p δ hc hp hp0 hpm hfix _ (by dsimp;omega)];rfl
  · simpa only [Nat.add_zero] using hl.1
  · omega
  · exact Or.inl (by omega)

lemma right_pair_steps (n r p δ cap : ℕ) (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ)
    (hr : 0<r) (hδ : 0<δ) (hp0 : 0<p) (hpm : p<g*(n+2)) (hfix : (0:Fin g)=mate r 0)
    (k : ℕ) (hk : k<rightPairs n (targetIndex n r δ 0 hfix hc)) :
    let h:=targetIndex n r δ 0 hfix hc
    let s:=signature n r p δ cap hc hp hp0 hpm hfix
    [stepAt s (rightStart n h+2*k),stepAt s (rightStart n h+2*k+1)]=
      pairSteps cap (letter (g*(n+2)) r (g*δ)
        (g*((startPhase n δ h+δ*(rightOffset h+k))%(n+2)))) := by
  dsimp only
  let h:=targetIndex n r δ 0 hfix hc
  have hl:=right_positions n h k hk
  refine raw_pair_steps n r p δ cap hc hp hr hδ hp0 hpm hfix
    (rightStart n h+2*k) (rightOffset h+k) 1 (by omega) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [originalIndex_after n r p δ hc hp hp0 hpm hfix _ (by dsimp;omega)];rfl
  · rw [originalIndex_after n r p δ hc hp hp0 hpm hfix _ (by dsimp;omega)];rfl
  · rw [originalIndex_after n r p δ hc hp hp0 hpm hfix _ (by dsimp;omega)];rfl
  · simpa only [Nat.add_zero] using hl.1
  · omega
  · exact Or.inr (by omega)

#print axioms raw_pair_steps
#print axioms left_pair_steps
#print axioms right_pair_steps
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionFixedZeroWindow

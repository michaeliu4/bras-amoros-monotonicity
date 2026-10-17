import Results.Genus.RawGraph.PackedAcceptance.ReflectionFixedZeroPairSteps
import Results.Genus.RawGraph.PackedAcceptance.ReflectionFixedOrdinaryProduct

namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionFixedZeroWord
open LayoutCompiler SourceModel ReflectionPairedOrbit ReflectionFullLayout
open ReflectionFixedPhase ReflectionFixedSourceWindow ReflectionFixedZeroPhysical
open ReflectionFixedZeroPartition ReflectionFixedZeroWindow ReflectionThresholdWord CompressedSignature
open ReflectionFixedOrdinaryWord (stepAt pairSteps pairValue sourceSteps_eq_range)
variable {g : ℕ} [NeZero g]

def headSteps {cap : ℕ} (h : ℕ) (s : ComponentSignature cap) :=
  (List.range (leftHead h)).map (stepAt s)
def middleSteps {cap : ℕ} (n h : ℕ) (s : ComponentSignature cap) :=
  (List.range' (leftEnd h) (rightStart n h-leftEnd h)).map (stepAt s)
def tailSteps {cap : ℕ} (n h : ℕ) (s : ComponentSignature cap) :=
  (List.range' (rightEnd n h) (n-rightEnd n h)).map (stepAt s)
def orbitStart (n h offset : ℕ) := (h/2+1+offset)%(n+2)
def bodyWord (n δ q h offset count : ℕ) : List Letter :=
  (List.range count).map (fun k=>reducedLetter (n+2) δ q ((δ*(orbitStart n h offset+k))%(n+2)))

lemma orbit_coordinate (n δ h offset k : ℕ) :
    (startPhase n δ h+δ*(offset+k))%(n+2)=(δ*(orbitStart n h offset+k))%(n+2) := by
  have he : ((startPhase n δ h+δ*(offset+k):ℕ):ZMod (n+2))=
      ((δ*(orbitStart n h offset+k):ℕ):ZMod (n+2)) := by
    simp only [startPhase,orbitStart,Nat.cast_add,Nat.cast_mul,ZMod.natCast_mod,Nat.cast_one]
    ring
  simpa only [ZMod.val_natCast] using congrArg ZMod.val he

lemma zero_letter_reduced (n r δ h offset k : ℕ) :
    letter (g*(n+2)) r (g*δ) (g*((startPhase n δ h+δ*(offset+k))%(n+2)))=
      reducedLetter (n+2) δ (cut g 0 r) ((δ*(orbitStart n h offset+k))%(n+2)) := by
  have hh:=affine_letter_reduced g (n+2) r δ 0
    ((startPhase n δ h+δ*(offset+k))%(n+2)) (NeZero.pos g) (NeZero.pos g)
  simpa only [Nat.zero_add,orbit_coordinate,reducedLetter] using hh

lemma boundary_lengths {cap : ℕ} (n h : ℕ) (hh : h≤n) (s : ComponentSignature cap) :
    (headSteps h s).length≤2 ∧ (middleSteps n h s).length≤5 ∧ (tailSteps n h s).length≤1 := by
  have hb:=bounds n h hh
  simpa only [headSteps,middleSteps,tailSteps,List.length_map,List.length_range,List.length_range']
    using hb.2.2.2.2

/-- Source-exact zero-fixed ordinary word. Pins and the neutral gap remain
literal; only free interior factors enter the two shifted pair words. -/
theorem sourceSteps_word (n r p δ cap : ℕ) (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ)
    (hr : 0<r) (hδ : 0<δ) (hp0 : 0<p) (hpm : p<g*(n+2)) (hfix : (0:Fin g)=mate r 0) :
    let h:=targetIndex n r δ 0 hfix hc
    let s:=signature n r p δ cap hc hp hp0 hpm hfix
    sourceSteps s=headSteps h s ++
      (bodyWord n δ (cut g 0 r) h (leftOffset h) (leftPairs h)).flatMap (pairSteps cap) ++
      middleSteps n h s ++
      (bodyWord n δ (cut g 0 r) h (rightOffset h) (rightPairs n h)).flatMap (pairSteps cap) ++
      tailSteps n h s := by
  dsimp only
  let h:=targetIndex n r δ 0 hfix hc
  let s:=signature n r p δ cap hc hp hp0 hpm hfix
  have hh:=(target_interior n r p δ hc hp hr hδ hp0 hpm hfix).2
  have hL : (List.range (leftPairs h)).flatMap
      (fun k=>[stepAt s (leftHead h+2*k),stepAt s (leftHead h+2*k+1)])=
      (bodyWord n δ (cut g 0 r) h (leftOffset h) (leftPairs h)).flatMap (pairSteps cap) := by
    simp only [bodyWord,List.flatMap_map,Function.comp_def]
    apply List.flatMap_congr
    intro k hk
    rw [left_pair_steps n r p δ cap hc hp hr hδ hp0 hpm hfix k (List.mem_range.mp hk)]
    rw [zero_letter_reduced]
  have hR : (List.range (rightPairs n h)).flatMap
      (fun k=>[stepAt s (rightStart n h+2*k),stepAt s (rightStart n h+2*k+1)])=
      (bodyWord n δ (cut g 0 r) h (rightOffset h) (rightPairs n h)).flatMap (pairSteps cap) := by
    simp only [bodyWord,List.flatMap_map,Function.comp_def]
    apply List.flatMap_congr
    intro k hk
    rw [right_pair_steps n r p δ cap hc hp hr hδ hp0 hpm hfix k (List.mem_range.mp hk)]
    rw [zero_letter_reduced]
  rw [sourceSteps_eq_range]
  change (List.range n).map (stepAt s)=_
  rw [values n h hh,hL,hR]
  rfl

/-- Ordered product over an arbitrary monoid, retaining all three bounded
literal blocks in their original positions. -/
theorem sourceSteps_product {M : Type*} [Monoid M] (f : Step (cap+1)→M)
    (n r p δ : ℕ) (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ)
    (hr : 0<r) (hδ : 0<δ) (hp0 : 0<p) (hpm : p<g*(n+2)) (hfix : (0:Fin g)=mate r 0) :
    let h:=targetIndex n r δ 0 hfix hc
    let s:=signature n r p δ cap hc hp hp0 hpm hfix
    ((sourceSteps s).map f).prod=((headSteps h s).map f).prod *
      ((bodyWord n δ (cut g 0 r) h (leftOffset h) (leftPairs h)).map (pairValue f)).prod *
      ((middleSteps n h s).map f).prod *
      ((bodyWord n δ (cut g 0 r) h (rightOffset h) (rightPairs n h)).map (pairValue f)).prod *
      ((tailSteps n h s).map f).prod := by
  dsimp only
  rw [sourceSteps_word n r p δ cap hc hp hr hδ hp0 hpm hfix]
  simp [pairValue,List.map_append,List.prod_append,List.flatMap_def,List.prod_flatten,
    List.map_map,Function.comp_def,mul_assoc]
  all_goals rfl

#print axioms sourceSteps_word
#print axioms sourceSteps_product
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionFixedZeroWord

import Results.Genus.RawGraph.PackedAcceptance.ReflectionFixedOrdinaryPartition
import Results.Genus.RawGraph.PackedAcceptance.ReflectionFixedPairLetters
import Results.Genus.RawGraph.PackedAcceptance.ReflectionFixedPhysicalLabels
import Results.Genus.CapFourMass.SignedReflectionFixedSource

/-! Exact ordinary-step decomposition for a nonzero fixed raw path. Boundary
steps are literal source fields; only fully interior pairs use threshold letters. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionFixedOrdinaryWord
open LayoutCompiler SourceModel ReflectionPairedOrbit ReflectionFullLayout
open ReflectionFixedPhase ReflectionFixedSourceWindow ReflectionFixedPhysicalLabels
open ReflectionThresholdWord CompressedSignature
open scoped Matrix

/-- Total indexing is used only under the original source edge range. -/
def stepAt {cap : ℕ} (s : ComponentSignature cap) (j : ℕ) : Step (cap+1) :=
  if h:j<s.edges then ⟨s.mask ⟨j,by omega⟩,s.bound ⟨j,h⟩⟩ else ⟨fun _=>false,0⟩

lemma sourceSteps_eq_range {cap : ℕ} (s : ComponentSignature cap) :
    sourceSteps s=(List.range s.edges).map (stepAt s) := by
  apply List.ext_getElem
  · simp [sourceSteps]
  · intro j hj hj'
    have hj0 : j<s.edges := by simpa [sourceSteps] using hj
    simp only [sourceSteps,List.getElem_ofFn,List.getElem_map,List.getElem_range,stepAt,dif_pos hj0]
    rfl

/-- Both vertices and both outgoing original thresholds of a full pair. -/
def pairSteps (cap : ℕ) (q : Letter) : List (Step (cap+1)) :=
  [⟨ReflectionThresholdWord.mask cap q,evenBound cap q⟩,
   ⟨ReflectionThresholdWord.mask cap q,oddBound cap q⟩]

variable {g : ℕ} [NeZero g]

lemma fullPoint_free (n r p δ : ℕ) (hp : p=r+g*δ) (a : Fin g) (hfix : a=mate r a)
    (hc : Nat.Coprime δ (n+2)) (ha0 : a≠0) (i : Fin (n+2)) :
    IsFree r p (fullPoint n r δ a hfix hc ha0 i) := by
  change IsFree r p (CapFourMass.SignedReflectionPaired.vertex n r p δ hp a
    (le_of_eq hfix) ha0 (CapFourMass.SignedReflectionFixed.residueOrder n r a hfix δ hc i)).val
  exact (CapFourMass.SignedReflectionPaired.vertex n r p δ hp a
    (le_of_eq hfix) ha0 (CapFourMass.SignedReflectionFixed.residueOrder n r a hfix δ hc i)).property

/-- An interior pair is exactly the old two-step letter, with no finite
signature premise. The original loop endpoint and terminal are outside it. -/
lemma body_pair_steps (n r p δ cap : ℕ) (hr : 0<r) (hδ : 0<δ)
    (hp : p=r+g*δ) (hpm : p<g*(n+2)) (a : Fin g) (hfix : a=mate r a)
    (hc : Nat.Coprime δ (n+2)) (ha0 : a≠0) (k : ℕ)
    (hk : k<ordinaryPairs n (targetIndex n r δ a hfix hc)) :
    let h:=targetIndex n r δ a hfix hc
    let s:=signature n r p δ cap a hfix hc ha0
    [stepAt s (ordinaryHead n h+2*k),stepAt s (ordinaryHead n h+2*k+1)]=
      pairSteps cap (letter (g*(n+2)) r (g*δ)
        (a.val+g*((startPhase n δ h+δ*(ordinaryPairOffset h+k))%(n+2)))) := by
  dsimp only
  let h:=targetIndex n r δ a hfix hc
  have hh:=ordinary_pair_positions n h k hk
  let i : Fin (n+2) := ⟨ordinaryHead n h+2*k,by omega⟩
  let j : Fin (n+2) := ⟨ordinaryHead n h+2*k+1,by omega⟩
  let w : Fin (n+2) := ⟨ordinaryHead n h+2*k+2,hh.2.2.2⟩
  have hi : i.val=alignment h+2*(ordinaryPairOffset h+k) := hh.1
  have hj : j.val=alignment h+2*(ordinaryPairOffset h+k)+1 := by dsimp [j];omega
  have hw : w.val=alignment h+2*(ordinaryPairOffset h+k+1) := by dsimp [w];omega
  have hi0 : residue n r δ a hfix hc i≠0 := ReflectionComponentOrders.coset_nonzero n a ha0 _
  have hj0 : residue n r δ a hfix hc j≠0 := ReflectionComponentOrders.coset_nonzero n a ha0 _
  have hw0 : residue n r δ a hfix hc w≠0 := ReflectionComponentOrders.coset_nonzero n a ha0 _
  have ht:=aligned_source_letter n r p δ cap hr hδ hp hpm a hfix hc
    (ordinaryPairOffset h+k) i j w hi hj hw hi0 hj0 hw0
    (fullPoint_free n r p δ hp a hfix hc ha0 i)
    (fullPoint_free n r p δ hp a hfix hc ha0 j)
    (fullPoint_free n r p δ hp a hfix hc ha0 w)
  dsimp only at ht
  have hei : ¬endpoint n i := by unfold endpoint;dsimp [i];omega
  have hej : ¬endpoint n j := by unfold endpoint;dsimp [j];omega
  have hmi (v : Fin (cap+1)) := (domain_mask n r p δ cap hp hpm a hfix hc i hi0 v).symm.trans
    (ht.2.2 hei hej v).1
  have hmj (v : Fin (cap+1)) := (domain_mask n r p δ cap hp hpm a hfix hc j hj0 v).symm.trans
    (ht.2.2 hei hej v).2
  have hiB : ordinaryHead n h+2*k<n+1 := by omega
  have hjB : ordinaryHead n h+2*k+1<n+1 := hh.2.2.1
  change [stepAt (signature n r p δ cap a hfix hc ha0) (ordinaryHead n h+2*k),
    stepAt (signature n r p δ cap a hfix hc ha0) (ordinaryHead n h+2*k+1)]=_
  simp only [stepAt,signature,dif_pos hiB,dif_pos hjB,pairSteps]
  congr 2
  · exact funext hmi
  · exact ht.1
  · congr 1
    · exact funext hmj
    · exact ht.2.1

/-- All ordinary factors in original order: literal bounded head and tail,
with a single shifted prefix of threshold pairs in the middle. -/
theorem sourceSteps_partition (n r p δ cap : ℕ) (hr : 0<r) (hδ : 0<δ)
    (hp : p=r+g*δ) (hpm : p<g*(n+2)) (a : Fin g) (hfix : a=mate r a)
    (hc : Nat.Coprime δ (n+2)) (ha0 : a≠0) :
    let h:=targetIndex n r δ a hfix hc
    let s:=signature n r p δ cap a hfix hc ha0
    sourceSteps s=(List.range (ordinaryHead n h)).map (stepAt s) ++
      (List.range (ordinaryPairs n h)).flatMap (fun k=>pairSteps cap
        (letter (g*(n+2)) r (g*δ)
          (a.val+g*((startPhase n δ h+δ*(ordinaryPairOffset h+k))%(n+2))))) ++
      (List.range' (ordinaryTailStart n h) (n+1-ordinaryTailStart n h)).map (stepAt s) := by
  dsimp only
  rw [sourceSteps_eq_range]
  change (List.range (n+1)).map _=_
  rw [ordinary_values_partition]
  congr 1
  congr 1
  apply List.flatMap_congr
  intro k hk
  exact body_pair_steps n r p δ cap hr hδ hp hpm a hfix hc ha0 k (List.mem_range.mp hk)

/-- The affine shifted-prefix coordinate is an orbit-index offset, not a
rotation of the physical path or its endpoint masks. -/
def orbitStart (n h : ℕ) : ℕ := (h/2+1+ordinaryPairOffset h)%(n+2)

lemma orbitStart_coordinate (n δ h k : ℕ) :
    (startPhase n δ h+δ*(ordinaryPairOffset h+k))%(n+2)=
      (δ*(orbitStart n h+k))%(n+2) := by
  have he : ((startPhase n δ h+δ*(ordinaryPairOffset h+k):ℕ):ZMod (n+2))=
      ((δ*(orbitStart n h+k):ℕ):ZMod (n+2)) := by
    simp only [startPhase,orbitStart,Nat.cast_add,Nat.cast_mul,ZMod.natCast_mod,Nat.cast_one]
    ring
  simpa only [ZMod.val_natCast] using congrArg ZMod.val he

#print axioms fullPoint_free
#print axioms body_pair_steps
#print axioms sourceSteps_partition
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionFixedOrdinaryWord

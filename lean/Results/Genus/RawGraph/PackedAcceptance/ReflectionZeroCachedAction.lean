import Results.Genus.RawGraph.PackedAcceptance.CachedStepAction
import Results.Genus.RawGraph.PackedAcceptance.ReflectionFixedZeroWord
import Results.Genus.RawGraph.PackedAcceptance.ReflectionPPhaseDenseCache

/-! Source words from a three-letter mask/threshold dictionary plus current
bounded literal blocks. Geometry is evaluated only for the actual boundaries
and terminal, not separately for every state at every source position. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionZeroCachedAction
open CachedStepAction CompressedSignature ReflectionThresholdWord ReflectionFixedPhase
open ReflectionFixedZeroWord ReflectionFixedZeroPartition ReflectionFixedZeroPhysical
open ReflectionFixedOrdinaryWord (pairSteps)

/-- Six complete cached step records, stored once for the three letters. -/
def pairTable (cap : ℕ) : LetterTable (List (CachedStep (cap+1))) :=
  LetterTable.ofFn (fun a=>(pairSteps cap a).map cache)

def word {cap : ℕ} (n δ q h : ℕ) (s : ComponentSignature cap) : List (CachedStep (cap+1)) :=
  let table:=pairTable cap
  (headSteps h s).map cache ++
    (bodyWord n δ q h (leftOffset h) (leftPairs h)).flatMap table.lookup ++
    (middleSteps n h s).map cache ++
    (bodyWord n δ q h (rightOffset h) (rightPairs n h)).flatMap table.lookup ++
    (tailSteps n h s).map cache

variable {g : ℕ} [NeZero g]
open LayoutCompiler ReflectionPairedOrbit ReflectionFullLayout

/-- Every dictionary step is the actual source step, including both retained
pins, the zero gap and the literal unpaired head/middle/tail. -/
theorem word_eq (n r p δ cap : ℕ) (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ)
    (hr : 0<r) (hδ : 0<δ) (hp0 : 0<p) (hpm : p<g*(n+2)) (hfix : (0:Fin g)=mate r 0) :
    word n δ (cut g 0 r) (targetIndex n r δ 0 hfix hc)
      (signature n r p δ cap hc hp hp0 hpm hfix)=
      (sourceSteps (signature n r p δ cap hc hp hp0 hpm hfix)).map cache := by
  rw [sourceSteps_word n r p δ cap hc hp hr hδ hp0 hpm hfix]
  simp only [word,pairTable,LetterTable.lookup_ofFn,List.map_append,List.map_flatMap]

variable {R : Type*} [CommSemiring R]
theorem signature_value (n r p δ cap : ℕ) (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ)
    (hr : 0<r) (hδ : 0<δ) (hp0 : 0<p) (hpm : p<g*(n+2)) (hfix : (0:Fin g)=mate r 0) (z : R) :
    CachedStepAction.value (powers z)
      (word n δ (cut g 0 r) (targetIndex n r δ 0 hfix hc) (signature n r p δ cap hc hp hp0 hpm hfix))
      (cacheTerminal (signature n r p δ cap hc hp hp0 hpm hfix))=
      signatureScalar (signature n r p δ cap hc hp hp0 hpm hfix) z :=
  value_eq _ z _ (word_eq n r p δ cap hc hp hr hδ hp0 hpm hfix)

theorem original_value (n r p δ cap : ℕ) (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ)
    (hr : 0<r) (hδ : 0<δ) (hp0 : 0<p) (hpm : p<g*(n+2))
    (c : Fin (count (g:=g) r)) (hfix : representative r c=mate r (representative r c))
    (ha0 : representative r c=0) (z : R) :
    let hz : (0:Fin g)=mate r 0:=by simpa only [ha0] using hfix
    let s:=signature n r p δ cap hc hp hp0 hpm hz
    scalarComponent (layout n r p δ hc hp hp0 hpm) r p cap z c=
      CachedStepAction.value (powers z) (word n δ (cut g 0 r) (targetIndex n r δ 0 hz hc) s)
        (cacheTerminal s) := by
  dsimp only
  rw [scalarComponent_eq_signature,ReflectionFixedZeroPhysical.physicalSignature_eq
    n r p δ cap hc hp hp0 hpm c hfix ha0]
  exact (signature_value n r p δ cap hc hp hr hδ hp0 hpm _ z).symm

#print axioms word_eq
#print axioms signature_value
#print axioms original_value
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionZeroCachedAction

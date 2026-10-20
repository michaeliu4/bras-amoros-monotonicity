import Results.Genus.RawGraph.PackedAcceptance.ReflectionZeroCachedAction
import Results.Genus.RawGraph.PackedAcceptance.ReflectionFixedOrdinaryProduct
import Results.Genus.RawGraph.PackedAcceptance.ReflectionPairedPowerScalar
import Results.Genus.RawGraph.PackedAcceptance.ReflectionZeroPairedCompressed

/-! Cached direct words for the other three original component branches.
Each word uses only a three-letter dictionary and literal current boundaries. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionCachedBranches
open CachedStepAction CompressedSignature ReflectionThresholdWord
open LayoutCompiler ReflectionPairedOrbit ReflectionFullLayout ReflectionFixedPhase
variable {g : ℕ} [NeZero g]

namespace Fixed
open ReflectionFixedOrdinaryWord ReflectionFixedPhysicalLabels

def word (n r p d cap : ℕ) (a : Fin g) (hfix : a=mate r a)
    (hc : Nat.Coprime d (n+2)) (ha0 : a≠0) : List (CachedStep (cap+1)) :=
  let table:=ReflectionZeroCachedAction.pairTable cap
  (headSteps n r p d cap a hfix hc ha0).map cache ++
    (bodyWord n r d a hfix hc).flatMap table.lookup ++
    (tailSteps n r p d cap a hfix hc ha0).map cache

lemma word_eq (n r p d cap : ℕ) (hr : 0<r) (hd : 0<d)
    (hp : p=r+g*d) (hpm : p<g*(n+2)) (a : Fin g) (hfix : a=mate r a)
    (hc : Nat.Coprime d (n+2)) (ha0 : a≠0) :
    word n r p d cap a hfix hc ha0=
      (sourceSteps (signature n r p d cap a hfix hc ha0)).map cache := by
  rw [sourceSteps_word n r p d cap hr hd hp hpm a hfix hc ha0]
  simp only [word,ReflectionZeroCachedAction.pairTable,LetterTable.lookup_ofFn,
    List.map_append,List.map_flatMap]
end Fixed

namespace Paired

def completeWord (n d cap q : ℕ) : List (CachedStep (cap+1)) :=
  let table:=ReflectionZeroCachedAction.pairTable cap
  ((List.range (n+2)).map (fun k=>reducedLetter (n+2) d q ((d*k)%(n+2)))).flatMap table.lookup

def word (n d cap q : ℕ) : List (CachedStep (cap+1)) :=
  (completeWord n d cap q).take (2*(n+2)-1)

lemma completeWord_eq (n d cap q : ℕ) :
    completeWord n d cap q=
      (sourceSteps (normalizedSignature n d cap q)++[closingStep (normalizedSignature n d cap q)]).map cache := by
  rw [PairMonomialShift.normalized_complete_word]
  simp only [completeWord,ReflectionZeroCachedAction.pairTable,LetterTable.lookup_ofFn,
    PairMonomialShift.pairSteps,normalizedPairs_map,List.map_flatMap,List.flatMap_map]
  rfl

lemma word_eq (n d cap q : ℕ) :
    word n d cap q=(sourceSteps (normalizedSignature n d cap q)).map cache := by
  rw [word,completeWord_eq,List.map_append]
  have hl : ((sourceSteps (normalizedSignature n d cap q)).map cache).length=2*(n+2)-1 := by
    simp only [List.length_map,sourceSteps,List.length_ofFn,normalizedSignature]
  rw [←hl,List.take_left]
end Paired

namespace ZeroPaired
open ReflectionZeroPaired

def word (n r d cap : ℕ) : List (CachedStep (cap+1)) :=
  let table:=ReflectionZeroCachedAction.pairTable cap
  (List.ofFn (fun j:Fin n=>table.lookup
    (ReflectionThresholdWord.letter (g*(n+2)) r (g*d) (g*((d*(j.val+1))%(n+2)))))).flatten

lemma word_eq (n r p d cap : ℕ) (hr : 0<r) (hd : 0<d)
    (hp : p=r+g*d) (hpm : p<g*(n+2)) (hc : Nat.Coprime d (n+2))
    (hpair : (0:Fin g)≠mate r 0) :
    word (g:=g) n r d cap=(sourceSteps (freeSignature n r p d cap hp hc hpair)).map cache := by
  rw [free_sourceSteps n r p d cap hr hd hp hpm hc hpair]
  simp only [word,ReflectionZeroCachedAction.pairTable,LetterTable.lookup_ofFn,
    List.map_flatten,List.map_ofFn]
  rfl
end ZeroPaired

#print axioms Fixed.word_eq
#print axioms Paired.word_eq
#print axioms ZeroPaired.word_eq
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionCachedBranches

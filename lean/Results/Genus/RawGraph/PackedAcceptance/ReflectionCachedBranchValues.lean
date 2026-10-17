import Results.Genus.RawGraph.PackedAcceptance.ReflectionCachedBranchWords
import Results.Genus.RawGraph.PackedAcceptance.ReflectionOriginalZeroCompression

/-! Source-exact direct scalar action for all four original branches. No
expanded geometry or numerical source-word test is a producer premise. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionCachedBranches
open CachedStepAction CompressedSignature ReflectionThresholdWord
open LayoutCompiler SourceModel ReflectionPairedOrbit ReflectionFullLayout ReflectionFixedPhase
variable {g : ℕ} [NeZero g] {R : Type*} [CommSemiring R]

def pairedValue (n d cap q : ℕ) (z : R) : R :=
  CachedStepAction.value (powers z) (Paired.word n d cap q)
    (cacheTerminal (normalizedSignature n d cap q))

lemma pairedValue_eq (n d cap q : ℕ) (z : R) :
    pairedValue n d cap q z=signatureScalar (normalizedSignature n d cap q) z :=
  CachedStepAction.value_eq _ z _ (Paired.word_eq n d cap q)

def fixedValue (n r p d cap : ℕ) (a : Fin g) (hfix : a=mate r a)
    (hc : Nat.Coprime d (n+2)) (ha0 : a≠0) (z : R) : R :=
  CachedStepAction.value (powers z) (Fixed.word n r p d cap a hfix hc ha0)
    (cacheTerminal (ReflectionFixedPhysicalLabels.signature n r p d cap a hfix hc ha0))

lemma fixedValue_eq (n r p d cap : ℕ) (hr : 0<r) (hd : 0<d) (hp : p=r+g*d)
    (hpm : p<g*(n+2)) (a : Fin g) (hfix : a=mate r a)
    (hc : Nat.Coprime d (n+2)) (ha0 : a≠0) (z : R) :
    fixedValue n r p d cap a hfix hc ha0 z=
      signatureScalar (ReflectionFixedPhysicalLabels.signature n r p d cap a hfix hc ha0) z :=
  CachedStepAction.value_eq _ z _ (Fixed.word_eq n r p d cap hr hd hp hpm a hfix hc ha0)

def zeroFixedValue (n r p d cap : ℕ) (hc : Nat.Coprime d (n+2)) (hp : p=r+g*d)
    (hp0 : 0<p) (hpm : p<g*(n+2)) (hfix : (0:Fin g)=mate r 0) (z : R) : R :=
  let s:=ReflectionFixedZeroPhysical.signature n r p d cap hc hp hp0 hpm hfix
  CachedStepAction.value (powers z)
    (ReflectionZeroCachedAction.word n d (cut g 0 r) (targetIndex n r d 0 hfix hc) s)
    (cacheTerminal s)

lemma zeroFixedValue_eq (n r p d cap : ℕ) (hc : Nat.Coprime d (n+2)) (hp : p=r+g*d)
    (hr : 0<r) (hd : 0<d) (hp0 : 0<p) (hpm : p<g*(n+2)) (hfix : (0:Fin g)=mate r 0) (z : R) :
    zeroFixedValue n r p d cap hc hp hp0 hpm hfix z=
      signatureScalar (ReflectionFixedZeroPhysical.signature n r p d cap hc hp hp0 hpm hfix) z :=
  ReflectionZeroCachedAction.signature_value n r p d cap hc hp hr hd hp0 hpm hfix z

def zeroPairedValue (n r p d cap : ℕ) (hp : p=r+g*d) (hc : Nat.Coprime d (n+2))
    (hpair : (0:Fin g)≠mate r 0) (z : R) : R :=
  z^(2*cap)*CachedStepAction.value (powers z) (ZeroPaired.word (g:=g) n r d cap)
    (cacheTerminal (ReflectionZeroPaired.freeSignature n r p d cap hp hc hpair))

lemma zeroPairedValue_eq (n r p d cap : ℕ) (hr : 0<r) (hd : 0<d)
    (hp : p=r+g*d) (hpm : p<g*(n+2)) (hc : Nat.Coprime d (n+2))
    (hpair : (0:Fin g)≠mate r 0) (z : R) :
    zeroPairedValue n r p d cap hp hc hpair z=
      z^(2*cap)*signatureScalar (ReflectionZeroPaired.freeSignature n r p d cap hp hc hpair) z := by
  unfold zeroPairedValue
  rw [CachedStepAction.value_eq _ z _ (ZeroPaired.word_eq n r p d cap hr hd hp hpm hc hpair)]

/-- The actual original component selects its own branch and current literal
boundaries. The zero-paired factor retains both original pivot vertices. -/
def componentValue (n r p d cap : ℕ) (hc : Nat.Coprime d (n+2)) (hp : p=r+g*d)
    (hp0 : 0<p) (hpm : p<g*(n+2)) (c : Fin (count (g:=g) r)) (z : R) : R :=
  if hfix:representative r c=mate r (representative r c) then
    if hz:representative r c=0 then
      zeroFixedValue n r p d cap hc hp hp0 hpm (by simpa only [hz] using hfix) z
    else fixedValue n r p d cap (representative r c) hfix hc hz z
  else if hz:representative r c=0 then
    zeroPairedValue n r p d cap hp hc (by simpa only [hz] using hfix) z
  else pairedValue n d cap (cut g (representative r c).val r) z

theorem componentValue_correct (n r p d cap : ℕ) (hr : 0<r) (hd : 0<d)
    (hc : Nat.Coprime d (n+2)) (hp : p=r+g*d) (hp0 : 0<p) (hpm : p<g*(n+2))
    (c : Fin (count (g:=g) r)) (z : R) :
    scalarComponent (layout n r p d hc hp hp0 hpm) r p cap z c=
      componentValue n r p d cap hc hp hp0 hpm c z := by
  unfold componentValue
  split_ifs with hfix hz hz
  · rw [zeroFixedValue_eq n r p d cap hc hp hr hd hp0 hpm _ z,
      scalarComponent_eq_signature,ReflectionFixedZeroPhysical.physicalSignature_eq n r p d cap hc hp hp0 hpm c hfix hz]
  · rw [fixedValue_eq n r p d cap hr hd hp hpm _ hfix hc hz z,
      scalarComponent_eq_signature,ReflectionFixedPhysicalLabels.physicalSignature_eq n r p d cap hc hp hp0 hpm c hfix hz]
  · rw [zeroPairedValue_eq n r p d cap hr hd hp hpm hc _ z]
    exact ReflectionZeroPaired.scalarComponent_eq_pinned_free n r p d cap hc hp hp0 hpm c hz
      (by simpa only [hz] using hfix) z
  · rw [pairedValue_eq,scalarComponent_eq_signature,
      physicalSignature_normalized n r p d cap hr hd hc hp hp0 hpm c hfix hz]

#print axioms pairedValue_eq
#print axioms fixedValue_eq
#print axioms zeroPairedValue_eq
#print axioms componentValue_correct
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionCachedBranches

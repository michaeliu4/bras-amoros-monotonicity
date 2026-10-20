import Results.Genus.RawGraph.PackedAcceptance.ReflectionNormalizedSharing
import Results.Genus.RawGraph.PackedAcceptance.ReflectionOriginalLongGate

namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord
open SourceModel LayoutCompiler ReflectionPairedOrbit ReflectionFullLayout
open ReflectionPairedPhysicalLabels

lemma normalized_close (n δ cap q : ℕ) (hδ : 0<δ) (hdL : δ<n+2) (hq : q≤n+2-δ) :
    (normalizedSignature n δ cap q).close=cap := by
  change oddBound cap (reducedLetter (n+2) δ q ((δ*(n+1))%(n+2)))=cap
  rw [show n+1=n+2-1 by omega,final_reduced_letter (n+2) δ q hδ hdL hq]
  rfl

/-- Genuine original gcd-selected source with reduced gap three. -/
def sharedLayout : Layout 104 := layout (g:=8) 11 3 27 3 (by decide) rfl (by decide) (by decide)
lemma sharedLayout_original : ReflectionOriginalLayout.layout 104 3 27 (by decide) (by decide)=sharedLayout := rfl

def sharedLowOne : Fin sharedLayout.count := ⟨2,by decide +kernel⟩
def sharedLowTwo : Fin sharedLayout.count := ⟨3,by decide +kernel⟩
def sharedHigh : Fin sharedLayout.count := ⟨1,by decide +kernel⟩

lemma sharedLowOne_signature : physicalSignature sharedLayout 3 27 4 sharedLowOne=normalizedSignature 11 3 4 0 := by
  exact physicalSignature_two_keys (g:=8) 11 3 27 3 4 (by decide) (by decide) (by decide) rfl
    (by decide) (by decide) ⟨2,by decide +kernel⟩ (by decide +kernel) (by decide +kernel)
lemma sharedLowTwo_signature : physicalSignature sharedLayout 3 27 4 sharedLowTwo=normalizedSignature 11 3 4 0 := by
  exact physicalSignature_two_keys (g:=8) 11 3 27 3 4 (by decide) (by decide) (by decide) rfl
    (by decide) (by decide) ⟨3,by decide +kernel⟩ (by decide +kernel) (by decide +kernel)
lemma sharedHigh_signature : physicalSignature sharedLayout 3 27 4 sharedHigh=normalizedSignature 11 3 4 1 := by
  exact physicalSignature_two_keys (g:=8) 11 3 27 3 4 (by decide) (by decide) (by decide) rfl
    (by decide) (by decide) ⟨1,by decide +kernel⟩ (by decide +kernel) (by decide +kernel)

lemma original_distinct_components_share :
    sharedLowOne≠sharedLowTwo ∧
      physicalSignature sharedLayout 3 27 4 sharedLowOne=physicalSignature sharedLayout 3 27 4 sharedLowTwo := by
  constructor
  · decide +kernel
  · rw [sharedLowOne_signature,sharedLowTwo_signature]

lemma original_shared_square {R : Type*} [CommSemiring R] (z : R) :
    scalarComponent sharedLayout 3 27 4 z sharedLowOne * scalarComponent sharedLayout 3 27 4 z sharedLowTwo=
      signatureScalar (normalizedSignature 11 3 4 0) z ^ 2 := by
  rw [scalarComponent_eq_signature,scalarComponent_eq_signature,
    sharedLowOne_signature,sharedLowTwo_signature,pow_two]

lemma interior_wrap_strong : (normalizedSignature 11 3 4 0).bound ⟨9,by decide⟩=4 := by decide +kernel
lemma before_wrap_carry : (normalizedSignature 11 3 4 0).bound ⟨8,by decide⟩=3 := by decide +kernel
lemma all_carry_rejected : ¬∀j,(normalizedSignature 11 3 4 0).bound j=3 := by
  intro h
  have hh:=h ⟨9,by decide⟩
  rw [interior_wrap_strong] at hh
  omega
lemma high_low_distinct : normalizedSignature 11 3 4 0≠normalizedSignature 11 3 4 1 := by
  intro h
  have hh:=congrArg (fun s : ComponentSignature 4=>s.close) h
  have hm := congrArg (fun s : ComponentSignature 4=>signatureVertices s (1:ℕ) 0 ⟨4,by decide⟩) h
  change 0=1 at hm
  omega

#print axioms normalized_close
#print axioms sharedLayout_original
#print axioms sharedLowOne_signature
#print axioms sharedLowTwo_signature
#print axioms sharedHigh_signature
#print axioms original_distinct_components_share
#print axioms original_shared_square
#print axioms interior_wrap_strong
#print axioms before_wrap_carry
#print axioms all_carry_rejected
#print axioms high_low_distinct
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord

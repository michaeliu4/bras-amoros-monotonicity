import Results.Genus.RawGraph.PackedAcceptance.ReflectionPairedPhysicalSignature
import Results.Genus.RawGraph.PackedAcceptance.ReflectionOriginalLayout
import Results.Genus.RawGraph.PackedAcceptance.ReflectionLongCycleGate

/-! The long power gate is a component of the actual gcd-selected original
packed layout, not only a separately named canonical source order. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionPairedPhysicalLabels
open LayoutCompiler SourceModel ReflectionPairedOrbit ReflectionFullLayout
open ReflectionThresholdWord CompressedSignature
open scoped Matrix

lemma physicalSignature_transport {M m : ℕ} (hm : M=m) (L : Layout m)
    (r p cap : ℕ) (c : Fin L.count) :
    physicalSignature (ReflectionGcdParameters.transportLayout hm L) r p cap c=
      physicalSignature L r p cap c := by
  subst M
  rfl

def originalLongLayout : Layout 400 := ReflectionOriginalLayout.layout 400 1 5 (by decide) (by decide)
def originalLongComponent : Fin originalLongLayout.count := ⟨1,by decide +kernel⟩
def originalLongSignature : ComponentSignature 4 := physicalSignature originalLongLayout 1 5 4 originalLongComponent

theorem originalLong_signature : originalLongSignature=deltaOneSignature 98 4 0 := by
  change physicalSignature
    (ReflectionGcdParameters.transportLayout (show 400=4*(98+2) from rfl)
      (layout (g:=4) 98 1 5 1 (by decide) rfl (by decide) (by decide))) 1 5 4 ⟨1,by decide +kernel⟩=_
  rw [physicalSignature_transport]
  exact physicalSignature_delta_one (g:=4) 98 1 5 4 (by decide) (by decide) rfl
    (by decide) (by decide) ⟨1,by decide +kernel⟩ (by decide +kernel) (by decide +kernel)

theorem originalLong_word : sourceSteps originalLongSignature=List.replicate 199 (carryStep 4) := by
  rw [originalLong_signature,deltaOneSignature_sourceSteps 98 4 0 (by omega)]
  rfl

theorem originalLong_scalar {R : Type*} [CommSemiring R] (z : R) :
    scalarComponent originalLongLayout 1 5 4 z originalLongComponent=
      Matrix.trace (carryPair 4 z ^ 99 * closingPair 4 z) := by
  rw [scalarComponent_eq_signature]
  change signatureScalar originalLongSignature z=_
  rw [originalLong_signature]
  exact deltaOne_zero_pair_trace 98 4 z

lemma originalLong_terminal_close :
    (originalLongSignature.mask (Fin.last originalLongSignature.edges) = mask 4 .carryCarry) ∧
    originalLongSignature.close=4 ∧ originalLongSignature.cycle=true := by
  rw [originalLong_signature]
  decide +kernel

lemma originalLong_no_skip : sourceSteps originalLongSignature≠List.replicate 198 (carryStep 4) := by
  rw [originalLong_word]
  intro h
  have:=congrArg List.length h
  simp only [List.length_replicate] at this
  omega

#print axioms physicalSignature_transport
#print axioms originalLong_signature
#print axioms originalLong_word
#print axioms originalLong_scalar
#print axioms originalLong_terminal_close
#print axioms originalLong_no_skip
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionPairedPhysicalLabels

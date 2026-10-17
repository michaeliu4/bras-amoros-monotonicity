import Results.Genus.RawGraph.PackedAcceptance.ReflectionPairedPowerScalar
import Results.Genus.RawGraph.PackedAcceptance.ReflectionOriginalLayout
import Results.Genus.RawGraph.PackedAcceptance.ReflectionNormalizedFixtures

namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord.RetainedPairedPower
open SourceModel LayoutCompiler ReflectionFullLayout ReflectionPairedOrbit
open PairMonomialShift CompressedSignature
open scoped Matrix

/-- Actual gcd-selected original layout at the retained strict boundary. -/
def actualLayout : Layout 548 := ReflectionOriginalLayout.layout 548 1 149 (by decide) (by decide)
def actualComponent : Fin actualLayout.count := ⟨1,by decide +kernel⟩
def actualSignature : ComponentSignature 4 := physicalSignature actualLayout 1 149 4 actualComponent

lemma retained_boundary : 3*548+149+1=2*897 := by decide +kernel
lemma chosen_representative : (representative (g:=4) 1 ⟨1,by decide +kernel⟩).val=2 := by decide +kernel

lemma actual_signature : actualSignature=normalizedSignature 135 37 4 0 := by
  change physicalSignature
    (layout (g:=4) 135 1 149 37 (by decide) rfl (by decide) (by decide))
      1 149 4 ⟨1,by decide +kernel⟩=_
  exact physicalSignature_normalized (g:=4) 135 1 149 37 4 (by decide) (by decide)
    (by decide) rfl (by decide) (by decide) ⟨1,by decide +kernel⟩
    (by decide +kernel) (by decide +kernel)

/-- No274-vertex validation: uniform physical signature and ordered-word
proofs connect the actual scalar to the tuple-materialized power program. -/
theorem actual_scalar_power {R : Type*} [CommSemiring R] (z : R) :
    scalarComponent actualLayout 1 149 4 z actualComponent=
      Matrix.trace ((sourceCompile 137 37 0).evalTuple (pairLetterMatrix 4 z)) := by
  rw [scalarComponent_eq_signature]
  change signatureScalar actualSignature z=_
  rw [actual_signature]
  exact normalized_scalar_power 135 37 4 0 (by omega) (by omega) (by omega) z

theorem actual_scalar_shifted {R : Type*} [CommSemiring R] (z : R) :
    scalarComponent actualLayout 1 149 4 z actualComponent=
      z^411*Matrix.trace ((sourceCompile 137 37 0).evalTuple (residualLetterMatrix 4 z)) := by
  rw [scalarComponent_eq_signature]
  change signatureScalar actualSignature z=_
  rw [actual_signature]
  exact normalized_scalar_shifted_power 135 37 4 0 (by omega) (by omega)
    (by decide) (by omega) (by omega) z

theorem actual_scalar_summary {R : Type*} [CommSemiring R] (z : R) :
    scalarComponent actualLayout 1 149 4 z actualComponent=
      z^411*Matrix.trace (sourceSummary (residualLetterMatrix 4 z) 137 37 0).value := by
  rw [sourceSummary_value_tuple _ 137 37 0 (by omega) (by omega) (by omega)]
  exact actual_scalar_shifted z

theorem actual_coefficient (H : ℕ) (hH : 411≤H) :
    (scalarComponent actualLayout 1 149 4 (Polynomial.X : Polynomial ℕ) actualComponent).coeff H=
      (Matrix.trace ((sourceCompile 137 37 0).evalTuple
        (residualLetterMatrix 4 (Polynomial.X : Polynomial ℕ)))).coeff (H-411) := by
  rw [actual_scalar_shifted,Polynomial.coeff_X_pow_mul',if_pos hH]

lemma actual_terminal : actualSignature.edges=273 ∧ actualSignature.cycle=true ∧
    actualSignature.close=4 ∧
    actualSignature.mask (Fin.last actualSignature.edges)=mask 4 .carryCarry := by
  rw [actual_signature]
  decide +kernel

lemma actual_last_pair : reducedLetter 137 37 0 ((37*136)%137)=.carryStrong := by
  exact final_reduced_letter 137 37 0 (by omega) (by omega) (by omega)

lemma interior_strong_odd_edge : (normalizedSignature 135 37 4 0).bound ⟨7,by decide⟩=4 := by decide +kernel
lemma ordinary_even_carry : (normalizedSignature 135 37 4 0).bound ⟨6,by decide⟩=3 := by decide +kernel
lemma residual_width : 897-411+1=487 := by decide +kernel

#print axioms actual_signature
#print axioms actual_scalar_power
#print axioms actual_scalar_shifted
#print axioms actual_scalar_summary
#print axioms actual_coefficient
#print axioms actual_terminal
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord.RetainedPairedPower

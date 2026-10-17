import Results.Genus.RawGraph.PackedAcceptance.ReflectionPPhasePower
import Results.Genus.RawGraph.PackedAcceptance.ReflectionRetainedPairedPower

namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord.RetainedPPhasePower
open RetainedPairedPower SourceModel PairMonomialShift CompressedSignature
open scoped Matrix

/-- Original gcd-selected M548/r1/p149 component, representative2, evaluated
with the exact adjacent-letter summary and one actual cycle closure. -/
theorem actual_p_scalar {R : Type*} [CommSemiring R] (z : R) :
    scalarComponent actualLayout 1 149 4 z actualComponent =
      z^448 * Matrix.trace (pProgramValue 4 z 137 37 0) := by
  rw [scalarComponent_eq_signature]
  change signatureScalar actualSignature z = _
  rw [actual_signature]
  exact normalized_p_scalar_power 135 37 4 0 (by omega) (by omega)
    (by decide) (by omega) (by omega) z

theorem actual_p_coefficient (H : ℕ) (hH : 448≤H) :
    (scalarComponent actualLayout 1 149 4 (Polynomial.X : Polynomial ℕ) actualComponent).coeff H =
      (Matrix.trace (pProgramValue 4 (Polynomial.X : Polynomial ℕ) 137 37 0)).coeff (H-448) := by
  rw [actual_p_scalar, Polynomial.coeff_X_pow_mul', if_pos hH]

theorem actual_p_below_shift (H : ℕ) (hH : H<448) :
    (scalarComponent actualLayout 1 149 4 (Polynomial.X : Polynomial ℕ) actualComponent).coeff H = 0 := by
  rw [actual_p_scalar, Polynomial.coeff_X_pow_mul', if_neg (by omega)]

lemma residual_H464 : 464-448+1=17 := rfl
lemma residual_H897 : 897-448+1=450 := rfl
lemma origin_retained : 448+(464-448)=464 := rfl

#print axioms actual_p_scalar
#print axioms actual_p_coefficient
#print axioms actual_p_below_shift
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord.RetainedPPhasePower

import Results.Genus.RawGraph.PackedAcceptance.ReflectionCompressedCycleTrace
import Results.Genus.RawGraph.PackedAcceptance.ReflectionThresholdAudit

/-! Concrete source gate for m=400, r=1, p=5, gcd=4, orbit length=100,
coset representative=2 and delta=1. The original 200-vertex source is
identified by arithmetic theorems, with no expanded mask/edge checker. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord
open CompressedSignature
open scoped Matrix

/-- Exact B^99 C identity for the actual long canonical original source. -/
theorem long_original_pair_trace {R : Type*} [CommSemiring R] (z : R) :
    signatureScalar Audit.longCanonical z =
      Matrix.trace (carryPair 4 z ^ 99 * closingPair 4 z) := by
  rw [Audit.long_original_signature]
  exact deltaOne_zero_pair_trace 98 4 z

/-- The final matrix is explicitly strong while its vertex mask stays carry. -/
lemma long_closing_step : closingStep Audit.longCanonical = strongCarryStep 4 := by
  rw [Audit.long_original_signature]
  exact deltaOne_zero_closingStep 98 4

#print axioms long_original_pair_trace
#print axioms long_closing_step
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord

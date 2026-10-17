import Results.Genus.RawGraph.PackedAcceptance.ReflectionDeltaOneProduct
import Results.Genus.RawGraph.PackedAcceptance.CompressedSignatureCycleTrace

/-! Pair-word trace compression of the original delta-one canonical cycle.
The final C has a carry-mask left factor and a strong closing right factor.
No expanded mask or edge validation occurs in these proofs. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord
open CompressedSignature ReflectionPairedOrbit
open scoped Matrix

/-- Final vertex has the carry mask, even though its closing edge is strong. -/
def strongCarryStep (cap : ℕ) : Step (cap+1) := ⟨mask cap .carryCarry, cap⟩

lemma deltaOne_zero_closingStep (n cap : ℕ) :
    closingStep (deltaOneSignature n cap 0) = strongCarryStep cap := by
  simp [closingStep, deltaOneSignature, strongCarryStep]

/-- B is the ordinary carry/carry pair. -/
def carryPair {R : Type*} [CommSemiring R] (cap : ℕ) (z : R) :=
  stepMatrix z (carryStep cap) ^ 2

/-- C consumes the final two vertices and the strong true closing edge. -/
def closingPair {R : Type*} [CommSemiring R] (cap : ℕ) (z : R) :=
  stepMatrix z (carryStep cap) * stepMatrix z (strongCarryStep cap)

/-- This identity is uniform in cycle length, cap, weight and semiring. -/
theorem deltaOne_zero_pair_trace {R : Type*} [CommSemiring R]
    (n cap : ℕ) (z : R) :
    signatureScalar (deltaOneSignature n cap 0) z =
      Matrix.trace (carryPair cap z ^ (n+1) * closingPair cap z) := by
  have hw : sourceSteps (deltaOneSignature n cap 0) =
      List.replicate (2*(n+1)+1) (carryStep cap) := by
    rw [deltaOneSignature_sourceSteps n cap 0 (by omega)]
    simp only [Nat.mul_zero, List.replicate_zero, List.nil_append, Nat.sub_zero]
    congr 1
  have h := cycle_single_step_pair_trace (deltaOneSignature n cap 0)
    rfl z (carryStep cap) (n+1) hw
  simpa only [deltaOne_zero_closingStep, carryPair, closingPair] using h

/-- Actual source arithmetic supplies the signature; no list checker appears. -/
theorem canonical_zero_cut_pair_trace {g : ℕ} [NeZero g]
    {R : Type*} [CommSemiring R] (n r p cap : ℕ) (hr : 0<r)
    (hp : p=r+g*1) (hpm : p<g*(n+2)) (hc : Nat.Coprime 1 (n+2))
    (a : Fin g) (ha : a≤mate r a) (ha0 : a≠0) (hpair : a≠mate r a)
    (hz : cut g a.val r = 0) (z : R) :
    signatureScalar (canonicalSignature n r p 1 cap hp hc a ha ha0 hpair) z =
      Matrix.trace (carryPair cap z ^ (n+1) * closingPair cap z) := by
  rw [canonicalSignature_delta_one n r p cap hr hp hpm hc a ha ha0 hpair, hz]
  exact deltaOne_zero_pair_trace n cap z

#print axioms deltaOne_zero_pair_trace
#print axioms canonical_zero_cut_pair_trace
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord

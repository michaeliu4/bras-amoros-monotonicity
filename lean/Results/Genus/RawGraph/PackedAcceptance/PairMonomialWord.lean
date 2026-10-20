import Results.Genus.RawGraph.PackedAcceptance.PairMonomialShift
import Results.Genus.RawGraph.PackedAcceptance.CompressedSignatureCycleTrace

/-! Exact accumulated shifts for ordered pair words, including the actual
closing step. The theorem does not authorize rotating into another phase. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.PairMonomialShift
open CompressedSignature
open scoped BigOperators Matrix
variable {R : Type*} [CommSemiring R] {k : ℕ}

def pairSteps (pairs : List (Step k × Step k)) : List (Step k) :=
  pairs.flatMap (fun p => [p.1,p.2])

def wordShift (pairs : List (Step k × Step k)) : ℕ :=
  (pairs.map (fun p => p.1.bound)).sum

def shiftedWordMatrix (z : R) (pairs : List (Step k × Step k)) :
    Matrix (Fin k) (Fin k) R :=
  (pairs.map (fun p => shiftedPairMatrix z p.1 p.2)).prod

theorem pair_word_factor (z : R) (pairs : List (Step k × Step k)) :
    ((pairSteps pairs).map (stepMatrix z)).prod =
      z^(wordShift pairs) • shiftedWordMatrix z pairs := by
  induction pairs with
  | nil => simp [pairSteps, wordShift, shiftedWordMatrix]
  | cons p pairs ih =>
    simp only [pairSteps, List.flatMap_cons, List.map_append, List.prod_append,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at *
    rw [pair_factor, ih, scalar_matrix_mul, ← pow_add]
    rfl

/-- The complete closing step is inside the word, so the terminal vertex and
actual-first closure are each consumed exactly once. -/
theorem cycle_word_factor {cap : ℕ} (s : ComponentSignature cap)
    (hc : s.cycle = true) (pairs : List (Step (cap+1) × Step (cap+1)))
    (hsource : sourceSteps s ++ [closingStep s] = pairSteps pairs) (z : R) :
    signatureScalar s z = z^(wordShift pairs) * Matrix.trace (shiftedWordMatrix z pairs) := by
  rw [cycle_signature_eq_trace s hc]
  have hw : ((sourceSteps s).map (stepMatrix z)).prod * stepMatrix z (closingStep s) =
      ((pairSteps pairs).map (stepMatrix z)).prod := by
    rw [← hsource, List.map_append, List.prod_append]
    simp
  rw [hw, pair_word_factor, Matrix.trace_smul, smul_eq_mul]

/-- Only the residual genus H minus the proved word shift is needed. -/
theorem cycle_coefficient_shift {cap : ℕ} (s : ComponentSignature cap)
    (hc : s.cycle = true) (pairs : List (Step (cap+1) × Step (cap+1)))
    (hsource : sourceSteps s ++ [closingStep s] = pairSteps pairs)
    (H : ℕ) (hH : wordShift pairs ≤ H) :
    (signatureScalar s (Polynomial.X : Polynomial ℕ)).coeff H =
      (Matrix.trace (shiftedWordMatrix (Polynomial.X : Polynomial ℕ) pairs)).coeff
        (H-wordShift pairs) := by
  rw [cycle_word_factor s hc pairs hsource, Polynomial.coeff_X_pow_mul', if_pos hH]

#print axioms pair_word_factor
#print axioms cycle_word_factor
#print axioms cycle_coefficient_shift
end SubmittedGenus.RawGraph.PackedAcceptance.PairMonomialShift

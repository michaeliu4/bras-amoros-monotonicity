import Results.Genus.RawGraph.PackedAcceptance.PairMonomialWord

/-! One-step cyclic phase change of a complete matrix word. This is a trace
identity, never a change of the original physical signature or an inversion. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.PairMonomialShift
open CompressedSignature
open scoped BigOperators Matrix
variable {k : ℕ}

/-- Retain the current second step and the next pair's first step. -/
def crossPairs (first previousSecond : Step k) : List (Step k × Step k) → List (Step k × Step k)
  | [] => [(previousSecond,first)]
  | p::pairs => (previousSecond,p.1)::crossPairs first p.2 pairs

def pPhasePairs : List (Step k × Step k) → List (Step k × Step k)
  | [] => []
  | p::pairs => crossPairs p.1 p.2 pairs

lemma crossPairs_word (first previousSecond : Step k) (pairs : List (Step k × Step k)) :
    pairSteps (crossPairs first previousSecond pairs) =
      previousSecond :: (pairSteps pairs ++ [first]) := by
  induction pairs generalizing previousSecond with
  | nil => rfl
  | cons p pairs ih =>
    change previousSecond :: p.1 :: pairSteps (crossPairs first p.2 pairs) =
      previousSecond :: ((p.1 :: p.2 :: pairSteps pairs) ++ [first])
    rw [ih]
    rfl

lemma crossPairs_shift (first previousSecond : Step k) (pairs : List (Step k × Step k)) :
    wordShift (crossPairs first previousSecond pairs) =
      previousSecond.bound + (pairs.map (fun p => p.2.bound)).sum := by
  induction pairs generalizing previousSecond with
  | nil => simp [crossPairs, wordShift]
  | cons p pairs ih =>
    change previousSecond.bound + wordShift (crossPairs first p.2 pairs) =
      previousSecond.bound + (p.2.bound + (pairs.map (fun p => p.2.bound)).sum)
    rw [ih]

lemma pPhase_wordShift (pairs : List (Step k × Step k)) :
    wordShift (pPhasePairs pairs) = (pairs.map (fun p => p.2.bound)).sum := by
  cases pairs with
  | nil => rfl
  | cons p pairs => simp [pPhasePairs, crossPairs_shift]

/-- Rotate exactly the first matrix step to the end; masks on adjacent
cross-letter factors need not be equal. -/
theorem pPhase_trace {R : Type*} [CommSemiring R]
    (z : R) (pairs : List (Step k × Step k)) :
    Matrix.trace (((pairSteps pairs).map (stepMatrix z)).prod) =
      Matrix.trace (((pairSteps (pPhasePairs pairs)).map (stepMatrix z)).prod) := by
  cases pairs with
  | nil => rfl
  | cons p pairs =>
    rw [pPhasePairs, crossPairs_word]
    simp only [pairSteps, List.flatMap_cons, List.map_append, List.prod_append,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [mul_assoc, Matrix.trace_mul_comm, mul_assoc]

/-- The complete source word includes its actual last-to-first closure.
Only its trace is rotated; open path terminals are outside this theorem. -/
theorem cycle_pPhase_factor {R : Type*} [CommSemiring R] {cap : ℕ}
    (s : ComponentSignature cap) (hc : s.cycle = true)
    (pairs : List (Step (cap+1) × Step (cap+1)))
    (hsource : sourceSteps s ++ [closingStep s] = pairSteps pairs) (z : R) :
    signatureScalar s z = z^(wordShift (pPhasePairs pairs)) *
      Matrix.trace (shiftedWordMatrix z (pPhasePairs pairs)) := by
  rw [cycle_signature_eq_trace s hc]
  have hw : ((sourceSteps s).map (stepMatrix z)).prod * stepMatrix z (closingStep s) =
      ((pairSteps pairs).map (stepMatrix z)).prod := by
    rw [← hsource, List.map_append, List.prod_append]
    simp
  rw [hw, pPhase_trace, pair_word_factor, Matrix.trace_smul, smul_eq_mul]

#print axioms pPhase_trace
#print axioms cycle_pPhase_factor
end SubmittedGenus.RawGraph.PackedAcceptance.PairMonomialShift

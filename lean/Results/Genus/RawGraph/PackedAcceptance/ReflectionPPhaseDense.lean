import Results.Genus.RawGraph.PackedAcceptance.ReflectionRetainedPPhasePower
import Results.Genus.RawGraph.PackedAcceptance.MaterializedMatrixMonoid

namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord
open MaterializedMatrixMonoid AdjacencySummary
open scoped Matrix

def densePTransition {R : Type*} [CommSemiring R] (cap : ℕ) (z : R) (a b : Letter) :
    Dense (cap+1) R := ofMatrix (pTransition cap z a b)

def densePProgramValue {R : Type*} [CommSemiring R] (cap : ℕ) (z : R) (L d q : ℕ) :
    Dense (cap+1) R :=
  close (densePTransition cap z)
    ((sourceCompile L d q).evalTuple (singleton (densePTransition cap z)))

lemma dense_p_chain {R : Type*} [CommSemiring R]
    (cap : ℕ) (z : R) (first previous : Letter) (xs : List Letter) :
    toMatrix (chain (densePTransition cap z) first previous xs) =
      chain (pTransition cap z) first previous xs := by
  induction xs generalizing previous with
  | nil => simp [chain, densePTransition]
  | cons a xs ih => simp [chain, densePTransition, ih]

/-- Numeric cells are stored after every summary multiplication. The
ordered source theorem and its original matrix dimension are unchanged. -/
theorem dense_p_program_eq {R : Type*} [CommSemiring R]
    (cap : ℕ) (z : R) (L d q : ℕ) (hd : 0<d) (hdL : d<L) (hq : q≤L-d) :
    toMatrix (densePProgramValue cap z L d q) = pProgramValue cap z L d q := by
  unfold densePProgramValue pProgramValue
  rw [SourceProgram.evalTuple_eq, SourceProgram.evalTuple_eq,
    sourceCompile_correct _ L d q hd hdL hq, sourceCompile_correct _ L d q hd hdL hq]
  change toMatrix (close _ (ofList _ _)) = close _ (ofList _ _)
  rw [close_ofList, close_ofList]
  cases (List.range L).map (fun k => reducedLetter L d q ((d*k)%L)) with
  | nil => exact toMatrix_one
  | cons a xs => exact dense_p_chain cap z a a xs

open RetainedPPhasePower RetainedPairedPower SourceModel

theorem actual_dense_p_scalar {R : Type*} [CommSemiring R] (z : R) :
    scalarComponent actualLayout 1 149 4 z actualComponent =
      z^448 * Matrix.trace (toMatrix (densePProgramValue 4 z 137 37 0)) := by
  rw [dense_p_program_eq 4 z 137 37 0 (by omega) (by omega) (by omega)]
  exact actual_p_scalar z

theorem actual_dense_p_coefficient (H : ℕ) (hH : 448≤H) :
    (scalarComponent actualLayout 1 149 4 (Polynomial.X : Polynomial ℕ) actualComponent).coeff H =
      (Matrix.trace (toMatrix (densePProgramValue 4 (Polynomial.X : Polynomial ℕ) 137 37 0))).coeff
        (H-448) := by
  rw [actual_dense_p_scalar, Polynomial.coeff_X_pow_mul', if_pos hH]

#print axioms dense_p_program_eq
#print axioms actual_dense_p_scalar
#print axioms actual_dense_p_coefficient
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord

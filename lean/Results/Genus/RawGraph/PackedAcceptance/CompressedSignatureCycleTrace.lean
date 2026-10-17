import Results.Genus.RawGraph.PackedAcceptance.CompressedSignature
import Mathlib.LinearAlgebra.Matrix.Trace

/-! Exact trace form of a closed signature. The last step consumes its vertex
mask and weight exactly once and closes to the actual initial state. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.CompressedSignature
open scoped BigOperators Matrix
variable {R : Type*} [CommSemiring R]

def closingStep {a : ℕ} (s : ComponentSignature a) : Step (a+1) :=
  ⟨s.mask (Fin.last s.edges), s.close⟩

lemma terminal_eq_closingStep {a : ℕ} (s : ComponentSignature a)
    (hc : s.cycle = true) (z : R) (first last : Fin (a+1)) :
    terminal s z first last = stepMatrix z (closingStep s) last first := by
  simp only [terminal, hc, ↓reduceIte, signatureVertices,
    Nat.lt_succ_self, ↓reduceDIte, stepMatrix, closingStep, Fin.last]
  split_ifs <;> simp

lemma matrixValue_eq_trace {a : ℕ} (s : ComponentSignature a)
    (hc : s.cycle = true) (z : R) (A : Matrix (Fin (a+1)) (Fin (a+1)) R) :
    matrixValue s z A = Matrix.trace (A * stepMatrix z (closingStep s)) := by
  simp only [matrixValue, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.mulVec, dotProduct, terminal_eq_closingStep s hc z]

/-- This trace includes the closing edge, so no extra terminal is applied. -/
theorem cycle_signature_eq_trace {a : ℕ} (s : ComponentSignature a)
    (hc : s.cycle = true) (z : R) :
    signatureScalar s z = Matrix.trace
      (((sourceSteps s).map (stepMatrix z)).prod * stepMatrix z (closingStep s)) := by
  rw [← matrixValue_eq_signature, matrixValue_eq_trace s hc]

/-- A repeated ordinary word plus a short final suffix remains an exact cycle. -/
theorem cycle_repeat_word_trace {a : ℕ} (s : ComponentSignature a)
    (hc : s.cycle = true) (z : R) (word tail : List (Step (a+1))) (n : ℕ)
    (hword : sourceSteps s = (List.replicate n word).flatten ++ tail) :
    signatureScalar s z = Matrix.trace
      (((word.map (stepMatrix z)).prod)^n *
        ((tail.map (stepMatrix z)).prod * stepMatrix z (closingStep s))) := by
  rw [cycle_signature_eq_trace s hc, hword, List.map_append,
    List.prod_append, repeat_word_product, mul_assoc]

/-- Pair-word B^n C without expanding 2*n+1 copies or checking a source list. -/
theorem cycle_single_step_pair_trace {a : ℕ} (s : ComponentSignature a)
    (hc : s.cycle = true) (z : R) (A : Step (a+1)) (n : ℕ)
    (hword : sourceSteps s = List.replicate (2*n+1) A) :
    signatureScalar s z = Matrix.trace
      ((stepMatrix z A ^ 2)^n * (stepMatrix z A * stepMatrix z (closingStep s))) := by
  rw [cycle_signature_eq_trace s hc, hword, List.map_replicate,
    List.prod_replicate, pow_succ, pow_mul, mul_assoc]

#print axioms cycle_signature_eq_trace
#print axioms cycle_repeat_word_trace
#print axioms cycle_single_step_pair_trace
end SubmittedGenus.RawGraph.PackedAcceptance.CompressedSignature

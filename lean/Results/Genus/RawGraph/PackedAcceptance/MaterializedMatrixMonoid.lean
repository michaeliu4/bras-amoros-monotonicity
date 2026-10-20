import Results.Genus.RawGraph.PackedAcceptance.CompressedSignature
import Mathlib.Data.Vector.Basic

namespace SubmittedGenus.RawGraph.PackedAcceptance.MaterializedMatrixMonoid
open scoped Matrix

/-- Every cell is stored, so repeated summary queries reuse numeric values
rather than a nested function that recomputes matrix multiplication. -/
structure Dense (k : ℕ) (R : Type*) where
  rows : List.Vector (List.Vector R k) k
  deriving DecidableEq

def toMatrix {k R} (A : Dense k R) : Matrix (Fin k) (Fin k) R := fun i j=>(A.rows.get i).get j
def ofMatrix {k R} (A : Matrix (Fin k) (Fin k) R) : Dense k R :=
  ⟨List.Vector.ofFn (fun i=>List.Vector.ofFn (A i))⟩

@[simp] theorem toMatrix_ofMatrix {k R} (A : Matrix (Fin k) (Fin k) R) :
    toMatrix (ofMatrix A)=A := by funext i j;simp [toMatrix,ofMatrix]

theorem toMatrix_injective {k R} : Function.Injective (@toMatrix k R) := by
  intro A B h
  cases A with | mk A =>
    cases B with | mk B =>
      congr 1
      apply List.Vector.ext
      intro i
      apply List.Vector.ext
      intro j
      exact congrFun (congrFun h i) j

instance {k R} [Semiring R] : Monoid (Dense k R) where
  mul A B:=ofMatrix (toMatrix A*toMatrix B)
  one:=ofMatrix 1
  one_mul A:=by
    apply toMatrix_injective
    change toMatrix (ofMatrix (toMatrix (ofMatrix 1)*toMatrix A))=toMatrix A
    simp
  mul_one A:=by
    apply toMatrix_injective
    change toMatrix (ofMatrix (toMatrix A*toMatrix (ofMatrix 1)))=toMatrix A
    simp
  mul_assoc A B C:=by
    apply toMatrix_injective
    change toMatrix (ofMatrix (toMatrix (ofMatrix (toMatrix A*toMatrix B))*toMatrix C))=
      toMatrix (ofMatrix (toMatrix A*toMatrix (ofMatrix (toMatrix B*toMatrix C))))
    simp [mul_assoc]

@[simp] theorem toMatrix_mul {k R} [Semiring R] (A B : Dense k R) :
    toMatrix (A*B)=toMatrix A*toMatrix B := toMatrix_ofMatrix _
@[simp] theorem toMatrix_one {k R} [Semiring R] : toMatrix (1:Dense k R)=1 := toMatrix_ofMatrix _

theorem toMatrix_prod {k R} [Semiring R] (w : List (Dense k R)) :
    toMatrix w.prod=(w.map toMatrix).prod := by
  induction w with
  | nil => simp
  | cons a w ih => simp [ih]

def step {k R} [CommSemiring R] (z : R) (s : CompressedSignature.Step k) : Dense k R :=
  ofMatrix (CompressedSignature.stepMatrix z s)

#print axioms toMatrix_injective
#print axioms toMatrix_prod
end SubmittedGenus.RawGraph.PackedAcceptance.MaterializedMatrixMonoid

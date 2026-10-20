import Results.Genus.RawGraph.PackedAcceptance.MaterializedMatrixMonoid

/-! Direct materialized matrix-vector baseline. Each suffix vector is stored
once; this is separate from full-matrix arithmetic and source metadata setup. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.MaterializedMatrixMonoid
open scoped Matrix
variable {k : ℕ} {R : Type*} [Semiring R]

def vectorProduct : List (Dense k R) → List.Vector R k → List.Vector R k
  | [],v => v
  | a::w,v =>
      let tail:=vectorProduct w v
      List.Vector.ofFn (fun i=>(toMatrix a *ᵥ (fun j=>tail.get j)) i)

theorem vectorProduct_eq (w : List (Dense k R)) (v : List.Vector R k) :
    (fun i=>(vectorProduct w v).get i)=toMatrix w.prod *ᵥ (fun i=>v.get i) := by
  induction w with
  | nil => simp [vectorProduct]
  | cons a w ih =>
    simp only [vectorProduct,List.Vector.get_ofFn,List.prod_cons,toMatrix_mul]
    rw [ih,Matrix.mulVec_mulVec]

#print axioms vectorProduct_eq
end SubmittedGenus.RawGraph.PackedAcceptance.MaterializedMatrixMonoid

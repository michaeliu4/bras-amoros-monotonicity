import Results.Genus.CapFourMass.IntervalMatrix

/-! Finite expression adapters for signed run programs. Taking matrixAbsolute
is an explicit syntax operation, so a complete projected block can be formed
before absolute values; multiplication itself remains fully signed. -/
open scoped Matrix
namespace SubmittedGenus.CapFourMass.Interval.Expr

noncomputable def vectorReal (xs : ℕ→ℝ) {n : ℕ} (v : EVector n) : Fin n→ℝ :=
  fun i => (v i).real xs

def vectorAbsolute {n : ℕ} (v : EVector n) : EVector n := fun i => .abs (v i)
def matrixAbsolute {n : ℕ} (A : EMatrix n) : EMatrix n := fun i j => .abs (A i j)
def matrixScale {n : ℕ} (s : Expr) (A : EMatrix n) : EMatrix n := fun i j => s*A i j

def matrixProduct {n : ℕ} : List (EMatrix n)→EMatrix n
  | [] => matrixId n
  | A::as => matrixMul A (matrixProduct as)

@[simp] theorem vectorAbsolute_real (xs : ℕ→ℝ) {n : ℕ} (v : EVector n) :
    vectorReal xs (vectorAbsolute v)=fun i => |vectorReal xs v i| := rfl

@[simp] theorem matrixAbsolute_real (xs : ℕ→ℝ) {n : ℕ} (A : EMatrix n) :
    matrixReal xs (matrixAbsolute A)=fun i j => |matrixReal xs A i j| := rfl

@[simp] theorem matrixScale_real (xs : ℕ→ℝ) {n : ℕ} (s : Expr) (A : EMatrix n) :
    matrixReal xs (matrixScale s A)=s.real xs • matrixReal xs A := by
  ext i j
  rfl

theorem matrixProduct_real (xs : ℕ→ℝ) {n : ℕ} (as : List (EMatrix n)) :
    matrixReal xs (matrixProduct as)=(as.map (matrixReal xs)).prod := by
  induction as with
  | nil => simpa only [matrixProduct,List.map_nil,List.prod_nil] using matrixId_real xs n
  | cons A as ih =>
    simp only [matrixProduct,matrixMul_real,ih,List.map_cons,List.prod_cons]

end SubmittedGenus.CapFourMass.Interval.Expr

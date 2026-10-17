import Results.Genus.CapFiveMass.MatrixSource

/-! Exact arbitrary signed asymmetric matrix-source normalization. Every edge
factor is kept inside the complete finite assignment sum. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass.AsymmetricMatrixSource
open RawGraph.Transfer CapFiveMass.MatrixSource
variable {A : Type*} [Fintype A] [DecidableEq A]

lemma run_matrix_eq (n : ℕ) (E : ℕ→Matrix A A ℝ) (y : A→ℝ) (first : A) :
    run n (fun _ _ => 1) E y first=(matrixRun n E*ᵥ y) first := by
  induction n generalizing E first with
  | zero => simp [run,matrixRun]
  | succ n ih =>
    simp only [run,one_mul,matrixRun,← Matrix.mulVec_mulVec]
    change (∑ next,E 0 first next*run n (fun _ _ => 1) (shift E) y next)=_
    simp_rw [ih]
    rfl

/-- Full assignment expansion with arbitrary endpoint vectors and signed edges. -/
lemma path_expansion (n : ℕ) (E : ℕ→Matrix A A ℝ) (x y : A→ℝ) :
    x ⬝ᵥ (matrixRun n E*ᵥ y)=
      ∑ a : Fin (n+1)→A,x (a 0)*(∏ j : Fin n,E j.val (a j.castSucc) (a j.succ))*y (a (Fin.last n)) := by
  rw [sum_cons]
  simp only [dotProduct,← run_matrix_eq,run_eq_fixedSource,fixedSource,Finset.mul_sum,
    sourceTerm,Finset.prod_const_one,one_mul,Fin.cons_zero]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro tail _
  ring

/-- A cycle retains its actual first state in the closing edge. -/
lemma cycle_expansion (n : ℕ) (E : ℕ→Matrix A A ℝ) (close : Matrix A A ℝ) :
    (matrixRun n E*close).trace=
      ∑ a : Fin (n+1)→A,(∏ j : Fin n,E j.val (a j.castSucc) (a j.succ))*close (a (Fin.last n)) (a 0) := by
  have he : (matrixRun n E*close).trace=cycleRun n (fun _ _ => 1) E close := by
    simp only [cycleRun,run_matrix_eq,Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Matrix.mulVec,dotProduct]
  rw [he,cycleRun_eq_source]
  simp only [cycleSource,sourceTerm,Finset.prod_const_one,one_mul]

def asymmetricMatrix (left right : ℕ→A→ℝ) (gate : ℕ→A→A→ℝ) (j : ℕ) : Matrix A A ℝ :=
  fun a b => left j a*gate j a b*right j b

def incomingWeight (right : ℕ→A→ℝ) (x : A→ℝ) (j : ℕ) (a : A) : ℝ :=
  if j=0 then x a else right (j-1) a

def outgoingWeight (n : ℕ) (left : ℕ→A→ℝ) (y : A→ℝ) (j : ℕ) (a : A) : ℝ :=
  if j=n then y a else left j a

def vertexWeight (n : ℕ) (left right : ℕ→A→ℝ) (x y : A→ℝ) (j : ℕ) (a : A) : ℝ :=
  incomingWeight right x j a*outgoingWeight n left y j a

lemma incoming_product (n : ℕ) (right : ℕ→A→ℝ) (x : A→ℝ) (a : Fin (n+1)→A) :
    (∏ j : Fin (n+1),incomingWeight right x j.val (a j))=
      x (a 0)*∏ j : Fin n,right j.val (a j.succ) := by
  simp [incomingWeight,Fin.prod_univ_succ]

lemma outgoing_product (n : ℕ) (left : ℕ→A→ℝ) (y : A→ℝ) (a : Fin (n+1)→A) :
    (∏ j : Fin (n+1),outgoingWeight n left y j.val (a j))=
      (∏ j : Fin n,left j.val (a j.castSucc))*y (a (Fin.last n)) := by
  rw [Fin.prod_univ_castSucc]
  simp only [outgoingWeight,Fin.val_last,if_true,Fin.val_castSucc]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  rw [if_neg (Nat.ne_of_lt j.isLt)]

/-- Pointwise regrouping places each incidence factor at its physical vertex.
The zero-edge case is the single vertex weight x(a)*y(a). -/
lemma asymmetric_sourceTerm (n : ℕ) (left right : ℕ→A→ℝ) (gate : ℕ→A→A→ℝ)
    (x y : A→ℝ) (a : Fin (n+1)→A) :
    x (a 0)*(∏ j : Fin n,asymmetricMatrix left right gate j.val (a j.castSucc) (a j.succ))*y (a (Fin.last n))=
      sourceTerm n (vertexWeight n left right x y) gate (fun _ => 1) a := by
  simp only [sourceTerm,vertexWeight,Finset.prod_mul_distrib,mul_one]
  rw [incoming_product,outgoing_product]
  simp only [asymmetricMatrix,Finset.prod_mul_distrib]
  ring

/-- Exact asymmetric transfer normalization, with no nonnegativity hypotheses. -/
theorem path_asymmetric_exact (n : ℕ) (left right : ℕ→A→ℝ) (gate : ℕ→A→A→ℝ) (x y : A→ℝ) :
    x ⬝ᵥ (matrixRun n (asymmetricMatrix left right gate)*ᵥ y)=
      pathSource n (vertexWeight n left right x y) gate := by
  rw [path_expansion]
  unfold pathSource
  exact Finset.sum_congr rfl (fun a _ => asymmetric_sourceTerm n left right gate x y a)

end SubmittedGenus.CapFourMass.AsymmetricMatrixSource

import Results.Genus.CapFiveMass.ThresholdMatrices

/-!
# Zero-state extension for the original raw enumerator

The raw evaluator uses Fin6 (values0,...,5), with value0 rejected by its
positive domains. Adding a zero row and column to the actual transfer
matrices preserves the fourth trace and all endpoint energies exactly.
-/

noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFiveMass

abbrev BoundedState := Fin 6

def zeroExtend {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Fin.cases (fun _ => 0) (fun i => Fin.cases 0 (M i))

def zeroExtendVector {n : ℕ} (v : Fin n → ℝ) : Fin (n + 1) → ℝ := Fin.cases 0 v

lemma zeroExtend_mul {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℝ) :
    zeroExtend (M * N) = zeroExtend M * zeroExtend N := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [zeroExtend, Matrix.mul_apply, Fin.sum_univ_succ]

lemma zeroExtend_transpose {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    zeroExtend M.transpose = (zeroExtend M).transpose := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [zeroExtend, Matrix.transpose_apply]

lemma zeroExtend_trace {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    (zeroExtend M).trace = M.trace := by
  simp [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_succ, zeroExtend]

lemma zeroExtend_pow_succ {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) :
    zeroExtend (M ^ (k + 1)) = (zeroExtend M) ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, zeroExtend_mul, ih]
    exact (pow_succ _ (k + 1)).symm

lemma zeroExtendVector_energy {n : ℕ} (v : Fin n → ℝ) :
    MatrixBounds.vectorEnergy (zeroExtendVector v) = MatrixBounds.vectorEnergy v := by
  simp [MatrixBounds.vectorEnergy, zeroExtendVector, Fin.sum_univ_succ]

/-- Extension preserves the proved fourth-trace contractive data. -/
def extendControlled {n : ℕ} (M : MatrixBounds.Controlled (ι := Fin n)) :
    MatrixBounds.Controlled (ι := Fin (n + 1)) where
  matrix := zeroExtend M.matrix
  bound := M.bound
  bound_nonneg := M.bound_nonneg
  symmetric := by rw [← zeroExtend_transpose, M.symmetric]
  trace_le := by rw [← zeroExtend_pow_succ M.matrix 3, zeroExtend_trace]; exact M.trace_le

def strongTransferSix := extendControlled strongTransfer
def carryTransferSix := extendControlled carryTransfer

def endpointVectorSix (kind : EndpointKind) (z : ℝ) : BoundedState → ℝ :=
  zeroExtendVector (endpointVector kind z)

lemma endpointSix_energy_le (kind : EndpointKind) :
    MatrixBounds.vectorEnergy (endpointVectorSix kind radius) ≤ endpointBound kind := by
  rw [endpointVectorSix, zeroExtendVector_energy]
  exact endpoint_energy_le kind

lemma endpointSix_nonneg (kind : EndpointKind) (z : ℝ) (i : BoundedState) :
    0 ≤ endpointVectorSix kind z i := by
  refine Fin.cases ?_ (fun i => ?_) i
  · rfl
  · cases kind <;> simp only [endpointVectorSix, zeroExtendVector, Fin.cases_succ, endpointVector]
    · exact Real.sqrt_nonneg _
    · split_ifs <;> first | exact le_refl 0 | exact Real.sqrt_nonneg _
    · split_ifs <;> first | exact le_refl 0 | exact Real.sqrt_nonneg _

lemma thresholdSix_nonneg (t : ℕ) (z : ℝ) (i j : BoundedState) :
    0 ≤ zeroExtend (thresholdMatrix t z) i j := by
  refine Fin.cases ?_ (fun i => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · exact threshold_nonneg t z i j

end SubmittedGenus.CapFiveMass

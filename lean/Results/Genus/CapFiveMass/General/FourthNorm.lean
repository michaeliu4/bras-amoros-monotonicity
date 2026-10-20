import Results.Genus.CapFiveMass.General.Control

/-! The original t-state symmetric matrix and its literal Schatten fourth
norm. No fifth state is added to the four-state matrix in this interface. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFiveMass.General

def originalMatrix (t : ℕ) (z : ℝ) : Matrix (Fin t) (Fin t) ℝ :=
  fun i j => if t ≤ (i.val + 1) + (j.val + 1)
    then Real.sqrt (z ^ (i.val + 1)) * Real.sqrt (z ^ (j.val + 1)) else 0

/-- Literal displayed entry z^((i+j)/2), with physical states numbered 1 to t. -/
lemma originalMatrix_entry (t : ℕ) {z : ℝ} (hz : 0 ≤ z) (i j : Fin t) :
    originalMatrix t z i j = if t ≤ (i.val + 1) + (j.val + 1)
      then z ^ (((i.val + 1 + (j.val + 1) : ℕ) : ℝ) / 2) else 0 := by
  unfold originalMatrix
  split_ifs
  · rw [← Real.sqrt_mul (pow_nonneg hz _), ← pow_add, Real.sqrt_eq_rpow,
      ← Real.rpow_natCast, ← Real.rpow_mul hz]
    congr 1
    ring
  · rfl

lemma originalMatrix_symmetric (t : ℕ) (z : ℝ) :
    (originalMatrix t z).transpose = originalMatrix t z := by
  ext i j
  simp [Matrix.transpose_apply, originalMatrix, Nat.add_comm, mul_comm]

lemma original_four_entry_product (t : ℕ) {z : ℝ} (hz : 0 ≤ z) (i j k l : Fin t) :
    originalMatrix t z i j * (originalMatrix t z j k *
      (originalMatrix t z k l * originalMatrix t z l i)) =
    if t ≤ (i.val + 1) + (j.val + 1) ∧ t ≤ (j.val + 1) + (k.val + 1) ∧
       t ≤ (k.val + 1) + (l.val + 1) ∧ t ≤ (l.val + 1) + (i.val + 1)
    then z ^ ((i.val + 1) + (j.val + 1) + (k.val + 1) + (l.val + 1)) else 0 := by
  by_cases hij : t ≤ (i.val + 1) + (j.val + 1) <;>
    by_cases hjk : t ≤ (j.val + 1) + (k.val + 1) <;>
    by_cases hkl : t ≤ (k.val + 1) + (l.val + 1) <;>
    by_cases hli : t ≤ (l.val + 1) + (i.val + 1) <;>
    simp only [originalMatrix, hij, hjk, hkl, hli, and_self, and_true, and_false,
      ↓reduceIte, mul_zero, zero_mul]
  calc
    _ = Real.sqrt (z ^ (i.val + 1)) ^ 2 * Real.sqrt (z ^ (j.val + 1)) ^ 2 *
        Real.sqrt (z ^ (k.val + 1)) ^ 2 * Real.sqrt (z ^ (l.val + 1)) ^ 2 := by ring
    _ = _ := by
      rw [Real.sq_sqrt (pow_nonneg hz (i.val + 1)), Real.sq_sqrt (pow_nonneg hz (j.val + 1)),
        Real.sq_sqrt (pow_nonneg hz (k.val + 1)), Real.sq_sqrt (pow_nonneg hz (l.val + 1))]
      simp only [pow_add]

lemma originalMatrix_trace_fourth (t : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    ((originalMatrix t z) ^ 4).trace = fourthTrace t z := by
  have he (M : Matrix (Fin t) (Fin t) ℝ) : M ^ 4 = M * (M * (M * M)) := by noncomm_ring
  rw [he]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Finset.mul_sum]
  simp_rw [original_four_entry_product t hz]
  rfl

def fourthNorm (t : ℕ) (z : ℝ) : ℝ := (fourthTrace t z) ^ ((4 : ℝ)⁻¹)

lemma fourthNorm_eq_matrix (t : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    fourthNorm t z = (((originalMatrix t z) ^ 4).trace) ^ ((4 : ℝ)⁻¹) := by
  rw [originalMatrix_trace_fourth t hz]
  rfl

end SubmittedGenus.CapFiveMass.General

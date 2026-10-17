import Results.Genus.CapFiveMass.MatrixBounds
import Mathlib.Tactic.FieldSimp

/-!
# Finite positive-test-vector Schur contraction

This proves the Euclidean contraction used in the submitted cap-four spectral
argument directly from its rational positive test vectors.  It does not assume
a spectral radius estimate or use a Perron--Frobenius oracle.
-/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass
open CapFiveMass.MatrixBounds

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Weighted finite Cauchy--Schwarz, with no square-root denominators. -/
lemma weighted_row_sq_le (a x v : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hx : ∀ i, 0 < x i) :
    (∑ i, a i * v i)^2 ≤ (∑ i, a i*x i) * ∑ i, a i*(v i)^2/x i := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun i _ => mul_nonneg (ha i) (hx i).le)
    (fun i _ => div_nonneg (mul_nonneg (ha i) (sq_nonneg _)) (hx i).le)
  intro i _
  have hi : x i ≠ 0 := ne_of_gt (hx i)
  apply le_of_eq
  field_simp

/-- A symmetric nonnegative matrix with a positive row supersolution is a
Euclidean contraction. This is the finite Schur test in squared form. -/
theorem positive_test_energy_le (A : Matrix ι ι ℝ) (x : ι → ℝ) (R : ℝ)
    (hA : A.transpose = A) (hpos : ∀ i j, 0 ≤ A i j)
    (hx : ∀ i, 0 < x i) (hR : 0 ≤ R)
    (hrow : ∀ i, (A *ᵥ x) i ≤ R*x i) (v : ι → ℝ) :
    vectorEnergy (A *ᵥ v) ≤ R^2*vectorEnergy v := by
  have hs (i j : ι) : A i j = A j i := by
    have hh := congrFun (congrFun hA j) i
    exact hh
  calc
    vectorEnergy (A *ᵥ v) ≤
        ∑ i, (R*x i)*(∑ j, A i j*(v j)^2/x j) := by
      apply Finset.sum_le_sum
      intro i _
      exact (weighted_row_sq_le (A i) x v (hpos i) hx).trans
        (mul_le_mul_of_nonneg_right (hrow i)
          (Finset.sum_nonneg fun j _ => div_nonneg
            (mul_nonneg (hpos i j) (sq_nonneg _)) (hx j).le))
    _ = ∑ j, (R*(v j)^2/x j)*(A *ᵥ x) j := by
      simp only [Finset.mul_sum, Matrix.mulVec, dotProduct]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      rw [hs i j]
      ring
    _ ≤ ∑ j, (R*(v j)^2/x j)*(R*x j) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (hrow j)
        (div_nonneg (mul_nonneg hR (sq_nonneg _)) (hx j).le)
    _ = R^2*vectorEnergy v := by
      rw [vectorEnergy, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      field_simp [ne_of_gt (hx j)]
      <;> ring

/-- A squared Euclidean operator estimate propagates to every matrix power. -/
theorem power_energy_le (A : Matrix ι ι ℝ) (R : ℝ)
    (hA : ∀ v, vectorEnergy (A *ᵥ v) ≤ R^2*vectorEnergy v)
    (n : ℕ) (v : ι → ℝ) :
    vectorEnergy ((A^n) *ᵥ v) ≤ R^(2*n)*vectorEnergy v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    calc
      vectorEnergy (A *ᵥ ((A^n) *ᵥ v)) ≤ R^2*vectorEnergy ((A^n) *ᵥ v) := hA _
      _ ≤ R^2*(R^(2*n)*vectorEnergy v) :=
        mul_le_mul_of_nonneg_left ih (sq_nonneg _)
      _ = _ := by rw [Nat.mul_succ, pow_add]; ring

/-- General bilinear power estimate, the basis of all-power moment control. -/
theorem power_bilinear_sq_le (A : Matrix ι ι ℝ) (R : ℝ)
    (hA : ∀ v, vectorEnergy (A *ᵥ v) ≤ R^2*vectorEnergy v)
    (n : ℕ) (x y : ι → ℝ) :
    (x ⬝ᵥ ((A^n) *ᵥ y))^2 ≤ R^(2*n)*vectorEnergy x*vectorEnergy y := by
  have h := (dot_sq_le x ((A^n) *ᵥ y)).trans
    (mul_le_mul_of_nonneg_left (power_energy_le A R hA n y) (vectorEnergy_nonneg x))
  simpa only [mul_assoc, mul_left_comm, mul_comm] using h

end SubmittedGenus.CapFourMass

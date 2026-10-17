import Results.Genus.CapFourMass.SpectralMatrices
import Mathlib.Analysis.CStarAlgebra.Matrix

/-! Literal Euclidean operator-norm versions of the submitted strict Schur
certificates. The scoped matrix norm is mathlib's L2 operator norm. -/
noncomputable section
open scoped BigOperators Matrix Matrix.Norms.L2Operator
namespace SubmittedGenus
namespace CapFiveMass.MatrixBounds

lemma operator_norm_le_of_energy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (a : ℝ) (ha : 0≤a)
    (hA : ∀ v,vectorEnergy (A*ᵥ v)≤a^2*vectorEnergy v) : ‖A‖≤a := by
  rw [←Matrix.l2_opNorm_toEuclideanCLM]
  apply ContinuousLinearMap.opNorm_le_bound _ ha
  intro v
  have h:=hA (fun i => v i)
  have hi : ‖v‖^2=vectorEnergy (fun i => v i) := by
    exact EuclideanSpace.real_norm_sq_eq v
  have ho : ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A) v‖^2=vectorEnergy (A*ᵥ fun i => v i) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    rfl
  have hp:=norm_nonneg ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A) v)
  have hq:=mul_nonneg ha (norm_nonneg v)
  nlinarith

end CapFiveMass.MatrixBounds
namespace CapFourMass
open CapFiveMass.MatrixBounds

/-- The manuscript's literal strict spectral/Euclidean norm bound for D. -/
theorem strong_operator_norm_lt : ‖strongMatrix‖<strongBound := by
  exact (operator_norm_le_of_energy strongMatrix strongInner
    (by norm_num [strongInner,strongBound]) strong_energy_inner).trans_lt
    (by norm_num [strongInner,strongBound])

/-- The manuscript's literal strict spectral/Euclidean norm bound for E. -/
theorem restricted_operator_norm_lt : ‖restrictedMatrix‖<restrictedBound := by
  exact (operator_norm_le_of_energy restrictedMatrix restrictedInner
    (by norm_num [restrictedInner,restrictedBound]) restricted_energy_inner).trans_lt
    (by norm_num [restrictedInner,restrictedBound])

end CapFourMass
end SubmittedGenus

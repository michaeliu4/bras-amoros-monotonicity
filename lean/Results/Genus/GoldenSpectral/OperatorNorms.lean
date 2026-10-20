import Results.Genus.CapFourMass.OperatorNorms
import Results.Genus.GoldenSpectral.Matrices

/-! Literal golden-q Euclidean operator norms from the exact positive-vector
energy certificates, under mathlib's L2 operator matrix norm. -/
noncomputable section
open scoped Matrix.Norms.L2Operator
namespace SubmittedGenus.GoldenSpectral
open CapFiveMass.MatrixBounds

theorem strong_operator_norm_lt : ‖strongMatrix‖<strongBound := by
  exact (operator_norm_le_of_energy strongMatrix strongInner
    (by norm_num [strongInner,strongBound]) strong_energy_inner).trans_lt
    (by norm_num [strongInner,strongBound])

theorem restricted_operator_norm_lt : ‖restrictedMatrix‖<restrictedBound := by
  exact (operator_norm_le_of_energy restrictedMatrix restrictedInner
    (by norm_num [restrictedInner,restrictedBound]) restricted_energy_inner).trans_lt
    (by norm_num [restrictedInner,restrictedBound])

end SubmittedGenus.GoldenSpectral

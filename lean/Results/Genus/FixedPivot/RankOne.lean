import Results.Genus.FixedPivot.SpectralTransfer

/-! Rational weighted rank-one endpoint factors for the original pure modes. -/
namespace SubmittedGenus.FixedPivot
open scoped BigOperators
section Ring
variable {R : Type*} [CommRing R]

def carryEigenvector (z theta : R) : Fin 3 → R := ![carryB z,theta,theta]

def carryEndpointWeight (z theta : R) (i : Fin 3) : R :=
  carryWeight z i*carryEigenvector z theta i

def carryWeightedDot (z theta : R) (v : Fin 3 → R) : R :=
  ∑ i : Fin 3, carryEndpointWeight z theta i*v i

def carryEigenNorm (z theta : R) : R :=
  ∑ i : Fin 3, carryWeight z i*(carryEigenvector z theta i)^2

lemma carry_root_equation (z theta other : R)
    (hb : theta+other=carryB z) (hc : theta*other=carryC z) :
    theta^2-carryB z*theta+carryC z=0 := by
  rw [← hb,← hc]
  ring

lemma carryWeightedDot_eq (z theta : R) (v : Fin 3 → R) :
    carryWeightedDot z theta v =
      z*carryB z*v 0+z^2*theta*v 1+z^3*theta*v 2 := by
  simp [carryWeightedDot,carryEndpointWeight,carryWeight,carryEigenvector,Fin.sum_univ_succ]
  ring

/-- A polynomial eigenvector uses no square roots and no extra denominators. -/
lemma carryEigenvector_eigen (z theta other : R)
    (hb : theta+other=carryB z) (hc : theta*other=carryC z) :
    carryStep z (carryEigenvector z theta)=fun i => theta*carryEigenvector z theta i := by
  have hq:=carry_root_equation z theta other hb hc
  funext i
  fin_cases i
  · simp [carryStep,carryEigenvector,carryB]
    ring
  · simp [carryStep,carryEigenvector,carryB]
    unfold carryB carryC at hq
    linear_combination -hq
  · simp [carryStep,carryEigenvector,carryB]
    unfold carryB carryC at hq
    linear_combination -hq

/-- The weighted norm appearing in each rank-one projector has exactly the
allowed factors b, theta and theta−other. -/
lemma carryEigenNorm_eq (z theta other : R)
    (hb : theta+other=carryB z) (hc : theta*other=carryC z) :
    carryEigenNorm z theta=carryB z*theta*(theta-other) := by
  have hq:=carry_root_equation z theta other hb hc
  have ho : other=carryB z-theta := by linear_combination hb
  rw [ho]
  simp [carryEigenNorm,carryWeight,carryEigenvector,Fin.sum_univ_succ]
  unfold carryB carryC at *
  linear_combination -(z^2+z^3)*hq

/-- Every port-to-port projection splits into one factor at each endpoint.
Multiplication by b avoids introducing inverses in this identity. -/
lemma carryStep_rank_one_numerator (z theta other : R)
    (hb : theta+other=carryB z) (hc : theta*other=carryC z)
    (v : Fin 3 → R) (i : Fin 3) :
    carryB z*(carryStep z (carryStep z v) i-other*carryStep z v i)=
      carryEigenvector z theta i*carryWeightedDot z theta v := by
  have hq:=carry_root_equation z theta other hb hc
  have ho : other=carryB z-theta := by linear_combination hb
  rw [ho,carryWeightedDot_eq]
  fin_cases i
  · simp [carryStep,carryEigenvector,carryB]
    ring
  · simp [carryStep,carryEigenvector,carryB]
    unfold carryB carryC at hq
    linear_combination -(z^2*v 1+z^3*v 2)*hq
  · simp [carryStep,carryEigenvector,carryB]
    unfold carryB carryC at hq
    linear_combination -(z^2*v 1+z^3*v 2)*hq

lemma free_endpoint_factor (z theta : R) :
    carryWeightedDot z theta freeTerminal=carryB z*(z+theta) := by
  rw [carryWeightedDot_eq]
  simp [freeTerminal,carryB]
  ring

lemma loop_endpoint_factor (z theta : R) :
    carryWeightedDot z theta loopTerminal=carryB z*theta := by
  rw [carryWeightedDot_eq]
  simp [loopTerminal,carryB]
  ring

end Ring
end SubmittedGenus.FixedPivot

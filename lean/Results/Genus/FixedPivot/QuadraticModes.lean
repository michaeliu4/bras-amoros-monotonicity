import Results.Genus.FixedPivot.CarryTransfer
import Mathlib.Algebra.QuadraticAlgebra.Basic

/-!
# Rational quadratic carry modes
The root algebra adjoins a root of T²−bT+c. Its explicit rank-two coordinates
and conjugation allow denominator-controlled descent without introducing any
square root of the vertex-weight variable.
-/
namespace SubmittedGenus.FixedPivot

section Algebra
variable {R : Type*} [CommRing R]

abbrev CarryAlgebra (b c : R) := QuadraticAlgebra R (-c) b

def carryRoot (b c : R) : CarryAlgebra b c := QuadraticAlgebra.omega

def carryConjugate (b c : R) : CarryAlgebra b c := star (carryRoot b c)

lemma carry_roots_sum (b c : R) :
    carryRoot b c+carryConjugate b c=algebraMap R (CarryAlgebra b c) b := by
  ext <;> simp [carryRoot,carryConjugate,QuadraticAlgebra.omega]

lemma carry_roots_product (b c : R) :
    carryRoot b c*carryConjugate b c=algebraMap R (CarryAlgebra b c) c := by
  ext <;> simp [carryRoot,carryConjugate,QuadraticAlgebra.omega]

def carryDiscriminant (b c : R) : R := b^2-4*c

lemma carry_root_difference_square (b c : R) :
    (carryRoot b c-carryConjugate b c)^2 =
      algebraMap R (CarryAlgebra b c) (carryDiscriminant b c) := by
  rw [pow_two]
  ext <;> simp [carryRoot,carryConjugate,QuadraticAlgebra.omega,carryDiscriminant,pow_two] <;> ring

/-- The exact submitted discriminant factorization. -/
lemma carryDiscriminant_source (z : R) :
    carryDiscriminant (carryB z) (carryC z)=z^3*(z+1)*(z^2+z+4) := by
  unfold carryDiscriminant carryB carryC
  ring

/-- The integer source of the localization denominator cΔ. -/
lemma carry_localization_denominator (z : R) :
    carryC z*carryDiscriminant (carryB z) (carryC z)=
      -z^6*(z+1)^2*(z^2+z+4) := by
  unfold carryDiscriminant carryB carryC
  ring

lemma carryRoot_norm (b c : R) :
    QuadraticAlgebra.norm (carryRoot b c)=c := by
  simp [QuadraticAlgebra.norm_def,carryRoot,QuadraticAlgebra.omega]

lemma carryRoot_difference_norm (b c : R) :
    QuadraticAlgebra.norm (carryRoot b c-carryConjugate b c)= -carryDiscriminant b c := by
  simp [QuadraticAlgebra.norm_def,carryRoot,carryConjugate,QuadraticAlgebra.omega,
    carryDiscriminant]
  ring

lemma carryRoot_isUnit (b c : R) (hc : IsUnit c) : IsUnit (carryRoot b c) := by
  rw [QuadraticAlgebra.isUnit_iff_norm_isUnit,carryRoot_norm]
  exact hc

lemma carryRoot_difference_isUnit (b c : R) (hΔ : IsUnit (carryDiscriminant b c)) :
    IsUnit (carryRoot b c-carryConjugate b c) := by
  rw [QuadraticAlgebra.isUnit_iff_norm_isUnit,carryRoot_difference_norm]
  exact hΔ.neg

/-- Explicit inverse of the root: only the base denominator c is used. -/
def carryRootInverse (b c ci : R) : CarryAlgebra b c :=
  carryConjugate b c*algebraMap R (CarryAlgebra b c) ci

lemma carryRoot_mul_inverse (b c ci : R) (hc : c*ci=1) :
    carryRoot b c*carryRootInverse b c ci=1 := by
  rw [carryRootInverse,← mul_assoc,carry_roots_product,← map_mul,hc,map_one]

/-- Explicit inverse of the root difference: only Δ is used. -/
def carryDifferenceInverse (b c Δi : R) : CarryAlgebra b c :=
  (carryRoot b c-carryConjugate b c)*algebraMap R (CarryAlgebra b c) Δi

lemma carryDifference_mul_inverse (b c Δi : R) (hΔ : carryDiscriminant b c*Δi=1) :
    (carryRoot b c-carryConjugate b c)*carryDifferenceInverse b c Δi=1 := by
  rw [carryDifferenceInverse,← mul_assoc,← pow_two,carry_root_difference_square,
    ← map_mul,hΔ,map_one]

end Algebra

section Descent
variable {R : Type*} [CommRing R] [NoZeroDivisors R] [CharZero R]

/-- Conjugation fixes precisely the coefficient ring in the free quadratic algebra. -/
theorem carryAlgebra_fixed_iff {b c : R} (x : CarryAlgebra b c) :
    star x=x ↔ ∃ r : R, algebraMap R (CarryAlgebra b c) r=x := by
  constructor
  · intro hx
    have hi : -x.im=x.im := congrArg QuadraticAlgebra.im hx
    have htwo : (2 : R)*x.im=0 := by
      calc (2 : R)*x.im=x.im-(-x.im) := by ring
           _ = 0 := by rw [hi]; ring
    have him : x.im=0 := (mul_eq_zero.mp htwo).resolve_left (by norm_num)
    refine ⟨x.re, ?_⟩
    ext <;> simp [him]
  · rintro ⟨r,rfl⟩
    ext <;> simp

end Descent
end SubmittedGenus.FixedPivot

import Results.Genus.FiniteArithmetic.Reservoir.Bivariate.Identities
import Results.Genus.FiniteArithmetic.Reservoir.Bivariate.Failure
import Mathlib.RingTheory.PowerSeries.Inverse

namespace SubmittedGenus.FiniteArithmetic.Reservoir.Bivariate
open PowerSeries
open scoped BigOperators
noncomputable section

/-- A denominator of constant coefficient one has its canonical formal inverse. -/
theorem solve_unit_denominator {R : Type} [CommRing R]
    {d a b : PowerSeries R} (hd : constantCoeff d=1) (h : d*a=b) :
    a=b*PowerSeries.invOfUnit d 1 := by
  have hi := PowerSeries.mul_invOfUnit d 1 hd
  calc
    a=a*(d*PowerSeries.invOfUnit d 1) := by rw [hi,mul_one]
    _=(d*a)*PowerSeries.invOfUnit d 1 := by ring
    _=_ := by rw [h]

def safeDenominator : PowerSeries (Polynomial ℤ) :=
  (1-lift v)*(1-lift v*T)*(1-lift v*T^2)

def safeNumerator : PowerSeries (Polynomial ℤ) :=
  X^3*(1+lift u)*(1-lift v*T)*(1-lift v*T^2) +
    X^6*lift u*(1+lift u)*T*(1-lift v*T^2) +
    X^6*T*(1+lift s*T)*(1-lift v)

def earlyDenominator : PowerSeries (Polynomial ℤ) :=
  (1-lift u)*(1-(lift u)^2)*(1-lift u*T)*(1-(lift u)^2*T)*
    (1-(lift u)^2*T^2)

def earlyNumerator : PowerSeries (Polynomial ℤ) :=
  X^6*(1-lift u*T)*(1-(lift u)^2*T)*(1-(lift u)^2*T^2) +
    X^9*T*(1-(lift u)^2*T)*(1-(lift u)^2*T^2) +
    X^9*lift u*T^2*(1-lift u)*(1-(lift u)^2*T^2) +
    X^9*lift u*T^4*(1-lift u)*(1-(lift u)^2)

@[simp] theorem safeDenominator_constant : constantCoeff safeDenominator=1 := by
  simp [safeDenominator,lift,v,u,s]

@[simp] theorem earlyDenominator_constant : constantCoeff earlyDenominator=1 := by
  simp [earlyDenominator,lift,u]

/-- Rational presentation of the physical bivariate safe marked source.
Its denominator is proved invertible, rather than an assumed unit. -/
theorem safe_rational : safe=safeNumerator*PowerSeries.invOfUnit safeDenominator 1 :=
  solve_unit_denominator safeDenominator_constant safe_identity

/-- Rational presentation of the physical bivariate early marked source. -/
theorem early_rational : early=earlyNumerator*PowerSeries.invOfUnit earlyDenominator 1 :=
  solve_unit_denominator earlyDenominator_constant early_identity

/-- Original failure-operator expression with its genuine formal division
by 1-c. This is valid for every coefficientwise locally finite marked series. -/
theorem failureOperator_rational (F : PowerSeries (Polynomial ℤ)) :
    failureOperator F = X*((specialize F 1-specialize F c)*
      PowerSeries.invOfUnit (1-c) 1+failureBlockSeries*specialize F c) := by
  have hi : (1-c)*PowerSeries.invOfUnit (1-c) 1=1 :=
    PowerSeries.mul_invOfUnit _ 1 (by simp [c])
  have h := solve_unit_denominator (d := 1-c) (by simp [c]) (failureOperator_identity F)
  rw [h]
  calc
    _=X*((specialize F 1-specialize F c)*PowerSeries.invOfUnit (1-c) 1+
      failureBlockSeries*specialize F c*((1-c)*PowerSeries.invOfUnit (1-c) 1)) := by ring
    _=_ := by rw [hi,mul_one]

#print axioms safe_rational
#print axioms early_rational
#print axioms failureOperator_rational
end
end SubmittedGenus.FiniteArithmetic.Reservoir.Bivariate

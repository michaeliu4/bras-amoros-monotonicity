import Results.Genus.FiniteArithmetic.Reservoir.Bivariate.Source

namespace SubmittedGenus.FiniteArithmetic.Reservoir.Bivariate
open PowerSeries
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Substitute any formal series for the independent distance variable.
The polynomial coefficient at each weight makes even substitution at one
coefficientwise finite, without any analytic convergence hypothesis. -/
def specialize (F : PowerSeries (Polynomial ℤ)) (t : PowerSeries ℤ) : PowerSeries ℤ :=
  gradedTransform (fun n => (PowerSeries.coeff n F).eval₂ PowerSeries.C t)

/-- The linear substitution sending a distance monomial to the exact failure
tail series at that distance. It also permits signed coefficients. -/
def polynomialFailure (p : Polynomial ℤ) : PowerSeries ℤ :=
  p.sum (fun d a => PowerSeries.C a * failureTailSeries d)

theorem polynomialFailure_add (p q : Polynomial ℤ) :
    polynomialFailure (p+q)=polynomialFailure p+polynomialFailure q := by
  apply Polynomial.sum_add_index
  · intro d; simp
  · intro d a b; rw [map_add,add_mul]

def polynomialFailureHom : Polynomial ℤ →+ PowerSeries ℤ where
  toFun := polynomialFailure
  map_zero' := by simp [polynomialFailure]
  map_add' := polynomialFailure_add

@[simp] theorem polynomialFailure_X_pow (d : ℕ) :
    polynomialFailure (Polynomial.X^d)=failureTailSeries d := by
  rw [Polynomial.X_pow_eq_monomial]
  simp [polynomialFailure]

/-- General original failure operator on arbitrary weight-graded polynomial
rows. Equivalently this is any coefficientwise locally finite family F_d. -/
def failureOperator (F : PowerSeries (Polynomial ℤ)) : PowerSeries ℤ :=
  X*gradedTransform (fun n => polynomialFailure (PowerSeries.coeff n F))

theorem polynomialFailure_clear (p : Polynomial ℤ) :
    polynomialFailure p*(1-c) =
      p.eval₂ PowerSeries.C 1-p.eval₂ PowerSeries.C c+
        p.eval₂ PowerSeries.C c*failureBlockSeries*(1-c) := by
  simp only [polynomialFailure,Polynomial.eval₂_eq_sum,Polynomial.sum_def,
    Finset.sum_mul]
  rw [←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  calc
    _ = PowerSeries.C (p.coeff d)*(failureTailSeries d*(1-c)) := by ring
    _ = _ := by rw [failureTailSeries_clear]; ring

/-- The displayed original operator identity for every locally finite
marked series, rather than only the two physical prefix families. -/
theorem failureOperator_identity (F : PowerSeries (Polynomial ℤ)) :
    (1-c)*failureOperator F =
      X*(specialize F 1-specialize F c)+
        (1-c)*X*failureBlockSeries*specialize F c := by
  have h : gradedTransform (fun n => polynomialFailure (PowerSeries.coeff n F))*(1-c) =
      specialize F 1-specialize F c+
        specialize F c*failureBlockSeries*(1-c) := by
    rw [←gradedTransform_mul]
    rw [gradedTransform_congr (fun n => polynomialFailure_clear (PowerSeries.coeff n F))]
    rw [gradedTransform_add,gradedTransform_sub,gradedTransform_mul,gradedTransform_mul]
    rfl
  unfold failureOperator
  calc
    _ = X*(gradedTransform (fun n => polynomialFailure (PowerSeries.coeff n F))*(1-c)) := by ring
    _ = _ := by rw [h]; ring

theorem specialize_markedSource {C : Type} (F : OriginalReservoir.PrefixFamily C)
    (t : PowerSeries ℤ) : specialize (markedSource F) t=markedPrefixSeries F t := by
  unfold specialize markedSource markedPrefixSeries
  apply gradedTransform_congr
  intro n
  simp only [PowerSeries.coeff_mk]
  change (Polynomial.eval₂RingHom PowerSeries.C t)
      (∑ p : OriginalReservoir.PrefixOccurrence F n,Polynomial.X^p.distance)=_
  simp

/-- The general operator agrees with the actual failed-mark population,
including multiplicity, the empty failing tail, and the extra genus unit. -/
theorem failureOperator_markedSource {C : Type} (F : OriginalReservoir.PrefixFamily C) :
    failureOperator (markedSource F)=actualFailureSeries F := by
  rw [actualFailureSeries_transform]
  unfold failureOperator markedSource
  congr 1
  apply gradedTransform_congr
  intro n
  simp only [PowerSeries.coeff_mk]
  change polynomialFailureHom
      (∑ p : OriginalReservoir.PrefixOccurrence F n,Polynomial.X^p.distance)=_
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro p hp
  exact polynomialFailure_X_pow p.distance

#print axioms failureOperator_identity
#print axioms failureOperator_markedSource
end
end SubmittedGenus.FiniteArithmetic.Reservoir.Bivariate

import Results.Genus.FiniteArithmetic.Reservoir.Bivariate.Failure

namespace SubmittedGenus.FiniteArithmetic.Reservoir.Bivariate
open PowerSeries
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Each bivariate coefficient counts actual occurrences, with multiplicity. -/
theorem markedSource_coeff {C : Type} (F : OriginalReservoir.PrefixFamily C) (n d : ℕ) :
    (PowerSeries.coeff n (markedSource F)).coeff d =
      (Fintype.card {p : OriginalReservoir.PrefixOccurrence F n // p.distance=d} : ℤ) := by
  simp only [markedSource,PowerSeries.coeff_mk,Polynomial.finsetSum_coeff,
    Polynomial.coeff_X_pow,Fintype.card_subtype]
  simp [eq_comm]

theorem markedSource_coeff_nonneg {C : Type} (F : OriginalReservoir.PrefixFamily C) (n d : ℕ) :
    0≤(PowerSeries.coeff n (markedSource F)).coeff d := by
  rw [markedSource_coeff]
  positivity

@[simp] theorem failureOperator_coeff_zero (F : PowerSeries (Polynomial ℤ)) :
    PowerSeries.coeff 0 (failureOperator F)=0 := by
  simp [failureOperator]

/-- Exact finite convolution, valid even for signed input rows. -/
theorem failureOperator_coeff_succ (F : PowerSeries (Polynomial ℤ)) (g : ℕ) :
    PowerSeries.coeff (g+1) (failureOperator F) =
      ∑ n : Fin (g+1), ∑ d ∈ (PowerSeries.coeff n.val F).support,
        (PowerSeries.coeff n.val F).coeff d *
          PowerSeries.coeff (g-n.val) (failureTailSeries d) := by
  rw [failureOperator,PowerSeries.coeff_succ_X_mul,gradedTransform_coeff]
  simp only [polynomialFailure,Polynomial.sum_def,map_sum,PowerSeries.coeff_C_mul]

theorem failureOperator_coeff_nonneg (F : PowerSeries (Polynomial ℤ))
    (h : ∀ n d,0≤(PowerSeries.coeff n F).coeff d) (g : ℕ) :
    0≤PowerSeries.coeff g (failureOperator F) := by
  cases g with
  | zero => simp
  | succ g =>
    rw [failureOperator_coeff_succ]
    apply Finset.sum_nonneg
    intro n hn
    apply Finset.sum_nonneg
    intro d hd
    rw [failureTailSeries_coeff]
    exact mul_nonneg (h _ _) (by positivity)

#print axioms markedSource_coeff
#print axioms failureOperator_coeff_succ
#print axioms failureOperator_coeff_nonneg
end
end SubmittedGenus.FiniteArithmetic.Reservoir.Bivariate

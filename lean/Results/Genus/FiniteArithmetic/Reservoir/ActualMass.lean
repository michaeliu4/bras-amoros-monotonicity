import Results.Genus.FiniteArithmetic.Reservoir.FailureEvaluation
import Results.Genus.Injection.ReservoirSources.DecoratedOccurrences

namespace SubmittedGenus.FiniteArithmetic.Reservoir
open PowerSeries Analytic OriginalReservoir
noncomputable section

theorem safeMarked_physical_one_evaluates :
    PositiveEval radius (markedPrefixSeries safeFamily 1) (safeMarkedValue 1) := by
  have h := safeMarked_evaluates unitDecoration 1 unit_decoration_evaluates (Or.inl rfl)
  rw [safeMarkedSeries_eq_physical,unitDecoration_series] at h
  exact h

theorem safeMarked_physical_c_evaluates :
    PositiveEval radius (markedPrefixSeries safeFamily c) (safeMarkedValue cValueAt) := by
  have h := safeMarked_evaluates binaryDecoration cValueAt binary_decoration_evaluates (Or.inr rfl)
  rw [safeMarkedSeries_eq_physical,binaryDecoration_series] at h
  exact h

theorem earlyMarked_physical_one_evaluates :
    PositiveEval radius (markedPrefixSeries earlyFamily 1) (earlyMarkedValue 1) := by
  have h := earlyMarked_evaluates unitDecoration 1 unit_decoration_evaluates (Or.inl rfl)
  rw [earlyMarkedSeries_eq_physical,unitDecoration_series] at h
  exact h

theorem earlyMarked_physical_c_evaluates :
    PositiveEval radius (markedPrefixSeries earlyFamily c) (earlyMarkedValue cValueAt) := by
  have h := earlyMarked_evaluates binaryDecoration cValueAt binary_decoration_evaluates (Or.inr rfl)
  rw [earlyMarkedSeries_eq_physical,binaryDecoration_series] at h
  exact h

theorem actual_safe_failure_evaluates :
    PositiveEval radius (actualFailureSeries safeFamily) safeFailureValue :=
  actualFailure_evaluates safeFamily safeMarked_physical_one_evaluates safeMarked_physical_c_evaluates

theorem actual_early_failure_evaluates :
    PositiveEval radius (actualFailureSeries earlyFamily) earlyFailureValue :=
  actualFailure_evaluates earlyFamily earlyMarked_physical_one_evaluates earlyMarked_physical_c_evaluates

/-- The original total error uses actual physical failed-mark populations. -/
def actualErrorSeries : PowerSeries ℤ := safeErrorSeries+earlyErrorSeries+
  actualFailureSeries safeFamily+actualFailureSeries earlyFamily

theorem actual_error_evaluates : PositiveEval radius actualErrorSeries totalErrorValue :=
  ((safeError_evaluates.add radius_nonneg earlyError_evaluates).add radius_nonneg
    actual_safe_failure_evaluates).add radius_nonneg actual_early_failure_evaluates

/-- Complete original mass input: source semantics, convergence and exact
rational evaluation are proved before the numerical bound is applied. -/
theorem actual_error_mass_lt_seventy_eight : SummableAt radius actualErrorSeries ∧
    normAt radius actualErrorSeries<78 :=
  ⟨actual_error_evaluates.summable,actual_error_evaluates.norm.trans_lt totalErrorValue_lt_seventy_eight⟩

#print axioms actual_error_mass_lt_seventy_eight
end
end SubmittedGenus.FiniteArithmetic.Reservoir

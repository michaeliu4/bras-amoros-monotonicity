import Results.Genus.FiniteArithmetic.Reservoir.Bivariate.Source
import Results.Genus.Injection.ReservoirSources.DecoratedOccurrences

namespace SubmittedGenus.FiniteArithmetic.Reservoir.Bivariate
open PowerSeries
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- An arbitrary finite number of zero-weight decorations specializes the
independent mark variable to that natural number, including zero. -/
def naturalDecoration (k : ℕ) : Decoration := ⟨Fin k,inferInstance,fun _ => 0⟩

@[simp] theorem naturalDecoration_series (k : ℕ) :
    (naturalDecoration k).series=PowerSeries.C (k : ℤ) := by
  change (∑ _a : Fin k, (X : PowerSeries ℤ)^0)=_
  simp only [pow_zero,Finset.sum_const,Finset.card_univ]
  rw [Fintype.card_fin]
  simp

/-- The independent mark-distance indeterminate. -/
def T : PowerSeries (Polynomial ℤ) := PowerSeries.C Polynomial.X

/-- Literal bivariate series of physical marks in safe prefixes. -/
def safe : PowerSeries (Polynomial ℤ) := markedSource OriginalReservoir.safeFamily

/-- Literal bivariate series of physical marks in early-single-one prefixes. -/
def early : PowerSeries (Polynomial ℤ) := markedSource OriginalReservoir.earlyFamily

/-- Original displayed safe marked-prefix formula, with all denominators
cleared. The distance variable is independent of the outer weight variable. -/
theorem safe_identity :
    (1-lift v)*(1-lift v*T)*(1-lift v*T^2)*safe =
      X^3*(1+lift u)*(1-lift v*T)*(1-lift v*T^2) +
      X^6*lift u*(1+lift u)*T*(1-lift v*T^2) +
      X^6*T*(1+lift s*T)*(1-lift v) := by
  apply ext_nat_eval
  intro k
  have h := safeMarkedSeries_identity (naturalDecoration k)
  rw [safeMarkedSeries_eq_physical,naturalDecoration_series] at h
  simpa only [safe,T,map_mul,map_sub,map_add,map_one,map_pow,evalAt_lift,
    evalAt_X,evalAt_markVariable,evalAt_markedSource] using h

/-- Original displayed early marked-prefix formula, with all denominators
cleared, for the independent distance indeterminate. -/
theorem early_identity :
    (1-lift u)*(1-(lift u)^2)*(1-lift u*T)*(1-(lift u)^2*T)*
      (1-(lift u)^2*T^2)*early =
      X^6*(1-lift u*T)*(1-(lift u)^2*T)*(1-(lift u)^2*T^2) +
      X^9*T*(1-(lift u)^2*T)*(1-(lift u)^2*T^2) +
      X^9*lift u*T^2*(1-lift u)*(1-(lift u)^2*T^2) +
      X^9*lift u*T^4*(1-lift u)*(1-(lift u)^2) := by
  apply ext_nat_eval
  intro k
  have h := earlyMarkedSeries_identity (naturalDecoration k)
  rw [earlyMarkedSeries_eq_physical,naturalDecoration_series] at h
  simpa only [early,T,map_mul,map_sub,map_add,map_one,map_pow,evalAt_lift,
    evalAt_X,evalAt_markVariable,evalAt_markedSource] using h

#print axioms safe_identity
#print axioms early_identity
end
end SubmittedGenus.FiniteArithmetic.Reservoir.Bivariate

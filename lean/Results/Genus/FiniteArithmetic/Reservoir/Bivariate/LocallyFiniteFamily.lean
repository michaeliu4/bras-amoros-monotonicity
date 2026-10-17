import Results.Genus.FiniteArithmetic.Reservoir.Bivariate.DistanceSum
import Results.Genus.FiniteArithmetic.Reservoir.Bivariate.Rational

namespace SubmittedGenus.FiniteArithmetic.Reservoir.Bivariate
open PowerSeries
open scoped BigOperators PowerSeries.WithPiTopology
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Exact local-finiteness condition needed for the formal substitutions at
one and at c in the original arbitrary marked-family operator. -/
def LocallyFiniteFamily (f : ℕ → PowerSeries ℤ) : Prop :=
  ∀ n,Set.Finite {d | PowerSeries.coeff n (f d)≠0}

/-- Every locally finite distance-indexed family has a polynomial-valued
weight grading; no positivity or uniform distance cutoff is required. -/
def fromFamily (f : ℕ → PowerSeries ℤ) (hf : LocallyFiniteFamily f) :
    PowerSeries (Polynomial ℤ) :=
  PowerSeries.mk (fun n => ∑ d ∈ (hf n).toFinset,
    Polynomial.monomial d (PowerSeries.coeff n (f d)))

theorem fromFamily_coeff (f : ℕ → PowerSeries ℤ) (hf : LocallyFiniteFamily f) (n d : ℕ) :
    (PowerSeries.coeff n (fromFamily f hf)).coeff d=PowerSeries.coeff n (f d) := by
  simp only [fromFamily,PowerSeries.coeff_mk,Polynomial.finsetSum_coeff,
    Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  by_cases h : PowerSeries.coeff n (f d)=0
  · simp [h]
  · simp [h]

@[simp] theorem distanceSlice_fromFamily (f : ℕ → PowerSeries ℤ)
    (hf : LocallyFiniteFamily f) (d : ℕ) : distanceSlice (fromFamily f hf) d=f d := by
  apply PowerSeries.ext
  intro n
  simp only [distanceSlice,PowerSeries.coeff_mk,fromFamily_coeff]

theorem locallyFinite_distanceSlice (F : PowerSeries (Polynomial ℤ)) :
    LocallyFiniteFamily (distanceSlice F) := by
  intro n
  apply (PowerSeries.coeff n F).support.finite_toSet.subset
  intro d hd
  exact Polynomial.mem_support_iff.mpr (by simpa only [Set.mem_setOf_eq,distanceSlice,PowerSeries.coeff_mk] using hd)

theorem fromFamily_distanceSlice (F : PowerSeries (Polynomial ℤ)) :
    fromFamily (distanceSlice F) (locallyFinite_distanceSlice F)=F := by
  apply PowerSeries.ext
  intro n
  apply Polynomial.ext
  intro d
  rw [fromFamily_coeff]
  simp only [distanceSlice,PowerSeries.coeff_mk]

theorem fromFamily_specialize (f : ℕ → PowerSeries ℤ) (hf : LocallyFiniteFamily f)
    (t : PowerSeries ℤ) : specialize (fromFamily f hf) t=∑' d,f d*t^d := by
  rw [specialize_distanceSum]
  simp only [distanceSlice_fromFamily]

theorem locallyFinite_weighted_summable (f : ℕ → PowerSeries ℤ)
    (hf : LocallyFiniteFamily f) (K : ℕ → PowerSeries ℤ) :
    Summable (fun d => f d*K d) := by
  simpa only [distanceSlice_fromFamily] using distanceWeighted_summable (fromFamily f hf) K

/-- Original general failure-operator display, in its literal distance-indexed
form. All three formal sums are coefficientwise summable by local finiteness. -/
theorem original_failure_operator (f : ℕ → PowerSeries ℤ) (hf : LocallyFiniteFamily f) :
    X*(∑' d,f d*failureTailSeries d) =
      X*((((∑' d,f d)-(∑' d,f d*c^d))*PowerSeries.invOfUnit (1-c) 1)+
        failureBlockSeries*(∑' d,f d*c^d)) := by
  have h := failureOperator_rational (fromFamily f hf)
  rw [failureOperator_distanceSum] at h
  simp only [distanceSlice_fromFamily,fromFamily_specialize,one_pow,mul_one] at h
  exact h

#print axioms fromFamily_coeff
#print axioms locallyFinite_weighted_summable
#print axioms original_failure_operator
end
end SubmittedGenus.FiniteArithmetic.Reservoir.Bivariate

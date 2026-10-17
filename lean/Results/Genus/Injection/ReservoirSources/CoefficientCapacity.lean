import Results.Genus.Injection.ReservoirSources.DecoratedOccurrences
import Results.Genus.Injection.ReservoirSources.Assembly
import Results.Genus.FiniteArithmetic.Reservoir.CandidateSeries

noncomputable section
namespace SubmittedGenus.OriginalReservoir
open FiniteArithmetic.Reservoir OriginalMaps OriginalSources PowerSeries
attribute [local instance] Classical.propDecidable

/-- The exact original nonbinary capacity expression, with each family
clipped independently and every coefficient tied to its actual sources. -/
def coefficientNonbinaryLowerBound (g : ℕ) : ℤ :=
  max 0 (coeff g (safeCandidateSeries-actualFailureSeries safeFamily)) +
    max 0 (coeff g (earlyCandidateSeries-actualFailureSeries earlyFamily))

lemma nonbinaryLowerBound_eq_coefficient_clip (g : ℕ) :
    (nonbinaryLowerBound g : ℤ)=coefficientNonbinaryLowerBound g := by
  unfold nonbinaryLowerBound coefficientNonbinaryLowerBound
  rw [Nat.cast_add,familyLowerBound_eq_clip,familyLowerBound_eq_clip]
  simp only [map_sub,safeCandidateSeries_coeff,earlyCandidateSeries_coeff,actualFailureSeries_coeff]

lemma coefficientNonbinaryLowerBound_nonnegative (g : ℕ) :
    0≤coefficientNonbinaryLowerBound g := by
  rw [←nonbinaryLowerBound_eq_coefficient_clip]
  positivity

/-- The exact paper coefficient expression supplies actual unused low
semigroups, with no unproved prefix, tail, mark or disjointness premise. -/
lemma coefficient_capacity_bound (g : ℕ) (hg : 1≤g) :
    ∃ fresh : DISources g ↪ BinaryEndTwo g,
      ∃ hreserved : ∀ di b,fresh di≠BReserved g b,
        ((max ((12*Nat.fib g+24)/25) (Nat.fib g-originalDemand g) : ℕ) : ℤ) +
          coefficientNonbinaryLowerBound g ≤
            (Fintype.card (UnusedLow g fresh hreserved) : ℤ) := by
  obtain ⟨fresh,hreserved,h⟩ := original_low_supply g hg
  refine ⟨fresh,hreserved,?_⟩
  rw [←nonbinaryLowerBound_eq_coefficient_clip]
  simpa only [Nat.cast_add] using (Int.ofNat_le.mpr h)

/-- The submitted fundamental inequality with its exact original source-
correct clipped coefficient bound. This does not assert numerical coverage
of the exceptional population. -/
lemma coefficient_fundamental_bound (g : ℕ) (hg : 1≤g) :
    (NumericalSemigroup.count (g+1) : ℤ)-NumericalSemigroup.count g ≥
      ((max ((12*Nat.fib g+24)/25) (Nat.fib g-originalDemand g) : ℕ) : ℤ) +
        coefficientNonbinaryLowerBound g - Fintype.card (SourceClass g .E) := by
  have h := original_fundamental_reservoir g hg
  rw [←nonbinaryLowerBound_eq_coefficient_clip]
  omega

#print axioms nonbinaryLowerBound_eq_coefficient_clip
#print axioms coefficient_capacity_bound
#print axioms coefficient_fundamental_bound
end SubmittedGenus.OriginalReservoir

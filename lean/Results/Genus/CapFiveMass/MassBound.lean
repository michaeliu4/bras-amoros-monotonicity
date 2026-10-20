import Results.Genus.CapFiveMass.ComponentFactorization
import Results.Genus.CapFiveMass.MissingCount
import Results.Genus.CapFiveMass.StrongIncidenceBound
import Results.Genus.CapFiveMass.PopulationEquivalence

/-!
# The submitted genuine multiple-five mass theorem

Original submitted manuscript e04fb276e8ceed829059cf724ead1e18e8bc9e9f,
Lemma mass:five, lines 1608--1684. All source inclusion, strict component
existence, coordinate coverage, endpoint and edge contractions, reflection
counts, geometric summability, and rational comparisons are proved in the
import closure. The conclusion counts genuine positive Kunz words (equivalently
actual numerical semigroups), not the enlarged raw source population.
-/

noncomputable section
open scoped BigOperators
namespace SubmittedGenus.CapFiveMass
open ActualComponent

/-- Source-specific bound for every actual ordered multiplicity/pivot triple. -/
theorem rawPartition_le_geometric (q : PivotParameters) :
    rawPartition q radius ≤ geometricTerm (parameterEquiv q) :=
  rawPartition_le_of_incidence_bounds q
    (MissingGeometry.free_endpoint_count_le_two q.valid)
    (ordered_strong_incidence_lower q.valid)

/-- The actual genuine multiple-five generating series converges at the
submitted radius, and its value is strictly less than 113. -/
theorem genuine_mass_summable_and_lt_113 :
    Summable (fun g => (count g : ℝ) * radius ^ g) ∧ mass radius < 113 :=
  mass_lt_113_of_partition_bounds rawPartition_le_geometric

/-- Literal-radius statement of the submitted paper's B(633/1000) < 113. -/
theorem mass_five :
    Summable (fun g : ℕ => (count g : ℝ) * ((633 : ℝ) / 1000) ^ g) ∧
      (∑' g : ℕ, (count g : ℝ) * ((633 : ℝ) / 1000) ^ g) < 113 := by
  simpa only [radius, mass] using genuine_mass_summable_and_lt_113

/-- The same unconditional bound for the actual numerical-semigroup genus
fibers, transported through the proved source equivalence. -/
theorem semigroup_mass_five :
    Summable (fun g : ℕ => (Fintype.card (GenuineFiveSemigroupsAt g) : ℝ) * ((633 : ℝ) / 1000) ^ g) ∧
      (∑' g : ℕ, (Fintype.card (GenuineFiveSemigroupsAt g) : ℝ) * ((633 : ℝ) / 1000) ^ g) < 113 := by
  simpa only [count_eq_semigroup_card] using mass_five

end SubmittedGenus.CapFiveMass

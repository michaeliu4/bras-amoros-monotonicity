import Results.Genus.CapFiveMass.General.Factorization

/-! The original general mass theorem for genuine multiple-five Kunz words,
with source geometry discharged and no layout or recurrence premises. -/
noncomputable section
open scoped BigOperators
namespace SubmittedGenus.CapFiveMass.General

lemma rawPartition_le_geometric (H : Control) (q : PivotParameters) :
    rawPartition q H.z ≤ geometricTerm H (parameterEquiv q) :=
  rawPartition_le_of_incidence_bounds H q
    (MissingGeometry.free_endpoint_count_le_two q.valid)
    (ActualComponent.ordered_strong_incidence_lower q.valid)

/-- Convergence and the exact submitted general bound follow from the
stated analytic matrix hypotheses, for the actual genuine source. -/
theorem genuine_mass_bound (H : Control) :
    Summable (fun g => (count g : ℝ) * H.z ^ g) ∧ mass H.z ≤ rootMajorant H := by
  have hsgeo : Summable (fun q : PivotParameters => geometricTerm H (parameterEquiv q)) :=
    parameterEquiv.summable_iff.mpr (geometric_summable H)
  have hsraw : Summable (fun q : PivotParameters => rawPartition q H.z) :=
    hsgeo.of_nonneg_of_le (rawPartition_nonneg H.z_pos.le) (rawPartition_le_geometric H)
  have hg := genuine_mass_le_raw H.z_pos.le hsraw
  refine ⟨hg.1, hg.2.trans ?_⟩
  have hle := hsraw.tsum_le_tsum (rawPartition_le_geometric H) hsgeo
  rw [parameterEquiv.tsum_eq, geometric_tsum H] at hle
  exact hle

/-- Identical conclusion for actual numerical-semigroup genus fibers. -/
theorem semigroup_mass_bound (H : Control) :
    Summable (fun g : ℕ => (Fintype.card (GenuineFiveSemigroupsAt g) : ℝ) * H.z ^ g) ∧
      (∑' g : ℕ, (Fintype.card (GenuineFiveSemigroupsAt g) : ℝ) * H.z ^ g) ≤ rootMajorant H := by
  simpa only [count_eq_semigroup_card, mass] using genuine_mass_bound H

end SubmittedGenus.CapFiveMass.General
